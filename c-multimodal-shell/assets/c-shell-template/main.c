#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAX_SLOTS 40
#define MAX_BUTTONS 40
#define FIELD 256
#define TEXT 512

typedef struct {
    int id;
    char modality[FIELD];
    char path[FIELD];
    char note[TEXT];
} TrainingSlot;

typedef struct {
    char placeholder[16];
    char label[FIELD];
    int x;
    int y;
    int width;
    int height;
} ButtonRef;

typedef struct {
    unsigned long tick_id;
    char screenshot_path[FIELD];
    int mouse_x;
    int mouse_y;
    int button_count;
    ButtonRef buttons[MAX_BUTTONS];
    int model_is_responding;
} ConsoleFrame;

static int read_file(const char *path, char **out, long *size) {
    FILE *file = fopen(path, "rb");
    long length;
    char *buffer;
    if (!file) return 0;
    if (fseek(file, 0, SEEK_END) != 0) { fclose(file); return 0; }
    length = ftell(file);
    if (length < 0) { fclose(file); return 0; }
    rewind(file);
    buffer = (char *)calloc((size_t)length + 1U, 1U);
    if (!buffer) { fclose(file); return 0; }
    if (fread(buffer, 1U, (size_t)length, file) != (size_t)length) {
        free(buffer);
        fclose(file);
        return 0;
    }
    fclose(file);
    *out = buffer;
    *size = length;
    return 1;
}

static int copy_attr(const char *tag, const char *name, char *out, size_t out_size) {
    char pattern[64];
    const char *start;
    const char *end;
    snprintf(pattern, sizeof(pattern), "%s=\"", name);
    start = strstr(tag, pattern);
    if (!start) return 0;
    start += strlen(pattern);
    end = strchr(start, '"');
    if (!end) return 0;
    if ((size_t)(end - start) >= out_size) return 0;
    memcpy(out, start, (size_t)(end - start));
    out[end - start] = '\0';
    return 1;
}


static void copy_text_between(const char *start, const char *end, char *out, size_t out_size) {
    size_t len;
    if (!start || !end || end < start || out_size == 0U) return;
    len = (size_t)(end - start);
    if (len >= out_size) len = out_size - 1U;
    memcpy(out, start, len);
    out[len] = '\0';
}

static int lookup_dictionary_word(const char *dictionary_path, const char *word) {
    char *xml = NULL;
    long size = 0;
    const char *cursor;
    int found = 0;
    if (!word || word[0] == '\0') return 0;
    if (!read_file(dictionary_path, &xml, &size)) return -1;
    (void)size;
    cursor = xml;
    while ((cursor = strstr(cursor, "<entry")) != NULL) {
        const char *tag_end = strchr(cursor, '>');
        const char *entry_close = strstr(cursor, "</entry>");
        char tag[TEXT];
        char entry_word[FIELD];
        size_t tag_len;
        if (!tag_end || !entry_close || entry_close < tag_end) break;
        tag_len = (size_t)(tag_end - cursor + 1);
        if (tag_len >= sizeof(tag)) tag_len = sizeof(tag) - 1U;
        memcpy(tag, cursor, tag_len);
        tag[tag_len] = '\0';
        entry_word[0] = '\0';
        copy_attr(tag, "word", entry_word, sizeof(entry_word));
        if (strcmp(entry_word, word) == 0) {
            const char *def = tag_end;
            int definition_count = 0;
            printf("dictionary_lookup word=\"%s\"\n", word);
            while ((def = strstr(def, "<definition")) != NULL && def < entry_close) {
                const char *def_start = strchr(def, '>');
                const char *def_end = strstr(def, "</definition>");
                char definition[TEXT];
                if (!def_start || !def_end || def_end > entry_close) break;
                copy_text_between(def_start + 1, def_end, definition, sizeof(definition));
                printf("  definition_%d=%s\n", ++definition_count, definition);
                def = def_end + 13;
            }
            found = definition_count;
            break;
        }
        cursor = entry_close + 8;
    }
    free(xml);
    return found;
}

static int parse_training_xml(const char *path, TrainingSlot slots[MAX_SLOTS]) {
    char *xml = NULL;
    long size = 0;
    const char *cursor;
    int count = 0;
    if (!read_file(path, &xml, &size)) return -1;
    (void)size;
    cursor = xml;
    while ((cursor = strstr(cursor, "<slot")) != NULL && count < MAX_SLOTS) {
        const char *tag_end = strchr(cursor, '>');
        const char *close = strstr(cursor, "</slot>");
        char tag[TEXT];
        char id_text[32];
        size_t tag_len;
        size_t note_len;
        if (!tag_end || !close || close < tag_end) break;
        tag_len = (size_t)(tag_end - cursor + 1);
        if (tag_len >= sizeof(tag)) tag_len = sizeof(tag) - 1U;
        memcpy(tag, cursor, tag_len);
        tag[tag_len] = '\0';
        memset(&slots[count], 0, sizeof(slots[count]));
        if (!copy_attr(tag, "id", id_text, sizeof(id_text))) break;
        slots[count].id = atoi(id_text);
        if (!copy_attr(tag, "modality", slots[count].modality, sizeof(slots[count].modality))) break;
        if (!copy_attr(tag, "path", slots[count].path, sizeof(slots[count].path))) break;
        note_len = (size_t)(close - tag_end - 1);
        if (note_len >= sizeof(slots[count].note)) note_len = sizeof(slots[count].note) - 1U;
        memcpy(slots[count].note, tag_end + 1, note_len);
        slots[count].note[note_len] = '\0';
        count++;
        cursor = close + 7;
    }
    free(xml);
    return count;
}

static void capture_screen_frame(ConsoleFrame *frame) {
    snprintf(frame->screenshot_path, sizeof(frame->screenshot_path), "screen_tick_%lu_grid.ppm", frame->tick_id);
    frame->mouse_x = 640;
    frame->mouse_y = 360;
}

static void detect_buttons(ConsoleFrame *frame) {
    int i;
    frame->button_count = 3;
    for (i = 0; i < frame->button_count; i++) {
        snprintf(frame->buttons[i].placeholder, sizeof(frame->buttons[i].placeholder), "BTN_%02d", i + 1);
        snprintf(frame->buttons[i].label, sizeof(frame->buttons[i].label), "Detected button %d", i + 1);
        frame->buttons[i].x = 100 + (i * 180);
        frame->buttons[i].y = 200;
        frame->buttons[i].width = 140;
        frame->buttons[i].height = 48;
    }
}

static void assemble_prompt_packet(const ConsoleFrame *frame, const char *user_prompt, char *out, size_t out_size) {
    int written;
    int i;
    written = snprintf(out, out_size,
                       "<message to=\"Shakti\" route=\"mcp\">\n"
                       "  <user_request>%s</user_request>\n"
                       "  <mouse placeholder=\"MOUSE_CURRENT\" x=\"%d\" y=\"%d\" />\n"
                       "  <screenshot grid=\"model_picture_only\" path=\"%s\" />\n"
                       "  <buttons>\n",
                       user_prompt, frame->mouse_x, frame->mouse_y, frame->screenshot_path);
    if (written < 0) return;
    for (i = 0; i < frame->button_count && (size_t)written < out_size; i++) {
        int more = snprintf(out + written, out_size - (size_t)written,
                            "    <button placeholder=\"%s\" label=\"%s\" x=\"%d\" y=\"%d\" w=\"%d\" h=\"%d\" />\n",
                            frame->buttons[i].placeholder,
                            frame->buttons[i].label,
                            frame->buttons[i].x,
                            frame->buttons[i].y,
                            frame->buttons[i].width,
                            frame->buttons[i].height);
        if (more < 0) return;
        written += more;
    }
    if ((size_t)written < out_size) {
        snprintf(out + written, out_size - (size_t)written,
                 "  </buttons>\n"
                 "  <instructions>answer in English or emit one action line: CLICK BTN_XX, TYPE &quot;...&quot;, TI83_EXPR, SEARCH_HISTORY, or WAIT</instructions>\n"
                 "</message>\n");
    }
}

static void gguf_generate_stream_dry_run(const char *prompt_packet) {
    printf("model_prompt_packet_begin\n%smodel_prompt_packet_end\n", prompt_packet);
    printf("model_response_stream: WAIT - dry-run adapter is connected; attach Shakti local runtime here.\n");
}

static void stream_model_tick(const ConsoleFrame *frame) {
    int i;
    printf("tick=%lu screenshot=%s mouse=MOUSE_CURRENT(%d,%d)\n",
           frame->tick_id, frame->screenshot_path, frame->mouse_x, frame->mouse_y);
    for (i = 0; i < frame->button_count; i++) {
        printf("  %s label=\"%s\" coords=(%d,%d,%d,%d)\n",
               frame->buttons[i].placeholder,
               frame->buttons[i].label,
               frame->buttons[i].x,
               frame->buttons[i].y,
               frame->buttons[i].width,
               frame->buttons[i].height);
    }
    if (frame->model_is_responding) {
        printf("  overlay=frame update queued while response stream continues\n");
    }
}

static void operate_mouse_keyboard(const char *placeholder, const char *action, int dry_run) {
    printf("%s action=%s target=%s\n", dry_run ? "dry_run" : "execute", action, placeholder);
}

static void wait_one_second(void) {
    time_t start = time(NULL);
    while (time(NULL) == start) { }
}

static const char *arg_value(int argc, char **argv, const char *name, const char *fallback) {
    int i;
    for (i = 1; i + 1 < argc; i++) {
        if (strcmp(argv[i], name) == 0) return argv[i + 1];
    }
    return fallback;
}

int main(int argc, char **argv) {
    const char *xml_path = arg_value(argc, argv, "--xml", "training_slots.xml");
    const char *md_path = arg_value(argc, argv, "--md", "level_41.md");
    const char *dictionary_path = arg_value(argc, argv, "--dict", "dictionary.xml");
    const char *lookup_word = arg_value(argc, argv, "--lookup", "");
    int ticks = atoi(arg_value(argc, argv, "--ticks", "1"));
    const char *user_prompt = arg_value(argc, argv, "--prompt", "describe the current screen");
    TrainingSlot slots[MAX_SLOTS];
    char *markdown = NULL;
    long markdown_size = 0;
    int slot_count = parse_training_xml(xml_path, slots);
    int i;

    if (ticks < 1) ticks = 1;
    if (slot_count != MAX_SLOTS) {
        fprintf(stderr, "expected 40 XML slots, loaded %d from %s\n", slot_count, xml_path);
        return 1;
    }
    if (!read_file(md_path, &markdown, &markdown_size)) {
        fprintf(stderr, "could not load level 41 Markdown slot: %s\n", md_path);
        return 1;
    }

    printf("loaded %d stateless XML slots and level 41 Markdown bytes=%ld\n", slot_count, markdown_size);
    if (lookup_word[0] != '\0') {
        int definitions = lookup_dictionary_word(dictionary_path, lookup_word);
        if (definitions <= 0) printf("dictionary_lookup word=\"%s\" definitions=0\n", lookup_word);
    }
    for (i = 0; i < ticks; i++) {
        ConsoleFrame frame;
        memset(&frame, 0, sizeof(frame));
        frame.tick_id = (unsigned long)(i + 1);
        frame.model_is_responding = (i % 2);
        capture_screen_frame(&frame);
        detect_buttons(&frame);
        char prompt_packet[2048];
        stream_model_tick(&frame);
        assemble_prompt_packet(&frame, user_prompt, prompt_packet, sizeof(prompt_packet));
        gguf_generate_stream_dry_run(prompt_packet);
        operate_mouse_keyboard("BTN_01", "hover", 1);
        if (i + 1 < ticks) wait_one_second();
    }

    free(markdown);
    return 0;
}
