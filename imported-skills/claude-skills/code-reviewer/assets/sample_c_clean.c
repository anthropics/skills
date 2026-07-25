/*
 * sample_c_clean.c — sample_c_smells.c refactored per
 * rules/universal.md + languages/c.md. Same surface area, zero
 * detector hits.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>


void safe_input(void) {
    char buf[64];

    /* fgets is bounds-aware */
    if (fgets(buf, sizeof(buf), stdin) == NULL) {
        return;
    }

    char dest[10];
    /* strncpy with explicit bound + manual null-terminate */
    strncpy(dest, buf, sizeof(dest) - 1);
    dest[sizeof(dest) - 1] = '\0';

    /* strncat with remaining-space bound */
    size_t room = sizeof(dest) - strlen(dest) - 1;
    strncat(dest, "world", room);

    char msg[100];
    /* snprintf is bounds-aware */
    snprintf(msg, sizeof(msg), "%s says hello", buf);

    /* Format string is a literal; buf is an argument */
    printf("%s\n", buf);

    char name[32];
    /* %s with explicit width prevents overflow */
    scanf("%31s", name);
}


void checked_alloc(int n) {
    /* malloc result is NULL-checked before any dereference */
    char *buf = malloc(n);
    if (buf == NULL) {
        return;
    }
    buf[0] = 'x';
    buf[1] = 'y';
    strncpy(buf, "ok", n - 1);

    free(buf);
    buf = NULL;
    printf("done\n");
}


void run_safe_cmd(void) {
    /* system() with a string literal — no command-injection surface */
    system("ls -la");
}


int main(int argc, char *argv[]) {
    (void)argc;
    (void)argv;
    safe_input();
    checked_alloc(100);
    run_safe_cmd();
    return 0;
}
