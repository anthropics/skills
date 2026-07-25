/*
 * sample_c_smells.c — labelled instances of every C-specific pattern
 * the code-reviewer skill flags. Every smell is annotated inline with
 * its CWE and the rule from languages/c.md.
 *
 * Refactored counterpart: sample_c_clean.c
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>


void unsafe_input(void) {
    char buf[64];

    /* RULE: banned function gets() — CWE-242, no bounds check */
    gets(buf);

    char dest[10];
    /* RULE: banned function strcpy() — no bounds check */
    strcpy(dest, buf);

    /* RULE: banned function strcat() — no bounds check */
    strcat(dest, "world");

    char msg[100];
    /* RULE: banned function sprintf() — no bounds check */
    sprintf(msg, "%s says hello", buf);

    /* RULE: format-string vulnerability — CWE-134, buf controls format */
    printf(buf);

    char name[32];
    /* RULE: unbounded scanf — %s without width, CWE-120 */
    scanf("%s", name);
}


void leaky_alloc(int n) {
    /* RULE: malloc result not NULL-checked within 5 lines — CWE-690 */
    char *buf = malloc(n);
    buf[0] = 'x';
    buf[1] = 'y';
    strcpy(buf, "leak");

    /* RULE: free without zeroing pointer — CWE-416 dangling */
    free(buf);
    printf("done\n");
}


void run_user_cmd(const char *cmd_from_user) {
    /* RULE: system() with non-literal argument — CWE-78 command injection */
    system(cmd_from_user);
}


int main(int argc, char *argv[]) {
    if (argc > 1) {
        unsafe_input();
        leaky_alloc(100);
        run_user_cmd(argv[1]);
    }
    return 0;
}
