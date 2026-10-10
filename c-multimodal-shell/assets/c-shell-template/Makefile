CC ?= cc
CFLAGS ?= -std=c99 -Wall -Wextra -pedantic -O2

all: c_multimodal_shell

c_multimodal_shell: main.c
	$(CC) $(CFLAGS) -o $@ main.c

clean:
	rm -f c_multimodal_shell
