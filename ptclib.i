/* ptclib.i */

#include <stdio.h>
#include <stdlib.h>

char *strcpy();
void p_main();

typedef int integer;

typedef char boolean;
#define TRUE 1
#define FALSE 0

typedef FILE *text;
text input, output;

#define chr(x) ((char) (x))
#define ord(x) ((integer) (x))
#define halt() exit(1);

#ifdef __TURBOC__
#include "alloc.h"

void allocate(integer huge **mem, long size)
{
     integer huge *m = (integer huge *) farmalloc(size * sizeof(integer));

     if (m == NULL) {
	  fprintf(stderr, "Sorry, not enough memory\n");
	  exit(2);
     }
     *mem = m;
}
#endif

void flush()
{
	fflush(stdout);
}

boolean eof(f)
text f;
{
     int c = getc(f);
     if (c != EOF) ungetc(c, f);
     return (c == EOF);
}

boolean eoln(f)
text f;
{
     int c = getc(f);
     if (c != EOF) ungetc(c, f);
     return (c == '\n');
}

void skipln(f)
text f;
{
     int c;
     do c = getc(f); while (c != '\n' && c != EOF);
}

#define openin(f, name) _openin(&f, name)

int _openin(f, name)
text *f;
char *name;
{
     if (*f != NULL && *f != stdin) fclose(*f);

     if ((*f = fopen(name, "r")) == NULL) return FALSE;
     return TRUE;
}


void closein(f)
text f;
{
     fclose(f);
}

int save_argc;
char **save_argv;

int argc()
{
     return save_argc;
}

void argv(i, buf)
integer i;
char *buf;
{
     strcpy(buf, save_argv[i]);
}

static char obuf[BUFSIZ];

int main(ac, av)
int ac;
char **av;
{
     save_argc = ac;
     save_argv = av;
     setbuf(stdout, obuf);
     input = stdin; output = stdout;
     p_main();
     return 0;
}

/* A few ad-hoc fix-ups */
#undef getchar
#define getchar _getchar_
#define fgetchar _fgetchar_
#define continue _continue_
