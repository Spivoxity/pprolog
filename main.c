/* main.c */

#define EXTERN
#include "ptc.h"
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>

extern FILE *yyin;
extern int yydebug;
extern int line;

PRIVATE int err_count = 0;

PUBLIC int main(int argc, char **argv)
{
     init_lex();
     init_symtab();
     init_type();
     init_lib();

     if (argc != 2) 
	  filename = "standard input";
     else {
	  filename = argv[1];
	  if ((yyin = fopen(filename, "r")) == NULL) {
	       perror(filename);
	       exit(1);
	  }
     }

     yyparse();
     return (err_count == 0 ? 0 : 1);
}

PUBLIC void warning(char *msg, ...)
{
     va_list va;

     fprintf(stderr, "\"%s\", line %d: warning -- ", filename, line);
     va_start(va, msg);
     vfprintf(stderr, msg, va);
     va_end(va);
     fprintf(stderr, "\n");
     fflush(stderr);
}

PUBLIC void error(char *msg, ...)
{
     va_list va;

     err_count++;
     fprintf(stderr, "\"%s\", line %d: ", filename, line);
     va_start(va, msg);
     vfprintf(stderr, msg, va);
     va_end(va);
     fprintf(stderr, "\n");
     fflush(stderr);
}

PUBLIC void panic(char *msg, ...)
{
     va_list va;

     fprintf(stderr, "Panic: ");
     va_start(va, msg);
     vfprintf(stderr, msg, va);
     va_end(va);
     exit(2);
}

PUBLIC void bad_tag(char *where, int tag)
{
     panic("bad tag %d in %s", tag, where);
}

