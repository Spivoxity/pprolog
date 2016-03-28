/* emit.c */

#include "ptc.h"
#include <stdio.h>
#include <stdarg.h>
#include <string.h>

#define MAX 70
#define STEP 5

static char buf[128];
static bool at_start = TRUE, no_break = FALSE;
static int margin = 0, outptr = 0, brkpt = 0, max = MAX;

PRIVATE void gen_ch(char ch)
{
     int i;

     if (ch == '\n') {
	  buf[outptr] = '\0';
	  puts(buf);
	  outptr = brkpt = 0;
	  at_start = TRUE;
	  return;
     }

     if (outptr >= max && brkpt > 0 & brkpt+1 < outptr) {
	  buf[brkpt] = '\0';
	  puts(buf);
	  for (i = 0; i < margin+2*STEP; i++) putchar(' ');
	  max = MAX-margin-2*STEP;
	  outptr -= brkpt+1;
	  strncpy(buf, &buf[brkpt+1], outptr);
	  brkpt = 0;
     }

     if (at_start) {
	  for (i = 0; i < margin; i++) putchar(' ');
	  max = MAX - margin;
	  at_start = FALSE;
     }

     if (ch == ' ' && ! no_break) brkpt = outptr;

     buf[outptr++] = ch;
}

PUBLIC void emit(char *fmt, ...)
{
     char ch;
     char *s, *p;
     va_list va;
     ident id;
     static char tmpbuf[16];

     va_start(va, fmt);
     s = fmt;
     while ((ch = *s++) != '\0') {
	  if (ch != '%') {
	       gen_ch(ch);
	       continue;
	  }
	  switch (ch = *s++) {
	  case 'i':
	       margin += STEP;
	       break;

	  case 'o':
	       margin -= STEP;
	       break;

	  case 'd':
	       sprintf(tmpbuf, "%d", va_arg(va, int));
	       for (p = tmpbuf; *p != '\0'; p++) gen_ch(*p);
	       break;

	  case 'e':
	       gen_expr(va_arg(va, tree));
	       break;

	  case 's':
	  case 't':
	       p = va_arg(va, char *);
	       if (ch == 't') no_break = TRUE;
	       while (*p != '\0') gen_ch(*p++);
	       no_break = FALSE;
	       break;

	  case 'x':
	       id = va_arg(va, ident);
	       for (p = id->i_text; *p != '\0'; p++) gen_ch(*p);
	       break;

	  default:
	       gen_ch(ch);
	  }
     }
     va_end(va);
}
