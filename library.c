/* library.c */

#include "ptc.h"
#include "parse.h"
#include <string.h>

#define L_NONE 0
#define L_CHR 1
#define L_HALT 2
#define L_EOF 3
#define L_EOLN 4
#define L_WRITE 5
#define L_WRITELN 6
#define L_READ 7
#define L_READLN 8
#define L_ORD 9
#define L_ARGC 10
#define L_ARGV 11
#define L_OPENIN 12
#define L_CLOSEIN 13
#define L_FLUSH 14

PUBLIC tree lib_call(def d, tree args)
{
     int n_args = list_len(args);
     tree call = NULL;
     bool ok = TRUE;
     type t = d->t_type;

     switch (d->d_libid) {
     case L_CHR:
	  ok = (n_args == 1
		&& same_type(car(args)->t_type, int_type));
	  break;

     case L_ORD:
	  ok = (n_args == 1
		&& (same_type(car(args)->t_type, char_type)
		    || same_type(car(args)->t_type, bool_type)));
	  break;

     case L_HALT:
     case L_FLUSH:
	  ok = (n_args == 0);
	  break;

     case L_EOF:
     case L_EOLN:
	  if (n_args == 0)
	       args = list1((tree) _input_);
	  else
	       ok = (n_args = 1
		     && same_type(car(args)->t_type, text_type));
	  break;

     case L_READ:
     case L_READLN:
     case L_WRITE:
     case L_WRITELN:
	  {
	       tree p = args;

	       if (p != nil && same_type(car(p)->t_type, text_type))
		    p = cdr(p);
	       for (; p != nil; p = cdr(p)) {
		    type at = car(p)->t_type;
		    if (! (same_type(at, int_type)
			   || same_type(at, char_type)
			   || same_type(at, string_type))) {
			 ok = FALSE;
			 break;
		    }
	       }
	       return node_t(LIBCALL, (tree) d, args, void_type);
	  }

     case L_ARGC:
	  ok = (n_args == 0);
	  break;

     case L_ARGV:
	  ok = (n_args == 2
		&& same_type(car(args)->t_type, int_type)
		&& is_string_type(cadr(args)->t_type));
	  break;

     case L_OPENIN:
	  ok = (n_args == 2
		&& same_type(car(args)->t_type, text_type)
		&& is_string_type(cadr(args)->t_type));
	  break;

     case L_CLOSEIN:
	  ok = (n_args == 1 && same_type(car(args)->t_type, text_type));
	  break;

     default:
	  ok = FALSE;
	  t = err_type;
     }

     if (! ok) {
	  error("I choked on a library call");
	  return (tree) dummy_def;
     }

     if (call == NULL)
	  return node_t(CALL, (tree) d, args, t);

     return call;
}

PRIVATE void built_in(char *name, type res, int libid)
{
     def d = declare(PROC, enter(name, BUILTIN), res);
     d->d_libid = libid;
}

PUBLIC void gen_libcall(def d, tree args)
{
     int nargs = list_len(args);

     switch (d->d_libid) {
     case L_READ:
     case L_READLN:
	  {
	       tree file = (tree) _input_;
	       tree p = args;
	       bool first = TRUE;

	       if (nargs > 0 && same_type(car(p)->t_type, text_type)) {
		    file = car(p);
		    p = cdr(p);
	       }
	       for (; p != nil; p = cdr(p)) {
		    if (! first) emit(", ");
		    first = FALSE;
		    if (same_type(car(p)->t_type, char_type))
			 emit("%e = getc(%e)", car(p), file);
		    else
			 error("I can only read characters");
	       }
	       if (d->d_libid == L_READLN) {
		    if (! first) emit(", ");
		    emit("skipln(%e)", file);
	       }
	  }
	  break;

     case L_WRITE:
     case L_WRITELN:
	  {
	       tree file = (tree) _output_;
	       tree p = args;
	       static char fmt[256];
	       static tree arg[16];
	       int n = 0, i;

	       if (nargs > 0 && same_type(car(p)->t_type, text_type)) {
		    file = car(p);
		    p = cdr(p);
	       }

	       /* Special case for efficiency: printing a single character */
	       if (d->d_libid == L_WRITE && cdr(p) == nil 
		   && same_type(car(p)->t_type, char_type)) {
		    emit("putc(%e, %e)", car(p), file);
		    break;
	       }

	       /* Another special case: printing just a newline */
	       if (d->d_libid == L_WRITELN && p == nil) {
		    emit("putc('\\n', %e)", file);
		    break;
	       }

	       fmt[0] = '\0';
	       for (; p != nil; p = cdr(p)) {
		    if (same_type(car(p)->t_type, int_type)) {
			 strcat(fmt, "%d");
			 arg[n++] = car(p);
		    }
		    else if (same_type(car(p)->t_type, char_type)) {
			 strcat(fmt, "%c");
			 arg[n++] = car(p);
		    }
		    else if (same_type(car(p)->t_type, string_type))
			 strcat(fmt, encode(((literal) car(p))->l_value));
	       }
	       if (d->d_libid == L_WRITELN)
		    strcat(fmt, "\\n");
	       emit("fprintf(%e, \"%t\"", file, fmt);
	       for (i = 0; i < n; i++) emit(", %e", arg[i]);
	       emit(")");
	  }
	  break;
	  
     default:
	  emit("<libcall-%d>", d->d_libid);
     }
}

PUBLIC void init_lib(void)
{
     built_in("chr", char_type, L_CHR);
     built_in("ord", int_type, L_ORD);
     built_in("halt", void_type, L_HALT);
     built_in("eof", bool_type, L_EOF);
     built_in("eoln", bool_type, L_EOLN);
     built_in("write", void_type, L_WRITE);
     built_in("writeln", void_type, L_WRITELN);
     built_in("read", void_type, L_READ);
     built_in("readln", void_type, L_READLN);
     built_in("flush", void_type, L_FLUSH);
     built_in("argc", int_type, L_ARGC);
     built_in("argv", void_type, L_ARGV);
     built_in("openin", bool_type, L_OPENIN);
     built_in("closein", void_type, L_CLOSEIN);
}
