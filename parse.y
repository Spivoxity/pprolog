/* parse.y */

%{
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>

#define EXTERN
#include "ptc.h"

#define YYDEBUG 1

char *filename;
static void error(char *msg, ...);
static void panic(char *msg, ...);
static void yyerror(char *msg);

static def _input_, _output_, dummy_def;
static ident cur_proc;
static type return_type;
static scope top_scope = NULL;

int yylex(void);
void init_lex(void);
ident enter(char *name, int lexval);
literal lit_cat(int kind, char *v1, char *v2, type t);
extern char *equiv[];

#define node(k, l, r)	 node_t(k, l, r, none)
#define nil		 ((tree) NULL)
#define cons(h, t)	 node(CONS, h, t)
#define car(t)		 (t)->t_left
#define cdr(t)		 (t)->t_right
#define cadr(t)		 car(cdr(t))
#define list1(x)	 cons(x, nil)

static tree node_t(int kind, tree left, tree right, type t);

static void assign(tree lhs, tree rhs);
static void write_stmt(int kind, tree args);
static void for_loop(tree var, tree first, tree last, int dir);
static void case_labels(tree labels);
static void gen_heading();
static void gen_decl(int kind, ident name, type rhs_type);
static void gen_decl_list(int kind, tree names, type rhs_type);

static tree var_ref(ident name);
static tree var_as_exp(tree var);
static tree eval(int kind, tree left, tree right);
static tree func_call(int kind, ident func, tree args);
static char *get_const(tree expr);
static char *encode(char *s);

static type check_type(char *cxt, type expected, type found);
static type const_type(ident name);
static type range_type(tree lower, tree upper);
static type array_type(type index, type elem);
static type record_type(void);

static void const_decl(ident name, tree value);
static def declare(int kind, ident name, type rhs_type);
static void decl_list(int kind, tree names, type rhs_type);
static void push_scope(void);
static scope pop_scope(void);
static void begin_proc(ident name); 
static void def_proc(type ret_type);
static void forward_def(void);

static void emit(char *fmt, ...);
%}

%union {
     tree E;
     type T;
     ident I;
     literal L;
}

%token <I>	IDENT MONOP MULOP ADDOP RELOP WRITE
%token <L>	NUMBER STRING CHAR
%token		ASSIGN DOTDOT NEQ GEQ LEQ 

/* keywords */
%token		AND ARRAY BEG CASE CONST DIV DO DOWNTO IF ELSE END 
%token		FOR FORWARD FUNC GOTO LABEL MOD NOT OF OR
%token		PROC PROGRAM RECORD REPEAT SHL SHR
%token		THEN TO TYPE UNTIL VAR WHILE

/* extra tokens for tree tags etc. */
%token		CALL CONS SUB DOT FIELD RANGE PRIMTYPE CPARAM VPARAM 
%token		NEG BITAND BITOR LIBCALL APARAM POINTER ADDRESS BUILTIN

%right		IF THEN ELSE
%left		RELOP '='
%left		ADDOP '-'
%left		MULOP
%nonassoc	MONOP UMINUS

%token		N_TOKENS

%type <E>	expr variable ident.list expr.list write.params write.list
%type <E>	actuals const const.list write.item number.list
%type <T>	type type.ident

%%

program :	prog.heading glo.decls main.prog '.' ;

prog.heading :	PROGRAM IDENT file.args ';'	
		{ emit("/* Program '%s' */\n\n", $2->i_text);
		  emit("#include \"ptclib.i\"\n\n"); } ;

file.args :	/* empty */
	|	'(' ident.list ')' ;

glo.decls :	/* empty */
	|	glo.decls decl
	|	glo.decls glo.decl ;

local.decls :	/* empty */
	|	local.decls decl ;

decl 	:	LABEL number.list ';'
	|	CONST const.decls
	|	VAR var.decls		{ emit("\n"); } ;

glo.decl :	proc.decl
	|	TYPE type.decls ;

const.decls:	const.decl
	|	const.decls const.decl ;

const.decl :	IDENT '=' const ';'	{ const_decl($1, $3); } ;

type.decls :	type.decl
	|	type.decls type.decl ;

type.decl :	IDENT '=' type ';'	
		{ declare(TYPE, $1, $3);
		  if ($3->x_name == NULL) {
			gen_decl(TYPE, $1, $3);
			emit("\n");
			$3->x_name = $1; } } ;

var.decls :	var.decl
	|	var.decls var.decl ;

var.decl :	ident.list ':' type ';'  
		{ decl_list(VAR, $1, $3);
		  gen_decl_list(VAR, $1, $3); } ;

proc.decl :	proc.heading 
		{ gen_heading(); emit(" {\n%i"); push_scope(); }
		local.decls 
		{ if (return_type != void_type) {
		     gen_decl(VAR, enter("__R__", BUILTIN), return_type);
		     emit("\n"); } }
    	        BEG stmt.list END ';'
		{ if (return_type != void_type) 
		     emit("return __R__;\n");
		  emit("%o}\n\n");
		  pop_scope(); pop_scope(); }
	|	proc.heading FORWARD ';'
                { gen_heading(); emit(";\n"); forward_def(); } ;

proc.heading :	PROC IDENT { begin_proc($2); }
		formal.params ';' { def_proc(void_type); }
	|	FUNC IDENT { begin_proc($2); }
		formal.params ':' type.ident ';' { def_proc($6); }
	|	FUNC IDENT ';' { begin_proc($2); def_proc(void_type); } ;

formal.params :	/* empty */
	|	'(' formal.decls ')' ;

formal.decls :	formal.decl
	|	formal.decls ';' formal.decl ;

formal.decl :	ident.list ':' type.ident
		{ decl_list(CPARAM, $1, $3); }
	|	VAR ident.list ':' type.ident
		{ decl_list(VPARAM, $2, $4); } ;

main.prog :	BEG { emit("void p_main()\n{\n%i"); }
		stmt.list END { emit("%o}\n"); } ;

stmt.list :	stmt
	|	stmt.list ';' stmt ;

stmt	:	basic.stmt
	|	BEG { emit("{\n%i"); } stmt.list END { emit("%o}\n"); } ;

sub.stmt :	{ emit("\n%i"); } basic.stmt { emit("%o"); }
	|	BEG { emit(" {\n%i"); } stmt.list END { emit("%o}\n"); } ;

basic.stmt :	/* EMPTY */ { emit("/* skip */;\n"); } 
	|	NUMBER ':' { emit("%oL%s:\n%i", $1->l_value); } stmt
	|	variable ASSIGN expr 	{ assign($1, $3); }
	|	IDENT actuals 		
		{ emit("%e;\n", func_call(PROC, $1, $2)); }
	|	WRITE write.params
		{ emit("%e;\n", func_call(PROC, $1, $2)); }
	|	GOTO NUMBER		
		{ emit("goto L%s;\n", $2->l_value); }
	|	IF { emit("if "); } if.tail
	|	WHILE expr DO
		{ check_type("while statement", bool_type, $2->t_type);
		  emit("while (%e)", $2); }
		sub.stmt
	|	REPEAT { emit("do {\n%i"); }
		stmt.list UNTIL expr
		{ check_type("repeat statement", bool_type, $5->t_type);
		  emit("%o} while (! (%e));\n", $5); }
	|	FOR variable ASSIGN expr TO expr DO
		{ for_loop($2, $4, $6, TO); }
		sub.stmt
	|	FOR variable ASSIGN expr DOWNTO expr DO 
		{ for_loop($2, $4, $6, DOWNTO); }
		sub.stmt
	|	CASE expr OF 
		{ check_type("case statement", scalar_type, $2->t_type);
		  emit("switch (%e) {\n%i", $2); }
		cases opt.semi default.part END
		{ emit("%o}\n"); } ;

if.tail	:	expr THEN
		{ check_type("if statement", bool_type, $1->t_type);
		  emit("(%e)", $1); }
		sub.stmt else.part ;

else.part :	/* empty */ %prec THEN
	|	ELSE marker { emit("else"); } sub.stmt
	|	ELSE IF { emit("else if "); } if.tail ;

marker	:	/* empty */ %prec IF ;

default.part :	/* empty */
	|	ELSE { emit("%odefault:\n%i"); } stmt.list ;

cases	:	case
	|	cases ';' case ;

case	:	const.list ':' { case_labels($1); } 
		stmt { emit("break;\n"); } ;

opt.semi :	';' | /* empty */ ;

ident.list :	IDENT			{ $$ = list1((tree) $1); }
	|	IDENT ',' ident.list 	{ $$ = cons((tree) $1, $3); } ;

number.list :	NUMBER			{ $$ = list1((tree) $1); }
	|	NUMBER ',' number.list  { $$ = cons((tree) $1, $3); } ;

write.params :	/* empty */		{ $$ = nil; }
	|	'(' write.list ')'	{ $$ = $2; } ;

write.list :	write.item		{ $$ = list1($1); }
	|	write.item ',' write.list { $$ = cons($1, $3); } ;

write.item :	expr
	|	expr ':' expr		{ $$ = $1; }
	;

expr 	:	variable		{ $$ = var_as_exp($1); }
	|	NUMBER			{ $$ = (tree) $1; }
	|	STRING			{ $$ = (tree) $1; }
	|	IDENT '(' expr.list ')' { $$ = func_call(FUNC, $1, $3); }
	|	'(' expr ')'		{ $$ = $2; }
	|	MONOP expr		{ $$ = eval($1->i_op, $2, nil); } 
	|	'-' expr %prec UMINUS	{ $$ = eval(UMINUS, $2, nil); }
	|	expr MULOP expr		{ $$ = eval($2->i_op, $1, $3); }
	|	expr ADDOP expr		{ $$ = eval($2->i_op, $1, $3); }
	|	expr '-' expr		{ $$ = eval('-', $1, $3); }
	|	expr RELOP expr		{ $$ = eval($2->i_op, $1, $3); }
	|	expr '=' expr		{ $$ = eval('=', $1, $3); } ;

actuals	:	/* empty */		{ $$ = nil; }
	|	'(' expr.list ')'	{ $$ = $2; } ;

expr.list :	expr			{ $$ = list1($1); }
	|	expr ',' expr.list 	{ $$ = cons($1, $3); }
	;

variable :	IDENT			{ $$ = var_ref($1); }
	|	variable '[' expr ']'	{ $$ = eval(SUB, $1, $3); }
	|	variable '.' IDENT	{ $$ = eval(DOT, $1, (tree) $3); } ;

type	:	type.ident
	|	const DOTDOT const	{ $$ = range_type($1, $3); }
	|	ARRAY '[' type ']' OF type  
					{ $$ = array_type($3, $6); }
	|	RECORD { push_scope(); } fields opt.semi END
					{ $$ = record_type(); } ;

type.ident :	IDENT			{ $$ = const_type($1); } ;

fields	:	field.decl
	|	fields ';' field.decl ;

field.decl :	ident.list ':' type	{ decl_list(FIELD, $1, $3); } ;

const	:	NUMBER 			{ $$ = (tree) $1; }
	| 	STRING 			{ $$ = (tree) $1; }
	|	IDENT 			{ $$ = var_ref($1); }
	|	'-' const
		{ check_type("constant", int_type, $2->t_type);
		  $$ = (tree) lit_cat(NUMBER, "-", ((literal) $2)->l_value, 
				      int_type); } ;

const.list :	const			{ $$ = list1($1); }
	|	const ',' const.list	{ $$ = cons($1, $3); } 	;

%%

extern FILE *yyin;
extern int yydebug;
extern int line;

static int err_count = 0;

static void error(char *msg, ...) {
     va_list va;

     err_count++;
     fprintf(stderr, "\"%s\", line %d: ", filename, line);
     va_start(va, msg);
     vfprintf(stderr, msg, va);
     va_end(va);
     fprintf(stderr, "\n");
     fflush(stderr);
}

static void yyerror(char *msg) {
     error(msg);
}

static void panic(char *msg, ...) {
     va_list va;

     fprintf(stderr, "Panic: ");
     va_start(va, msg);
     vfprintf(stderr, msg, va);
     va_end(va);
     exit(2);
}

void bad_tag(char *where, int tag) {
     panic("bad tag %d in %s", tag, where);
}

static tree node_t(int kind, tree left, tree right, type t) {
     tree p;

     p = (tree) malloc(sizeof(struct tree));
     p->t_kind = kind;
     p->t_left = left;
     p->t_right = right;
     p->t_type = t;
     return p;
}

static int list_len(tree a) {
     int len = 0;
     for (tree p = a; p != nil; p = cdr(p)) len++;
     return len;
}

static void built_in(char *name, type res, int libid) {
     def d = declare(PROC, enter(name, BUILTIN), res);
     d->d_libid = libid;
}

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

static void init_lib(void) {
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

static void push_scope(void) {
     scope e = (scope) malloc(sizeof(struct scope));
     e->e_defs = NULL;
     e->e_link = &e->e_defs;
     e->e_ndefs = 0;
     e->e_next = top_scope;
     top_scope = e;
}

static scope pop_scope(void) {
     scope e = top_scope;

     if (e == NULL)
	  panic("popping too many scopes");

     top_scope = e->e_next;
     return e;
}

static def search(ident name, scope s) {
     for (def p = s->e_defs; p != NULL; p = p->d_next)
	  if (p->d_name == name) return p;
     return (def) NULL;
}

static def find(ident name) {
     for (scope d = top_scope; d != NULL; d = d->e_next) {
          def p = search(name, d);
	  if (p != NULL) return p;
     }

     if (name->i_glodef != NULL)
          return name->i_glodef;

     error("undeclared identifier %s", name->i_text);
     return dummy_def;
}

static type alloc_type(void) {
     type t = (type) malloc(sizeof(struct type));
     t->x_name = NULL;
     return t;
}

/* same_type -- check types are compatible */
static bool same_type(type t1, type t2) {
     if (t1->x_kind == RANGE) t1 = t1->x_base;
     if (t2->x_kind == RANGE) t2 = t2->x_base;
     return (t1 == t2 || t1 == err_type || t2 == err_type);
}

/* scalar -- test if type is scalar */
static bool scalar(type t) {
     return (t == int_type || t == char_type || t == bool_type 
	     || t == err_type || t->x_kind == RANGE);
}

/* check_type -- check for expected type and return it */
static type check_type(char *cxt, type expected, type found) {
     if (same_type(expected, found))
	  return found;
     else if (expected == scalar_type) {
	  if (scalar(found))
	       return found;
	  error("expected scalar in %s", cxt);
	  return err_type;
     }
     else if (expected->x_kind == ARRAY && expected->x_elem == char_type
	      && found == string_type) {
	  return found;
     }
     else {
	  error("type mismatch in %s", cxt);
	  return err_type;
     }
}

static type const_type(ident name) {
     def d = find(name);

     if (d == NULL)
	  return err_type;
     else if (d->t_kind != TYPE) {
	  error("%s is not a type", name->i_text);
	  return err_type;
     }
     else
	  return d->t_type;
}

static type ptr_type(type base) {
     type p = alloc_type();
     p->x_kind = POINTER;
     p->x_base = base;
     return p;
}

static bool is_string_type(type t) {
     return (t->x_kind == ARRAY && same_type(t->x_elem, char_type)
	     && t->x_index->x_base == int_type 
	     && t->x_index->x_lo == 1);
}

static type range_type(tree lower, tree upper) { 
     type p;

     check_type("range type", int_type, lower->t_type);
     check_type("range type", int_type, upper->t_type);

     p = alloc_type();
     p->x_kind = RANGE;
     p->x_base = int_type;
     p->x_lo = atol(get_const(lower));
     p->x_hi = atol(get_const(upper));
     return p;
}

static type array_type(type index, type elem) { 
     type p;

     if (index->x_kind != RANGE || index->x_base != int_type) {
	  error("sorry, arrays indexed by integer ranges only");
	  return err_type;
     }

     p = alloc_type();
     p->x_kind = ARRAY;
     p->x_index = index;
     p->x_elem = elem;
     return p;
}

static type record_type(void) {
     type p = alloc_type();
     p->x_kind = RECORD;
     p->x_fields = pop_scope();
     return p;
}

static type prim_type(char *name) {
     ident sym = enter(name, BUILTIN);
     type p = alloc_type();

     p->x_kind = PRIMTYPE;
     p->x_name = sym;
     declare(TYPE, sym, p);
     return p;
}     

static tree var_ref(ident name) {
     def d = find(name);
     if (d == NULL)
	  return (tree) dummy_def;
     else
	  return (tree) d;
}

static tree var_as_exp(tree var) {
     if (var->t_kind == PROC || var->t_kind == FORWARD)
	  return func_call(FUNC, ((def) var)->d_name, nil);
     else
	  return var;
}     

static tree eval(int kind, tree left, tree right) {
     type t = left->t_type;
     bool ok;

     switch (kind) {
     case SUB:
	  ok = (left->t_type->x_kind == ARRAY) 
	       && same_type(right->t_type, left->t_type->x_index);
	  t = (ok ? left->t_type->x_elem : err_type);
	  break;

     case DOT:
	  t = err_type;
	  ok = (left->t_type->x_kind == RECORD);
	  if (ok) {
	       def p = search((ident) right, left->t_type->x_fields);
	       if (p != NULL)
		    t = p->t_type;
	       else {
		    error("selecting non-existent field");
		    t = err_type;
	       }
	  }
	  break;

     case UMINUS:
	  ok = same_type(t, int_type);
	  break;

     case NOT:
	  if (same_type(t, int_type))
	       kind = NEG;
	  else
	       ok = same_type(t, bool_type);
	  break;

     case '*':
     case '/':
     case DIV:
     case MOD:
     case '+':
     case '-':
     case SHL:
     case SHR:
	  ok = same_type(t, int_type) && same_type(t, right->t_type);
	  break;

     case AND:
     case OR:
	  if (same_type(t, int_type))
	       kind = (kind == AND ? BITAND : BITOR);
	  else
	       ok = same_type(t, bool_type);
	  if (ok) ok = same_type(t, right->t_type);
	  break;

     case '=':
     case '<':
     case '>':
     case NEQ:
     case LEQ:
     case GEQ:
	  ok = scalar(t) && same_type(t, right->t_type);
	  t = bool_type;
	  break;

     default:
	  error("I can't handle this kind of expr yet");
	  t = err_type;
	  ok = TRUE;
     }

     if (! ok)
	  error("type conflagration in expression");

     return node_t(kind, left, right, t);
}

static bool is_var(tree t) {
     switch (t->t_kind) {
     case VAR:
     case CPARAM:
     case VPARAM:
     case APARAM:
     case SUB:
     case DOT:
	  return TRUE;

     default:
	  return FALSE;
     }
}

static tree lib_call(def d, tree args) {
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

static tree func_call(int kind, ident func, tree args) {
     def d = find(func);
     type t;

     if (d == NULL || d == dummy_def)
	  return (tree) dummy_def;
     else if (d->t_kind != PROC && d->t_kind != FORWARD) {
	  error("%s is not a procedure or function", d->d_name->i_text);
	  return (tree) dummy_def;
     }
     else {
	  t = d->t_type;
	  if (kind == PROC && t != void_type)
	       error("can't call a function as a procedure");
	  if (kind == FUNC && t == void_type) {
	       error("can't call a procedure as a function");
	       t = err_type;
	  }
	  if (d->d_libid != 0)
	       return lib_call(d, args);
	  if (d->d_params->e_ndefs != list_len(args))
	       error("wrong number of arguments");
	  else {
	       def f; tree a;
	       for (f = d->d_params->e_defs, a = args;
			 a != nil; f = f->d_next, a = cdr(a)) {
		    if (! (same_type(f->t_type, car(a)->t_type)
			   || is_string_type(f->t_type) 
			      && car(a)->t_type == string_type))
			 error("argument has wrong type");
		    if (f->t_kind == VPARAM) {
			 if (! is_var(car(a)))
			      error("var parameter not a variable");
			 car(a) = node(ADDRESS, car(a), nil);
		    }
	       }
	  }
	  return node_t(CALL, (tree) d, args, t);
     }
}

static void gen_call(def d, tree args) {
     emit("%x(", d->d_name);
     for (tree p = args; p != nil; p = cdr(p)) {
	  if (p != args) emit(", ");
	  emit("%e", car(p));
     }
     emit(")");
}

static char *encode(char *s) {
     static char buf[256];
     char *t = buf;

     for (; *s != '\0'; s++)
	  if (*s == '\'') {
	       *t++ = '\\'; *t++ = '\'';
	  }
	  else if (*s == '\"') {
	       *t++ = '\\'; *t++ = '\"';
	  }
	  else
	       *t++ = *s;

     *t++ = '\0';
     return buf;
}
	       
static void gen_const(type t, char *v) {
     if (t == int_type)
	  emit("%s", v);
     else if (t == bool_type)
	  emit("%s", v);
     else if (t == char_type)
	  emit("'%t'", encode(v));
     else if (t == string_type)
	  emit("\"%t\"", encode(v));
     else
	  emit("*strange*");
}

static void gen_libcall(def d, tree args) {
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
	       int n = 0;

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
	       for (int i = 0; i < n; i++) emit(", %e", arg[i]);
	       emit(")");
	  }
	  break;
	  
     default:
	  emit("<libcall-%d>", d->d_libid);
     }
}

static void gen_expr(tree expr) {
     int x = expr->t_kind;

     switch (x) {
     case VAR:
     case CPARAM:
     case APARAM:
	  emit("%x", ((def) expr)->d_name);
	  break;

     case VPARAM:
	  emit("*%x", ((def) expr)->d_name);
	  break;

     case NUMBER:
     case STRING:
	  gen_const(expr->t_type, ((literal) expr)->l_value);
	  break;

     case CONST:
	  gen_const(expr->t_type, ((def) expr)->d_value);
	  break;

     case SUB:
	  emit("%e[%e", expr->t_left, expr->t_right);
	  if (expr->t_left->t_type->x_index->x_lo != 0)
	       emit(" - %d", expr->t_left->t_type->x_index->x_lo);
	  emit("]");
	  break;

     case DOT:
	  emit("%e.%x", expr->t_left, (ident) expr->t_right);
	  break;

     case NOT:
     case UMINUS:
     case NEG:
	  emit("(%s %e)", equiv[x], expr->t_left);
	  break;

     case '*':
     case '/':
     case DIV:
     case MOD:
     case '+':
     case '-':
     case SHL:
     case SHR:
     case AND:
     case OR:
     case BITAND:
     case BITOR:
     case '=':
     case '<':
     case '>':
     case NEQ:
     case LEQ:
     case GEQ:
	  emit("(%e %s %e)", expr->t_left, equiv[x], expr->t_right);
	  break;

     case CALL:
	  gen_call((def) expr->t_left, expr->t_right);
	  break;

     case LIBCALL:
	  gen_libcall((def) expr->t_left, expr->t_right);
	  break;

     case ADDRESS:
	  emit("&%e", expr->t_left);
	  break;

     default:
	  emit("<expr-%d>", x);
     }
}

static char *get_const(tree expr) {
     switch (expr->t_kind) {
     case NUMBER:
     case CHAR:
     case STRING:
	  return ((literal) expr)->l_value;

     case CONST:
	  return ((def) expr)->d_value;

     default:
	  error("I expected a constant");
	  return "";
     }
}

static void assign(tree lhs, tree rhs) {
     type lt = lhs->t_type, rt = rhs->t_type;
     if (! same_type(lt, rt))
	  error("types don't match in assignment");
     else if (! scalar(rt))
	  error("I can't copy non-scalar values");

     if (lhs->t_kind == PROC && ((def) lhs)->d_name == cur_proc)
	  emit("__R__");
     else
	  emit("%e", lhs);
     emit(" = %e;\n", rhs);
}

static void for_loop(tree var, tree first, tree last, int dir) {
     emit("for (%e = %e; %e %s %e; %e%s)",
	  var, first,
	  var, (dir == DOWNTO ? ">=" : "<="), last, 
	  var, (dir == DOWNTO ? "--" : "++"));
}

static void case_labels(tree labels) {
     for (tree t = labels; t != nil; t = cdr(t))
	  emit("%ocase %e:\n%i", car(t));
}

static void gen_scope_decls(scope e) {
     for (def d = e->e_defs; d != NULL; d = d->d_next)
	  gen_decl(d->t_kind, d->d_name, d->t_type);
}

static void gen_type_root(type t) {
     if (t->x_name != NULL) {
	  emit("%x", t->x_name);
	  return;
     }

     switch (t->x_kind) {
     case RANGE:
	  gen_type_root(t->x_base);
	  break;

     case ARRAY:
	  gen_type_root(t->x_elem);
	  break;

     case RECORD:
	  emit("struct {\n%i");
	  gen_scope_decls(t->x_fields);
	  emit("%o}");
	  break;

     default:
	  bad_tag("gen_type_root", t->x_kind);
     }
}

static void gen_var_pattern(ident name, type t) {
     if (t->x_name == NULL && t->x_kind == ARRAY) {
	  gen_var_pattern(name, t->x_elem);
	  emit("[%d]", t->x_index->x_hi - t->x_index->x_lo + 1);
     }
     else if (t->x_name == NULL && t->x_kind == POINTER) {
	  emit("(*");
	  gen_var_pattern(name, t->x_base);
	  emit(")");
     }
     else {
	  emit("%x", name);
     }
}

static void gen_decl(int kind, ident name, type rhs_type) {
     if (kind == TYPE) emit("typedef ");
     gen_type_root(rhs_type);
     emit(" ");
     gen_var_pattern(name, rhs_type);
     emit(";\n");
}

static void gen_decl_list(int kind, tree names, type rhs_type) {
     gen_type_root(rhs_type);
     emit(" ");
     for (tree t = names; t != nil; t = cdr(t)) {
	  if (t != names) emit(", ");
	  gen_var_pattern((ident) car(t), rhs_type);
     }
     emit(";\n");
}

static void gen_heading(void) {
     emit("%x %x(", return_type->x_name, cur_proc);
     for (def d = top_scope->e_defs; d != NULL; d = d->d_next) {
	  if (d != top_scope->e_defs) emit(", ");

          gen_type_root(d->t_type);
          emit(" ");
          if (d->t_kind == VPARAM)
               gen_var_pattern(d->d_name, ptr_type(d->t_type));
          else
               gen_var_pattern(d->d_name, d->t_type);
     }
     emit(")");
}

static def def_const(char *name, type val_type, char *value) {
     def d = declare(CONST, enter(name, BUILTIN), val_type);
     d->d_value = value;
     return d;
}

static void init_type(void) {
     void_type = prim_type("void");
     char_type = prim_type("char");
     int_type = prim_type("integer");
     bool_type = prim_type("boolean");
     scalar_type = prim_type("*scalar*");
     string_type = prim_type("*string*");
     text_type = prim_type("text");
     err_type = prim_type("*err_type*");

     def_const("true", bool_type, "TRUE");
     def_const("false", bool_type, "FALSE");
     dummy_def = def_const("*dummy*", err_type, "");

     _input_ = declare(VAR, enter("input", BUILTIN), text_type);
     _output_ = declare(VAR, enter("output", BUILTIN), text_type);
}

static def make_def(int kind, ident name, type rhs_type) {
     def d = (def) malloc(sizeof(struct def));
     d->t_kind = kind;
     d->d_name = name;
     d->t_type = rhs_type;
     d->d_value = NULL;
     d->d_params = NULL;
     d->d_libid = 0;
     d->d_next = NULL;
     return d;
}

static def decl(int kind, ident name, type rhs_type, scope e) {
     def d = make_def(kind, name, rhs_type);

     if (e == NULL)
	  name->i_glodef = d;
     else {
	  *e->e_link = d;
	  e->e_link = &d->d_next;
	  e->e_ndefs++;
     }

     return d;
}

static def declare(int kind, ident name, type rhs_type) {
     if ((kind == VPARAM || kind == CPARAM)
	 && (same_type(rhs_type, text_type) 
	     || rhs_type->x_kind == ARRAY))
	  kind = APARAM;

     return decl(kind, name, rhs_type, top_scope);
}

static void const_decl(ident name, tree value) { 
     def d = declare(CONST, name, value->t_type);
     d->d_value = get_const(value);
}

static void decl_list(int kind, tree names, type rhs_type) { 
     for (tree t = names; t != nil; t = cdr(t))
	  declare(kind, (ident) car(t), rhs_type);
}

static void begin_proc(ident name) {
     cur_proc = name;
     push_scope();
}

static void def_proc(type ret_type) {
     def d = cur_proc->i_glodef;

     if (d != NULL && d->t_kind == FORWARD) {
	  pop_scope();
	  d->t_kind = PROC;
	  top_scope = d->d_params;
	  return_type = d->t_type;
	  return;
     }	  

     d = decl(PROC, cur_proc, ret_type, (scope) NULL);
     d->d_params = top_scope;
     return_type = ret_type;
}     

static void forward_def(void) {
     cur_proc->i_glodef->t_kind = FORWARD;
     pop_scope();
}

#define MAX 70
#define STEP 5

static char buf[128];
static bool at_start = TRUE, no_break = FALSE;
static int margin = 0, outptr = 0, brkpt = 0, max = MAX;

static void gen_ch(char ch) {
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
	  for (int i = 0; i < margin+2*STEP; i++) putchar(' ');
	  max = MAX-margin-2*STEP;
	  outptr -= brkpt+1;
	  strncpy(buf, &buf[brkpt+1], outptr);
	  brkpt = 0;
     }

     if (at_start) {
	  for (int i = 0; i < margin; i++) putchar(' ');
	  max = MAX - margin;
	  at_start = FALSE;
     }

     if (ch == ' ' && ! no_break) brkpt = outptr;

     buf[outptr++] = ch;
}

static void emit(char *fmt, ...) {
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

int main(int argc, char **argv) {
     init_lex();
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
