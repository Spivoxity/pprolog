/* parse.y */

%{
#include "ptc.h"
#include <stdlib.h>

#define YYDEBUG 1
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
%token		AND ARRAY BEGN CASE CONST DIV DO DOWNTO IF ELSE END 
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
		{ gen_heading(); emit("{\n%i"); push_scope(); }
		local.decls 
		{ if (return_type != void_type) {
		    gen_decl(VAR, enter("__R__", BUILTIN), return_type);
		    emit("\n"); } }
		body ';' { pop_scope(); pop_scope(); }
	|	proc.heading FORWARD ';'
		{ gen_forward(); forward_def(); } ;

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

main.prog :	BEGN { emit("void p_main()\n{\n%i"); }
		stmt.list END { emit("%o}\n"); } ;

body 	:	BEGN stmt.list END 
		{ if (return_type != void_type) 
			emit("return __R__;\n");
		  emit("%o}\n\n"); } ;

stmt.list :	stmt
	|	stmt.list ';' stmt ;

stmt	:	basic.stmt
	|	BEGN { emit("{\n%i"); } stmt.list END { emit("%o}\n"); } ;

sub.stmt :	{ emit("\n%i"); } basic.stmt { emit("%o"); }
	|	BEGN { emit(" {\n%i"); } stmt.list END { emit("%o}\n"); } ;

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
		  enter_case($2->t_type);
		  emit("switch (%e) {\n%i", $2); }
		cases opt.semi default.part END
		{ emit("%o}\n"); exit_case(); } ;

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
	|	ident.list ',' IDENT	{ $$ = snoc($1, (tree) $3); } ;

number.list :	NUMBER			{ $$ = list1((tree) $1); }
	|	number.list ',' NUMBER	{ $$ = snoc($1, (tree) $3); } ;

write.params :	/* empty */		{ $$ = nil; }
	|	'(' write.list ')'	{ $$ = $2; } ;

write.list :	write.item		{ $$ = list1($1); }
	|	write.list ',' write.item  { $$ = snoc($1, $3); } ;

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
	|	expr.list ',' expr	{ $$ = snoc($1, $3); }
	;

variable :	IDENT			{ $$ = var_ref($1); }
	|	variable '[' expr ']'	{ $$ = eval(SUB, $1, $3); }
	|	variable '.' IDENT	{ $$ = eval(DOT, $1, (tree) $3); } ;

type	:	type.ident
	|	const DOTDOT const	{ $$ = range_type($1, $3); }
	|	ARRAY '[' type ']' OF type  
					{ $$ = array_type($3, $6); }
	|	RECORD { start_rec_type(); } fields opt.semi END
					{ $$ = end_rec_type(); } ;

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
	|	const.list ',' const	{ $$ = snoc($1, $3); } 	;

%%

PUBLIC tree nconc(tree a, tree b)
{
     if (a == nil)
	  return b;
     else {
	  tree t = a;
	  while (cdr(t) != nil) t = cdr(t);
	  cdr(t) = b;
	  return a;
     }
}

PUBLIC tree node_t(int kind, tree left, tree right, type t)
{
     tree p;

     p = (tree) malloc(sizeof(struct tree));
     p->t_kind = kind;
     p->t_left = left;
     p->t_right = right;
     p->t_type = t;
     return p;
}

PUBLIC void yyerror(char *msg)
{
     error(msg);
}
