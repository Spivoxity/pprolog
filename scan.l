%{
#include "ptc.h"
#include "parse.h"
#include <string.h>
#include <stdio.h>
#include <ctype.h>

extern YYSTYPE yylval;

int line = 1;

static int lookup(char *t);
static int save_string(char *t, int kind);

static int yywrap(void) { return 1; }
%}

%x COMMENT

%%

[A-Za-z][A-Za-z0-9]*		return lookup(/*strlwr*/(yytext));
[0-9]+				return save_string(yytext, NUMBER);
"'"([^']|"''")*"'"		return save_string(yytext, STRING);
[*/+<>]				return lookup(yytext);
[=.,;:()]			return *yytext;
"-"|"["|"]"			return *yytext;
":="				return ASSIGN;
".."				return DOTDOT;
">="|"<="|"<>"			return lookup(yytext);
"{"				BEGIN COMMENT;
[ \t\f]*			;
.				printf("<%c>", *yytext);
\n				line++;

<COMMENT>"}"			BEGIN 0;
<COMMENT>.			;
<COMMENT>\n			line++;

%%

static ident hashtable[HASHSIZE];
static int n_idents = 0;

ident enter(char *t, int lexval) {
     unsigned h = 0;
     char *s;
     ident p;

     for (s = t; *s != '\0'; s++)
	  h = h * 5 + *s;
     h %= HASHSIZE;

     for (p = hashtable[h]; p != NULL; p = p->i_next)
	  if (strcmp(t, p->i_text) == 0)
	       goto found;

     p = (ident) malloc(sizeof(struct ident));
     p->i_text = strdup(t);
     p->i_num = (lexval == IDENT ? n_idents++ : -1);
     p->i_lexval = (lexval == BUILTIN ? IDENT : lexval);
     p->i_op = 0;
     p->i_next = hashtable[h];
     p->i_glodef = NULL;
     hashtable[h] = p;

found:
     return p;
}

static int lookup(char *t) {
     ident p = enter(t, IDENT);
     yylval.I = p;
     return p->i_lexval;
}

static char buf[256];

static char *translit(char *s) {
     char *t = buf;

     s++;
     do {
	  while (*s != '\'')
	       *t++ = *s++;
	  if (*(s+1) == '\'') {
	       *t++ = '\'';
	       s += 2;
	  }
     } while (*s != '\'');
     *t++ = '\0';

     return buf;
}

static literal make_literal(int kind, char *v, type t) {
     literal p;

     p = (literal) malloc(sizeof(struct literal));
     p->t_kind = kind;
     p->t_type = t;
     p->l_value = strdup(v);
     return p;
}

literal lit_cat(int kind, char *v1, char *v2, type t) {
     strcpy(buf, v1);
     strcat(buf, v2);
     return make_literal(kind, buf, t);
}

static int save_string(char *t, int kind) {
     char *tt;

     switch (kind) {
     case NUMBER:
	  yylval.L = make_literal(NUMBER, t, int_type);
	  break;
     case STRING:
	  tt = translit(t);
	  yylval.L = make_literal(STRING, tt,
	       (strlen(tt) == 1 ? char_type : string_type));
	  break;
     default:
	  bad_tag("save_string", kind);
     }

     return kind;
}

char *equiv[N_TOKENS];

void def_op(char *name, int lexval, int op, char *eq) {
     if (*name != '\0') {
	  ident i = enter(name, lexval);
	  i->i_op = op;
     }
     equiv[op] = eq;
}

void init_lex(void) {
     int i;

     for (i = 0; i < N_TOKENS; i++)
	  equiv[i] = "?!?";

     enter("array", ARRAY);
     enter("begin", BEG);
     enter("case", CASE);
     enter("const", CONST);
     enter("do", DO);
     enter("downto", DOWNTO);	
     enter("if", IF);
     enter("else", ELSE);
     enter("end", END);
     enter("for", FOR);
     enter("forward", FORWARD);
     enter("function", FUNC);
     enter("goto", GOTO);
     enter("label", LABEL);
     enter("of", OF);
     enter("procedure", PROC);
     enter("program", PROGRAM);
     enter("record", RECORD);
     enter("repeat", REPEAT);
     enter("then", THEN);
     enter("to", TO);
     enter("type", TYPE);
     enter("until", UNTIL);
     enter("var", VAR);
     enter("while", WHILE);
     enter("write", WRITE);
     enter("writeln", WRITE);

     def_op("not", MONOP, NOT, "!");
     def_op("",    MONOP, UMINUS, "-");
     def_op("",    MONOP, NEG, "~");
     def_op("*",   MULOP, '*', "*");
     def_op("/",   MULOP, '/', "/");
     def_op("div", MULOP, DIV, "/");
     def_op("mod", MULOP, MOD, "%");
     def_op("and", MULOP, AND, "&&");
     def_op("",    MULOP, BITAND, "&");
     def_op("shl", MULOP, SHL, "<<");
     def_op("shr", MULOP, SHR, ">>");
     def_op("+",   ADDOP, '+', "+");
     def_op("-",   ADDOP, '-', "-");
     def_op("or",  ADDOP, OR,  "||");
     def_op("",    ADDOP, BITOR, "|");
     def_op("=",   RELOP, '=', "==");
     def_op("<",   RELOP, '<', "<");
     def_op(">",   RELOP, '>', ">");
     def_op("<>",  RELOP, NEQ, "!=");
     def_op("<=",  RELOP, LEQ, "<=");
     def_op(">=",  RELOP, GEQ, ">=");
}
