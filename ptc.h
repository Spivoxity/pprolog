/* ptc.h */

#define PUBLIC
#define PRIVATE static
#ifndef EXTERN
#define EXTERN extern
#endif

typedef int bool;
#define TRUE 1
#define FALSE 0

#ifndef NULL
#define NULL 0
#endif

#define HASHSIZE 256

typedef struct ident *ident;
typedef struct tree *tree;
typedef struct literal *literal;
typedef struct type *type;
typedef struct scope *scope;
typedef struct def *def;

struct ident {
     char *i_text;
     int i_num;
     int i_lexval, i_op;
     ident i_next;
     def i_glodef;
};

struct literal {
     int t_kind;
     type t_type;
     char *l_value;
};

struct def {
     int t_kind;
     type t_type;
     ident d_name;
     char *d_value;
     scope d_params;
     int d_libid;
     def d_next;
};

struct tree {
     int t_kind;
     type t_type;
     tree t_left, t_right;
};

#define node(k, l, r)	 node_t(k, l, r, none)
#define nil		 ((tree) NULL)
#define cons(h, t)	 node(CONS, h, t)
#define car(t)		 (t)->t_left
#define cdr(t)		 (t)->t_right
#define cadr(t)		 car(cdr(t))
#define caddr(t)	 car(cdr(cdr(t)))
#define list1(x)	 cons(x, nil)
#define snoc(f, b)	 nconc(f, list1(b))

struct type {
     int x_kind;
     ident x_name;
     union {
	  /* empty */         /* PRIMTYPE */
	  struct {	      /* RANGE, POINTER */
	       type x__base;
	       int x__lo, x__hi;
	  } x_range;
	  struct {	      /* ARRAY */
	       type x__index, x__elem;
	  } x_array;
	  scope x__fields;    /* RECORD */
     } x_u;
};

#define x_base	    x_u.x_range.x__base
#define x_lo	    x_u.x_range.x__lo
#define x_hi	    x_u.x_range.x__hi
#define x_index	    x_u.x_array.x__index
#define x_elem	    x_u.x_array.x__elem
#define x_fields    x_u.x__fields

#define none		 ((type) NULL)

struct scope {
     def e_defs;
     def *e_link;
     int e_ndefs;
     scope e_next;
};

/* main.c */
EXTERN char *filename;
PUBLIC void warning(char *msg, ...);
PUBLIC void error(char *msg, ...);
PUBLIC void panic(char *msg, ...);
PUBLIC void bad_tag(char *where, int tag);

/* scan.l */
PUBLIC int yylex(void);
PUBLIC void init_lex(void);
PUBLIC void dump_hash(void);
PUBLIC ident enter(char *name, int lexval);
PUBLIC literal lit_cat(int kind, char *v1, char *v2, type t);

/* parse.y */
PUBLIC int yyparse(void);
PUBLIC tree nconc(tree a, tree b);
PUBLIC tree node_t(int kind, tree left, tree right, type t);
PUBLIC void yyerror(char *msg);

/* sem.c */
PUBLIC void assign(tree lhs, tree rhs);
PUBLIC void write_stmt(int kind, tree args);
PUBLIC void for_loop(tree var, tree first, tree last, int dir);
PUBLIC void enter_case(type arg_type);
PUBLIC void case_labels(tree labels);
PUBLIC void exit_case(void);
PUBLIC void gen_heading();
PUBLIC void gen_forward();
PUBLIC void gen_decl(int kind, ident name, type rhs_type);
PUBLIC void gen_decl_list(int kind, tree names, type rhs_type);

/* expr.c */
PUBLIC tree var_ref(ident name);
PUBLIC tree var_as_exp(tree var);
PUBLIC tree eval(int kind, tree left, tree right);
PUBLIC tree func_call(int kind, ident func, tree args);
PUBLIC void gen_expr(tree expr);
PUBLIC char *get_const(tree expr);
PUBLIC int list_len(tree a);
PUBLIC char *encode(char *s);

/* type.c */
EXTERN type bool_type, int_type, char_type, text_type,
     scalar_type, string_type, err_type, void_type;
EXTERN def _input_, _output_, dummy_def;

PUBLIC bool same_type(type t1, type t2);
PUBLIC bool scalar(type t);
PUBLIC type check_type(char *cxt, type expected, type found);
PUBLIC bool is_string_type(type t);
PUBLIC type const_type(ident name);
PUBLIC type ptr_type(type base);
PUBLIC type range_type(tree lower, tree upper);
PUBLIC type array_type(type index, type elem);
PUBLIC void start_rec_type(void);
PUBLIC type end_rec_type(void);
PUBLIC void init_type(void);

/* symtab.c */
EXTERN ident cur_proc;
EXTERN type return_type;
EXTERN scope top_scope;

PUBLIC def search(ident name, scope s);
PUBLIC def find(ident name);
PUBLIC void const_decl(ident name, tree value);
PUBLIC def declare(int kind, ident name, type rhs_type);
PUBLIC void decl_list(int kind, tree names, type rhs_type);
PUBLIC void push_scope(void);
PUBLIC scope pop_scope(void);
PUBLIC void begin_proc(ident name); 
PUBLIC void def_proc(type ret_type);
PUBLIC void forward_def(void);
PUBLIC void init_symtab(void);

/* library.c */
PUBLIC tree lib_call(def d, tree args);
PUBLIC void gen_libcall(def d, tree args);
PUBLIC void init_lib(void);

/* emit.c */
PUBLIC void emit(char *fmt, ...);
