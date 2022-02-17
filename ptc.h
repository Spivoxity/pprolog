/* ptc.h */

#define PRIVATE static
#ifndef EXTERN
#define EXTERN extern
#endif

typedef int bool;
#define TRUE 1
#define FALSE 0

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

EXTERN type bool_type, int_type, char_type, text_type,
     scalar_type, string_type, err_type, void_type;

void bad_tag(char *where, int tag);
