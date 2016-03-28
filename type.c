/* type.c */

#include "ptc.h"
#include "parse.h"
#include <stdlib.h>

PRIVATE type alloc_type(void)
{
     type t = (type) malloc(sizeof(struct type));
     t->x_name = NULL;
     return t;
}

/* same_type -- check types are compatible */
PUBLIC bool same_type(type t1, type t2)
{
     if (t1->x_kind == RANGE) t1 = t1->x_base;
     if (t2->x_kind == RANGE) t2 = t2->x_base;
     return (t1 == t2 || t1 == err_type || t2 == err_type);
}

/* scalar -- test if type is scalar */
PUBLIC bool scalar(type t)
{
     return (t == int_type || t == char_type || t == bool_type 
	     || t == err_type || t->x_kind == RANGE);
}

/* check_type -- check for expected type and return it */
PUBLIC type check_type(char *cxt, type expected, type found)
{
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

PUBLIC type const_type(ident name)
{
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

PUBLIC type ptr_type(type base)
{
     type p = alloc_type();
     p->x_kind = POINTER;
     p->x_base = base;
     return p;
}

PUBLIC bool is_string_type(type t)
{
     return (t->x_kind == ARRAY && same_type(t->x_elem, char_type)
	     && t->x_index->x_base == int_type 
	     && t->x_index->x_lo == 1);
}

PUBLIC type range_type(tree lower, tree upper)
{ 
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

PUBLIC type array_type(type index, type elem)
{ 
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

PUBLIC void start_rec_type(void)
{
     push_scope();
}

PUBLIC type end_rec_type(void)
{
     type p = alloc_type();

     p->x_kind = RECORD;
     p->x_fields = pop_scope();
     return p;
}

PRIVATE type prim_type(char *name)
{
     ident sym = enter(name, BUILTIN);
     type p = alloc_type();

     p->x_kind = PRIMTYPE;
     p->x_name = sym;
     declare(TYPE, sym, p);
     return p;
}     

PRIVATE def def_const(char *name, type val_type, char *value)
{
     def d = declare(CONST, enter(name, BUILTIN), val_type);
     d->d_value = value;
     return d;
}

PUBLIC void init_type(void)
{
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
