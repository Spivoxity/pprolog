/* symtab.c */

#include "ptc.h"
#include "parse.h"
#include <stdlib.h>

PUBLIC def search(ident name, scope s)
{
     def p;

     for (p = s->e_defs; p != NULL; p = p->d_next)
	  if (p->d_name == name)
	       return p;

     return (def) NULL;
}

PUBLIC def find(ident name)
{
     scope d;
     def p;

     for (d = top_scope; d != NULL; d = d->e_next) {
	  p = search(name, d);
	  if (p != NULL) return p;
     }

     if (name->i_glodef != NULL)
	  return name->i_glodef;

     error("undeclared identifier %s", name->i_text);
     return dummy_def;
}

PRIVATE def make_def(int kind, ident name, type rhs_type)
{
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

PRIVATE def decl(int kind, ident name, type rhs_type, scope e)
{
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

PUBLIC def declare(int kind, ident name, type rhs_type)
{
     if ((kind == VPARAM || kind == CPARAM)
	 && (same_type(rhs_type, text_type) 
	     || rhs_type->x_kind == ARRAY))
	  kind = APARAM;

     return decl(kind, name, rhs_type, top_scope);
}

PUBLIC void const_decl(ident name, tree value)
{ 
     def d = declare(CONST, name, value->t_type);
     d->d_value = get_const(value);
}

PUBLIC void decl_list(int kind, tree names, type rhs_type)
{ 
     tree t;

     for (t = names; t != nil; t = cdr(t))
	  declare(kind, (ident) car(t), rhs_type);
}

PUBLIC void push_scope(void)
{
     scope e = (scope) malloc(sizeof(struct scope));

     e->e_defs = NULL;
     e->e_link = &e->e_defs;
     e->e_ndefs = 0;
     e->e_next = top_scope;
     top_scope = e;
}

PUBLIC scope pop_scope(void)
{
     scope e = top_scope;

     if (e == NULL)
	  panic("popping too many scopes");

     top_scope = e->e_next;
     return e;
}

PUBLIC void begin_proc(ident name)
{
     cur_proc = name;
     push_scope();
}

PUBLIC void def_proc(type ret_type)
{
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

PUBLIC void forward_def(void)
{
     cur_proc->i_glodef->t_kind = FORWARD;
     pop_scope();
}

PUBLIC void init_symtab(void)
{ 
     top_scope = NULL;
}
