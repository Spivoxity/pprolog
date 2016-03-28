/* sem.c */

#include "ptc.h"
#include "parse.h"

PUBLIC void assign(tree lhs, tree rhs)
{
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

PUBLIC void for_loop(tree var, tree first, tree last, int dir)
{
     emit("for (%e = %e; %e %s %e; %e%s)",
	  var, first,
	  var, (dir == DOWNTO ? ">=" : "<="), last, 
	  var, (dir == DOWNTO ? "--" : "++"));
}

PUBLIC void enter_case(type arg_type)
{ }

PUBLIC void case_labels(tree labels)
{
     tree t;

     for (t = labels; t != nil; t = cdr(t))
	  emit("%ocase %e:\n%i", car(t));
}

PUBLIC void exit_case(void)
{ }

PRIVATE void gen_scope_decls(scope e)
{
     def d;

     for (d = e->e_defs; d != NULL; d = d->d_next)
	  gen_decl(d->t_kind, d->d_name, d->t_type);
}

PUBLIC void gen_heading(void)
{
     def d;
     bool first = TRUE;

     emit("%x %x(", return_type->x_name, cur_proc);
     for (d = top_scope->e_defs; d != NULL; d = d->d_next) {
	  emit((first ? "%x" : ", %x"), d->d_name);
	  first = FALSE;
     }
     emit(")\n");
     if (top_scope->e_defs != NULL)
	  gen_scope_decls(top_scope);
}

PUBLIC void gen_forward(void)
{
     emit("%x %x();\n\n", return_type->x_name, cur_proc);
}

PRIVATE void gen_type_root(type t)
{
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

PRIVATE void gen_var_pattern(ident name, type t)
{
     if (t->x_name == NULL && t->x_kind == ARRAY) {
	  gen_var_pattern(name, t->x_elem);
	  emit("[%d]", t->x_index->x_hi - t->x_index->x_lo + 1);
     }
     else if (t->x_name == NULL && t->x_kind == POINTER) {
	  emit("(*");
	  gen_var_pattern(name, t->x_base);
	  emit(")");
     }
     else
	  emit("%x", name);
}

PUBLIC void gen_decl(int kind, ident name, type rhs_type)
{
     if (kind == TYPE)
	  emit("typedef ");

     gen_type_root(rhs_type);
     emit(" ");
     gen_var_pattern(name,
		     (kind == VPARAM ? ptr_type(rhs_type): rhs_type));
     emit(";\n");
}

PUBLIC void gen_decl_list(int kind, tree names, type rhs_type)
{
     tree t;
     bool first = TRUE;

     gen_type_root(rhs_type);
     for (t = names; t != nil; t = cdr(t)) {
	  emit(first ? " " : ", ");
	  gen_var_pattern((ident) car(t), rhs_type);
	  first = FALSE;
     }
     emit(";\n");
}
