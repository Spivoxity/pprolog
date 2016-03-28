/* expr.c */

#include "ptc.h"
#include "parse.h"

EXTERN char *equiv[];

PUBLIC tree var_ref(ident name)
{
     def d = find(name);
     if (d == NULL)
	  return (tree) dummy_def;
     else
	  return (tree) d;
}

PUBLIC tree var_as_exp(tree var)
{
     if (var->t_kind == PROC || var->t_kind == FORWARD)
	  return func_call(FUNC, ((def) var)->d_name, nil);
     else
	  return var;
}     

PUBLIC tree eval(int kind, tree left, tree right)
{
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

PUBLIC int list_len(tree a)
{
     int len = 0;
     tree p;

     for (p = a; p != nil; p = cdr(p))
	  len++;
     return len;
}

PRIVATE bool is_var(tree t)
{
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

PUBLIC tree func_call(int kind, ident func, tree args)
{
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

PRIVATE void gen_call(def d, tree args)
{
     bool first = TRUE;
     tree p;

     emit("%x(", d->d_name);
     for (p = args; p != nil; p = cdr(p)) {
	  if (! first) emit(", ");
	  emit("%e", car(p));
	  first = FALSE;
     }
     emit(")");
}

PUBLIC char *encode(char *s)
{
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
	       

PUBLIC void gen_const(type t, char *v)
{
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

PUBLIC void gen_expr(tree expr)
{
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

PUBLIC char *get_const(tree expr)
{
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
