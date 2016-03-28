/* expr.pp */

expr(T, A, C) :- term(T_1, A, B), exprtail(T_1, T, B, C).

exprtail(T_1, T_1, A, A) :- .
exprtail(T_1, T, A, D) :- 
    eat('+', A, B), term(T_2, B, C),
    exprtail(add(T_1, T_2), T, C, D).
exprtail(T_1, T, A, D) :- 
    eat('-', A, B), term(T_2, B, C),
    exprtail(subtract(T_1, T_2), T, C, D).

term(T, A, C) :-
    factor(T_1, A, B), termtail(T_1, T, B, C).

termtail(T_1, T_1, A, A) :- .
termtail(T_1, T, A, D) :-
    eat('*', A, B), factor(T_2, B, C),
    termtail(multiply(T_1, T_2), T, C, D).
termtail(T_1, T, A, D) :-
    eat('/', A, B), factor(T_2, B, C),
    termtail(divide(T_1, T_2), T, C, D).

factor(vbl(x), A, B) :- eat('x', A, B).
factor(vbl(y), A, B) :- eat('y', A, B).
factor(T, A, D) :-
    eat('(', A, B), expr(T, B, C), eat(')', C, D).

eat(X, X:A, A) :- .
