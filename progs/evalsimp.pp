/* evalsimp.pp */

value(X, X) :- integer(X).

value(add(E_1, E_2), V) :-
    value(E_1, V_1), value(E_2, V_2),
    plus(V_1, V_2, V).

value(multiply(E_1, E_2), V) :-
    value(E_1, V_1), value(E_2, V_2),
    times(V_1, V_2, V).

calculator(S, V) :- expr(E, S, ""), value(E, V).


lookup(X, A, V) :- member(val(X, V), A).

member(X, X:A) :- .
member(X, Y:A) :- member(X, A).

eval(X, A, X) :- integer(X).
eval(vbl(X), A, V) :- lookup(X, A, V).

eval(add(E_1, E_2), A, V) :-
    eval(E_1, A, V_1), eval(E_2, A, V_2), plus(V_1, V_2, V).

eval(multiply(E_1, E_2), A, V) :-
    eval(E_1, A, V_1), eval(E_2, A, V_2), times(V_1, V_2, V).


simp(add(E, 0), E) :- .
simp(multiply(E, 1), E) :- .
simp(add(0, E), E) :- .
simp(multiply(1, E), E) :- .

simp(multiply(A, add(B, C)),
    add(multiply(A, B), multiply(B, C))) :- .

simp(add(A, B), add(A_1, B)) :- simp(A, A_1).
simp(add(A, B), add(A, B_1)) :- simp(B, B_1).
simp(multiply(A, B), multiply(A_1, B)) :- simp(A, A_1).
simp(multiply(A, B), multiply(A, B_1)) :- simp(B, B_1).

simplify(X, Y) :- simp(X, X1), simplify(X1, Y).
simplify(X, X) :- not(reducible(X)).

reducible(X) :- simp(X, Y).

