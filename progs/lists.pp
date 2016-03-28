/* lists.pp */

/* Various relations on lists taken from Chapters 3, 5 and 8: */

append(nil, B, B) :- .
append(X:A, B, X:C) :- append(A, B, C).

list(nil) :- .
list(X:A) :- list(A).

member(X, X:A) :- .
member(Y, X:A) :- member(Y, A).

dominates(X, nil) :- .
dominates(X, Y:A) :- geq(X, Y), dominates(X, A).

maximum(X, A) :- member(X, A), dominates(X, A).

max1(X, X, nil) :- .
max1(X, Y, Z:A) :- geq(Y, Z), max1(X, Y, A).
max1(X, Y, Z:A) :- less(Y, X), max1(X, Z, A).

maximum1(X, Y:A) :- max1(X, Y, A).

member1(X, A) :- append(U, X:V, A).

flatten(tip(X), X:nil) :- .
flatten(fork(L, R), C) :- 
    flatten(L, A), flatten(R, B), append(A, B, C).

reverse(nil, nil) :- .
reverse(X:A, C) :- reverse(A, B), append(B, X:nil, C).

subset(A, B) :- not(nonsubset(A, B)).
nonsubset(A, B) :- member(X, A), not(member(X, B)).

subset1(nil, B) :- .
subset1(X:A, B) :- member(X, B), subset1(A, B).

