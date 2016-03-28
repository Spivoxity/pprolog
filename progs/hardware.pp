/* hardware.pp */

ptran(X, 0, X) :- .
ptran(X, 1, Y) :- .

ntran(X, 1, X) :- .
ntran(X, 0, Y) :- .

pwr(1) :- .
gnd(0) :- .

inverter(A, Z) :-
    pwr(P), gnd(Q),
    ptran(P, A, Z),
    ntran(Z, A, Q).

nand(A, B, Z) :-
    pwr(P), gnd(Q),
    ptran(P, A, Z), ptran(P, B, Z),
    ntran(Z, A, R), ntran(R, B, Q).

and(A, B, Z) :-
    nand(A, B, W),
    inverter(W, Z).

short(X) :- pwr(X), gnd(X).
