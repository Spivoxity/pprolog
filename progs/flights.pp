/* flights.pp */

flight(london, paris) :- .
flight(london, dublin) :- .
flight(paris, berlin) :- .
flight(paris, rome) :- .
flight(berlin, london) :- .

journey(A, A) :- .
journey(A, C) :- flight(A, B), journey(B, C).

