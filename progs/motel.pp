/* motel.pp */

suite(FD, LW, BD, BW) :-
    lounge(FD, LW, BD),
    bedroom(BD, BW).

lounge(FD, LW, BD) :-
    opposite(FD, LW),
    adjacent(FD, BD).

bedroom(BD, BW) :-
    adjacent(BD, BW),
    BW = east.

opposite(north, south) :- .
opposite(south, north) :- .
opposite(east, west) :- .
opposite(west, east) :- .

adjacent(north, east) :- .
adjacent(north, west) :- .
adjacent(south, east) :- .
adjacent(south, west) :- .
adjacent(east, north) :- .
adjacent(east, south) :- .
adjacent(west, north) :- .
adjacent(west, south) :- .
