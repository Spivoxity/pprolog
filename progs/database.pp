/* database.pp */

uses(mike, compiler, sun) :- .
uses(mike, compiler, pc) :- .
uses(mike, compiler, mac) :- .
uses(mike, editor, sun) :- .
uses(mike, editor, pc) :- .
uses(mike, diary, pc) :- .
uses(anna, editor, mac) :- .
uses(anna, spreadsheet, mac) :- .
uses(jane, database, pc) :- .
uses(jane, compiler, pc) :- .
uses(jane, editor, pc) :- .

needs(compiler, 128) :- .
needs(editor, 512) :- .
needs(diary, 64) :- .
needs(spreadsheet, 640) :- .
needs(database, 8192) :- .

greater(X, Y) :- plus(Y, W, X).


/* The queries from Chapter 2, with small changes for picoProlog syntax: */

answer1(PROGRAM, MEMORY) :-
    uses(PERSON, PROGRAM, mac),
    needs(PROGRAM, MEMORY).

answer2(PROGRAM, MEMORY) :-
    needs(PROGRAM, MEMORY), greater(MEMORY, 256).

answer3(PROGRAM, MEMORY) :-
    needs(PROGRAM, MEMORY), PROGRAM = editor.

answer4(editor, MEMORY) :-
    needs(editor, MEMORY).

answer5(PERSON, PROGRAM) :-
    uses(PERSON, PROGRAM, MACHINE).

answer6(PROGRAM) :-
    needs(PROGRAM, MEMORY), greater(MEMORY, 256).

answer7(MEMORY) :-
    needs(editor, MEMORY).

answer8(PERSON, PROGRAM, MACHINE, MEMORY) :-
    uses(PERSON, PROGRAM, MACHINE),
    needs(PROGRAM, MEMORY).

answer9(PROGRAM, MEMORY) :-
    uses(anna, PROGRAM, mac),
    needs(PROGRAM, MEMORY).

answer10a(PERSON_1, PERSON_2, PROGRAM, MACHINE) :-
    uses(PERSON_1, PROGRAM, MACHINE),
    uses(PERSON_2, PROGRAM, MACHINE).

answer10(PROGRAM) :-
    answer10a(PERSON_1, PERSON_2, PROGRAM, MACHINE),
    not(PERSON_1 = PERSON_2).

answer11(PROGRAM) :-
    answer11a(PROGRAM),
    answer11b(PROGRAM).

answer11a(PROGRAM) :- uses(anna, PROGRAM, MACHINE).

answer11b(PROGRAM) :- uses(jane, PROGRAM, MACHINE).

answer12(PROGRAM) :-
    uses(anna, PROGRAM, MACHINE_1),
    uses(jane, PROGRAM, MACHINE_2).

answer13(PROGRAM) :-
    uses(anna, PROGRAM, MACHINE),
    uses(jane, PROGRAM, MACHINE).

answer14(program) :- answer11a(PROGRAM).
answer14(program) :- answer11b(PROGRAM).

answer15(PROGRAM) :-
    answer11a(PROGRAM), not(answer11b(PROGRAM)).
