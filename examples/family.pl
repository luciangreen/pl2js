% family.pl - Sample Prolog program for pl2js
% Demonstrates facts, rules, lists, and basic I/O

% ---- Facts ----
parent(tom, bob).
parent(tom, liz).
parent(bob, ann).
parent(bob, pat).
parent(pat, jim).

% ---- Rules ----
grandparent(X, Z) :- parent(X, Y), parent(Y, Z).

ancestor(X, Y) :- parent(X, Y).
ancestor(X, Y) :- parent(X, Z), ancestor(Z, Y).

% ---- List predicates ----
member(X, [X|_]).
member(X, [_|T]) :- member(X, T).

append([], L, L).
append([H|T1], L2, [H|T3]) :- append(T1, L2, T3).

% ---- Numeric example ----
max(X, Y, X) :- X >= Y, !.
max(_, Y, Y).

% ---- Main entry point (called at startup) ----
main :-
    write('=== Family Relationships ==='), nl,
    ( grandparent(tom, ann) ->
        write('grandparent(tom, ann) = true'), nl
    ;
        write('grandparent(tom, ann) = false'), nl
    ),
    ( member(bob, [tom, bob, liz]) ->
        write('member(bob, [tom,bob,liz]) = true'), nl
    ;
        write('member(bob, [tom,bob,liz]) = false'), nl
    ),
    max(3, 5, M),
    write('max(3,5) = '), write(M), nl,
    write('=== Done ==='), nl.
