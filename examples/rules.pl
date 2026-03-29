% rules.pl — rule chains and simple inference example for pl2js
%
% Demonstrates: multi-step rules, negation-as-failure (\+), disjunction.
% Try queries like:
%   mortal(X).
%   happy(X).
%   sibling(X, Y).
%   can_fly(X).

% ---- Classical syllogism ----
mortal(X) :- human(X).

human(socrates).
human(plato).
human(aristotle).

% ---- Likes / happiness ----
likes(mary, food).
likes(mary, wine).
likes(mary, john).
likes(john, wine).
likes(john, mary).

happy(X) :- likes(X, Y), likes(Y, X).

% ---- Family / sibling ----
parent(tom, bob).
parent(tom, liz).
parent(bob, ann).
parent(bob, pat).
parent(pat, jim).

sibling(X, Y) :- parent(Z, X), parent(Z, Y), X \= Y.

grandparent(X, Z) :- parent(X, Y), parent(Y, Z).

% ---- Bird / flight rules ----
bird(tweety).
bird(sam).
penguin(sam).

can_fly(X) :- bird(X), \+ penguin(X).

% ---- Numeric classifier ----
classify(N, positive) :- N > 0.
classify(0, zero).
classify(N, negative) :- N < 0.

% ---- Main demo ----
main :-
    write('=== Rule Chain Demo ==='), nl,
    write('mortal(socrates) = '),
    ( mortal(socrates) -> write(true) ; write(false) ), nl,
    write('happy(john) = '),
    ( happy(john) -> write(true) ; write(false) ), nl,
    write('can_fly(tweety) = '),
    ( can_fly(tweety) -> write(true) ; write(false) ), nl,
    write('can_fly(sam) = '),
    ( can_fly(sam) -> write(true) ; write(false) ), nl,
    classify(42, C1), write('classify(42) = '), write(C1), nl,
    classify(-3, C2), write('classify(-3) = '), write(C2), nl,
    write('=== Done ==='), nl.
