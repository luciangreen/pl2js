% lists.pl — list operations example for pl2js
%
% Demonstrates: member, append, length, last, reverse.
% Try queries like:
%   member(X, [1,2,3]).
%   append([1,2], [3,4], L).
%   my_length([a,b,c], N).
%   my_reverse([1,2,3], R).

% ---- Membership ----
member(X, [X|_]).
member(X, [_|T]) :- member(X, T).

% ---- Append ----
append([], L, L).
append([H|T1], L2, [H|T3]) :- append(T1, L2, T3).

% ---- Length (named my_length to avoid clash with built-in) ----
my_length([], 0).
my_length([_|T], N) :- my_length(T, N1), N is N1 + 1.

% ---- Last element ----
my_last([X], X).
my_last([_|T], X) :- my_last(T, X).

% ---- Reverse ----
my_reverse([], []).
my_reverse([H|T], R) :- my_reverse(T, RT), append(RT, [H], R).

% ---- Nth element (0-indexed) ----
nth(0, [H|_], H).
nth(N, [_|T], X) :- N > 0, N1 is N - 1, nth(N1, T, X).

% ---- Sum of a list ----
sum_of([], 0).
sum_of([H|T], S) :- sum_of(T, S1), S is S1 + H.

% ---- Main demo ----
main :-
    write('member(2, [1,2,3]) = '),
    ( member(2, [1,2,3]) -> write(true) ; write(false) ), nl,
    append([1,2], [3,4], L),
    write('append([1,2],[3,4],L) = '), write(L), nl,
    my_length([a,b,c,d], N),
    write('my_length([a,b,c,d],N) = '), write(N), nl,
    my_reverse([1,2,3], R),
    write('my_reverse([1,2,3],R) = '), write(R), nl,
    sum_of([1,2,3,4,5], S),
    write('sum_of([1,2,3,4,5],S) = '), write(S), nl.
