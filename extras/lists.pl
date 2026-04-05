% extras/lists.pl — extra list predicates
%
% These predicates are part of the pl2js prelude and are automatically
% available in every query.  They can be overridden by user code.

% not_member(?X, +List) — succeeds when X is not a member of List
not_member(_, []).
not_member(X, [H|T]) :- X \= H, not_member(X, T).

% max_member(?Max, +List) — Max is the largest element (standard order)
max_member(Max, [Max]).
max_member(Max, [H|T]) :- max_member(TMax, T), (H @>= TMax -> Max = H ; Max = TMax).

% min_member(?Min, +List) — Min is the smallest element (standard order)
min_member(Min, [Min]).
min_member(Min, [H|T]) :- min_member(TMin, T), (H @=< TMin -> Min = H ; Min = TMin).
