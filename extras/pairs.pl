% extras/pairs.pl — Key-Value pair predicates
%
% These predicates are part of the pl2js prelude and are automatically
% available in every query.  They can be overridden by user code.

% pairs_keys_values(?Pairs, ?Keys, ?Values)
pairs_keys_values([], [], []).
pairs_keys_values([K-V|Ps], [K|Ks], [V|Vs]) :- pairs_keys_values(Ps, Ks, Vs).

% pairs_keys(?Pairs, ?Keys) — extract keys from a list of Key-Value pairs
pairs_keys([], []).
pairs_keys([K-_|Ps], [K|Ks]) :- pairs_keys(Ps, Ks).

% pairs_values(?Pairs, ?Values) — extract values from a list of Key-Value pairs
pairs_values([], []).
pairs_values([_-V|Ps], [V|Vs]) :- pairs_values(Ps, Vs).
