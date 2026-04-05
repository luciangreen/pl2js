% extras/strings.pl — string convenience predicates
%
% These predicates are part of the pl2js prelude and are automatically
% available in every query.  They can be overridden by user code.

% string_lower(+Atom, ?Lower) — lower-case alias for downcase_atom/2
string_lower(X, Y) :- downcase_atom(X, Y).

% string_upper(+Atom, ?Upper) — upper-case alias for upcase_atom/2
string_upper(X, Y) :- upcase_atom(X, Y).
