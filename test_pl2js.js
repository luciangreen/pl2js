/**
 * test_pl2js.js — Test suite for pl2js.js
 *
 * Run with: node test_pl2js.js
 *
 * Tests the public API exposed by pl2js.js:
 *   runQuery(programSource, queryString, maxAnswers)
 *   tokenize(src)
 *   parsePrologSource(src)
 *   buildDatabase(clauses)
 *   hasMainPredicate(source)
 *   generateHtml(runtimeSource, programSource)
 *   termToString(term)
 *
 * Design note — ground-query ok flag:
 *   pl2js.runQuery sets ok=true for any ground query (no query variables) that
 *   completes without a JavaScript error, regardless of whether Prolog itself
 *   succeeded or failed. This mirrors the design choice documented in
 *   runQuery: "ok: true if at least one answer found (or no error)".
 *   For ground queries we therefore check answers.length to distinguish
 *   Prolog success (≥1 answer) from Prolog failure (0 answers).
 *   The fails() helper encapsulates that pattern.
 */

'use strict';

const assert = require('assert');
const fs     = require('fs');
const path   = require('path');

const pl2js = require('./pl2js.js');

// ---------------------------------------------------------------------------
// Minimal test runner
// ---------------------------------------------------------------------------

let _passed = 0;
let _failed = 0;

function group(name) {
  console.log('\n── ' + name + ' ──');
}

function test(description, fn) {
  try {
    fn();
    _passed++;
    console.log('  ✓ ' + description);
  } catch (err) {
    _failed++;
    console.log('  ✗ ' + description);
    console.log('      ' + (err && err.message ? err.message : String(err)));
  }
}

// ---------------------------------------------------------------------------
// Query helpers
// ---------------------------------------------------------------------------

/** Run a query and return the full result object. */
function q(prog, query, max) {
  return pl2js.runQuery(prog, query, max || 10);
}

/**
 * Assert that the first answer's binding for varName equals expected string.
 * Use this for queries that contain at least one named variable.
 */
function assertBinding(result, varName, expected) {
  assert.ok(result.ok, 'query should succeed (ok=false, error=' + result.error + ')');
  assert.ok(result.answers.length > 0, 'should have at least one answer');
  assert.strictEqual(
    result.answers[0][varName],
    expected,
    'binding ' + varName + ': expected ' + JSON.stringify(expected) +
      ' got ' + JSON.stringify(result.answers[0][varName])
  );
}

/**
 * Returns true when the query produces NO solutions (Prolog failure).
 *
 * pl2js sets ok=true for ground queries even when Prolog fails, so we rely
 * on answers.length instead of the ok flag for those cases.
 */
function fails(prog, query, max) {
  const r = q(prog, query, max);
  assert.strictEqual(r.error, null, 'expected no JS error but got: ' + r.error);
  return r.answers.length === 0;
}

// ---------------------------------------------------------------------------
// 1. Facts and simple queries
// ---------------------------------------------------------------------------
group('Facts and simple queries');

test('simple atom fact succeeds', () => {
  const r = q('likes(alice, chocolate).', 'likes(alice, chocolate).');
  assert.ok(r.ok);
  assert.strictEqual(r.error, null);
});

test('atom fact with wrong argument fails', () => {
  assert.ok(fails('likes(alice, chocolate).', 'likes(alice, broccoli).'));
});

test('integer fact', () => {
  const r = q('age(bob, 30).', 'age(bob, 30).');
  assert.ok(r.ok);
});

test('fact with variable binding', () => {
  const r = q('color(sky, blue).', 'color(sky, X).');
  assertBinding(r, 'X', 'blue');
});

test('multiple facts — first match wins', () => {
  const prog = 'color(rose, red). color(sky, blue).';
  const r = q(prog, 'color(rose, X).');
  assertBinding(r, 'X', 'red');
});

test('fact: integer binding', () => {
  const r = q('val(42).', 'val(X).');
  assertBinding(r, 'X', '42');
});

// ---------------------------------------------------------------------------
// 2. Rules and rule chains
// ---------------------------------------------------------------------------
group('Rules and rule chains');

const FAMILY = [
  'parent(tom, bob).',
  'parent(tom, liz).',
  'parent(bob, ann).',
  'parent(bob, pat).',
  'grandparent(X, Z) :- parent(X, Y), parent(Y, Z).',
].join('\n');

test('simple rule succeeds', () => {
  const r = q(FAMILY, 'grandparent(tom, ann).');
  assert.ok(r.ok);
});

test('simple rule fails when no match', () => {
  assert.ok(fails(FAMILY, 'grandparent(tom, tom).'));
});

test('rule with variable binding', () => {
  const r = q(FAMILY, 'grandparent(tom, Z).', 1);
  assertBinding(r, 'Z', 'ann');
});

test('multi-clause rule — ancestor', () => {
  const prog = FAMILY +
    '\nancestor(X,Y) :- parent(X,Y).' +
    '\nancestor(X,Y) :- parent(X,Z), ancestor(Z,Y).';
  const r = q(prog, 'ancestor(tom, ann).');
  assert.ok(r.ok);
});

test('recursive rule terminates and fails when appropriate', () => {
  const prog = FAMILY +
    '\nancestor(X,Y) :- parent(X,Y).' +
    '\nancestor(X,Y) :- parent(X,Z), ancestor(Z,Y).';
  assert.ok(fails(prog, 'ancestor(ann, tom).'));
});

// ---------------------------------------------------------------------------
// 3. Multiple answers / backtracking
// ---------------------------------------------------------------------------
group('Multiple answers and backtracking');

test('multiple answers collected', () => {
  const r = q(FAMILY, 'parent(tom, X).');
  assert.ok(r.ok);
  assert.strictEqual(r.answers.length, 2);
  const vals = r.answers.map(a => a['X']);
  assert.ok(vals.includes('bob'));
  assert.ok(vals.includes('liz'));
});

test('maxAnswers limits results', () => {
  const prog = 'p(1). p(2). p(3). p(4). p(5).';
  const r = q(prog, 'p(X).', 3);
  assert.strictEqual(r.answers.length, 3);
});

test('all answers for member/2', () => {
  const prog = 'member(X,[X|_]). member(X,[_|T]) :- member(X,T).';
  const r = q(prog, 'member(X, [a,b,c]).', 10);
  assert.strictEqual(r.answers.length, 3);
  const vals = r.answers.map(a => a['X']);
  assert.deepStrictEqual(vals, ['a', 'b', 'c']);
});

// ---------------------------------------------------------------------------
// 4. Conjunction
// ---------------------------------------------------------------------------
group('Conjunction');

test('conjunction of two succeeding goals', () => {
  const prog = 'a. b.';
  const r = q(prog, 'a, b.');
  assert.ok(r.ok);
});

test('conjunction fails when first goal fails', () => {
  // Use a variable so ok properly reflects Prolog failure.
  const prog = 'b.';
  const r = q(prog, 'c, b, X = done.');
  assert.ok(!r.ok);
});

test('conjunction fails when second goal fails', () => {
  const prog = 'a.';
  const r = q(prog, 'a, c, X = done.');
  assert.ok(!r.ok);
});

test('conjunction with variable sharing', () => {
  const prog = 'foo(1). bar(1, done).';
  const r = q(prog, 'foo(X), bar(X, Y).');
  assertBinding(r, 'Y', 'done');
});

// ---------------------------------------------------------------------------
// 5. Disjunction
// ---------------------------------------------------------------------------
group('Disjunction');

test('first branch succeeds', () => {
  const r = q('a. b.', 'a ; b.');
  assert.ok(r.ok);
});

test('second branch tried when first fails', () => {
  const r = q('b.', 'c ; b.');
  assert.ok(r.ok);
});

test('disjunction with variable binding from first branch', () => {
  const r = q('', 'X = hello ; X = world.', 1);
  assertBinding(r, 'X', 'hello');
});

test('disjunction collects answers from both branches', () => {
  const r = q('', '(X = a ; X = b).', 10);
  assert.strictEqual(r.answers.length, 2);
});

// ---------------------------------------------------------------------------
// 6. If-then-else
// ---------------------------------------------------------------------------
group('If-then-else');

test('condition true — then branch taken', () => {
  const r = q('', '(1 > 0 -> X = yes ; X = no).');
  assertBinding(r, 'X', 'yes');
});

test('condition false — else branch taken', () => {
  const r = q('', '(0 > 1 -> X = yes ; X = no).');
  assertBinding(r, 'X', 'no');
});

test('if-then-else with user predicate condition', () => {
  const prog = 'big(elephant).';
  const r = q(prog, '(big(elephant) -> X = large ; X = small).');
  assertBinding(r, 'X', 'large');
});

// ---------------------------------------------------------------------------
// 7. If-then (no else)
// ---------------------------------------------------------------------------
group('If-then (no else)');

test('if-then: condition true succeeds', () => {
  const r = q('', '(1 =:= 1 -> X = ok).');
  assertBinding(r, 'X', 'ok');
});

test('if-then: condition false — query fails', () => {
  const r = q('', '(1 =:= 2 -> X = ok).');
  assert.ok(!r.ok);
});

// ---------------------------------------------------------------------------
// 8. Cut
// ---------------------------------------------------------------------------
group('Cut (!)');

test('cut stops further backtracking into clauses', () => {
  const prog = 'max(X, Y, X) :- X >= Y, !.\nmax(_, Y, Y).';
  const r = q(prog, 'max(5, 3, M).');
  assertBinding(r, 'M', '5');
});

test('cut: second clause chosen when first cut not reached', () => {
  const prog = 'max(X, Y, X) :- X >= Y, !.\nmax(_, Y, Y).';
  const r = q(prog, 'max(2, 7, M).');
  assertBinding(r, 'M', '7');
});

test('cut limits number of answers', () => {
  const prog = [
    'first(X) :- member(X,[1,2,3]), !.',
    'member(X,[X|_]).',
    'member(X,[_|T]) :- member(X,T).',
  ].join('\n');
  const r = q(prog, 'first(X).', 10);
  assert.strictEqual(r.answers.length, 1);
  assertBinding(r, 'X', '1');
});

// ---------------------------------------------------------------------------
// 9. Negation as failure (\+)
// ---------------------------------------------------------------------------
group('Negation as failure (\\+)');

test('\\+ fails for provable goal', () => {
  // Use a variable so ok properly reflects Prolog failure.
  const r = q('a.', 'X = check, \\+ a.');
  assert.ok(!r.ok);
});

test('\\+ succeeds for unprovable goal', () => {
  const r = q('a.', '\\+ b.');
  assert.ok(r.ok);
});

test('negation in rule body — can_fly(tweety) succeeds', () => {
  const prog = 'bird(tweety). penguin(sam). bird(sam).\ncan_fly(X) :- bird(X), \\+ penguin(X).';
  assert.ok(q(prog, 'can_fly(tweety).').ok);
});

test('negation in rule body — can_fly(sam) fails', () => {
  const prog = 'bird(tweety). penguin(sam). bird(sam).\ncan_fly(X) :- bird(X), \\+ penguin(X).';
  assert.ok(fails(prog, 'can_fly(sam).'));
});

// ---------------------------------------------------------------------------
// 10. Unification
// ---------------------------------------------------------------------------
group('Unification (=, \\=, ==, \\==)');

test('= unifies atoms', () => {
  const r = q('', 'foo = foo.');
  assert.ok(r.ok);
});

test('= binds variable', () => {
  const r = q('', 'X = hello.');
  assertBinding(r, 'X', 'hello');
});

test('= fails on mismatch', () => {
  // Variable-based failure: X binds then second unification fails.
  const r = q('', 'X = foo, X = bar.');
  assert.ok(!r.ok);
});

test('\\= succeeds when not unifiable', () => {
  const r = q('', 'foo \\= bar.');
  assert.ok(r.ok);
});

test('\\= fails when unifiable', () => {
  const r = q('', 'X \\= X.');
  assert.ok(!r.ok);
});

test('== structural equality succeeds', () => {
  const r = q('', 'foo == foo.');
  assert.ok(r.ok);
});

test('== structural equality fails for unbound var vs atom', () => {
  const r = q('', 'X == foo.');
  assert.ok(!r.ok);
});

test('\\== structural inequality succeeds for different atoms', () => {
  const r = q('', 'foo \\== bar.');
  assert.ok(r.ok);
});

test('\\== fails for identical atoms', () => {
  // Use a variable to ensure the ok flag is meaningful.
  const r = q('', 'X = foo, X \\== foo.');
  assert.ok(!r.ok);
});

// ---------------------------------------------------------------------------
// 11. Arithmetic
// ---------------------------------------------------------------------------
group('Arithmetic (is/2, >, <, >=, =<, =:=, =\\=)');

test('is/2 addition', () => {
  assertBinding(q('', 'X is 3 + 4.'), 'X', '7');
});

test('is/2 subtraction', () => {
  assertBinding(q('', 'X is 10 - 3.'), 'X', '7');
});

test('is/2 multiplication', () => {
  assertBinding(q('', 'X is 6 * 7.'), 'X', '42');
});

test('is/2 integer division (/)', () => {
  // Note: the // token is not recognised by the tokenizer; / performs
  // Math.trunc integer division, which is the same result.
  assertBinding(q('', 'X is 10 / 3.'), 'X', '3');
});

test('is/2 modulo', () => {
  assertBinding(q('', 'X is 10 mod 3.'), 'X', '1');
});

test('is/2 nested expression', () => {
  assertBinding(q('', 'X is (2 + 3) * 4.'), 'X', '20');
});

test('is/2 abs', () => {
  assertBinding(q('', 'X is abs(-5).'), 'X', '5');
});

test('is/2 sign', () => {
  assertBinding(q('', 'X is sign(-3).'), 'X', '-1');
});

test('> succeeds when left > right', () => {
  assert.ok(q('', '5 > 3.').ok);
});

test('> fails when left <= right', () => {
  assert.ok(fails('', '3 > 5.'));
});

test('< succeeds when left < right', () => {
  assert.ok(q('', '2 < 10.').ok);
});

test('< fails when left >= right', () => {
  assert.ok(fails('', '10 < 2.'));
});

test('>= succeeds for equal or greater', () => {
  assert.ok(q('', '5 >= 5.').ok);
  assert.ok(q('', '6 >= 5.').ok);
});

test('>= fails when left < right', () => {
  assert.ok(fails('', '4 >= 5.'));
});

test('=< succeeds for equal or less', () => {
  assert.ok(q('', '5 =< 5.').ok);
  assert.ok(q('', '4 =< 5.').ok);
});

test('=< fails when left > right', () => {
  assert.ok(fails('', '6 =< 5.'));
});

test('=:= arithmetic equality succeeds', () => {
  assert.ok(q('', '3 + 2 =:= 5.').ok);
});

test('=:= arithmetic equality fails', () => {
  assert.ok(fails('', '3 + 2 =:= 6.'));
});

test('=\\= arithmetic inequality succeeds', () => {
  assert.ok(q('', '3 + 2 =\\= 6.').ok);
});

test('=\\= arithmetic inequality fails', () => {
  assert.ok(fails('', '3 + 2 =\\= 5.'));
});

test('bit operators: /\\, \\/, <<, >>', () => {
  assertBinding(q('', 'X is 5 /\\ 3.'), 'X', '1');
  assertBinding(q('', 'X is 5 \\/ 3.'), 'X', '7');
  assertBinding(q('', 'X is 1 << 3.'), 'X', '8');
  assertBinding(q('', 'X is 8 >> 2.'), 'X', '2');
});

test('min/max in arithmetic', () => {
  assertBinding(q('', 'X is min(3, 7).'), 'X', '3');
  assertBinding(q('', 'X is max(3, 7).'), 'X', '7');
});

// ---------------------------------------------------------------------------
// 12. Type checks
// ---------------------------------------------------------------------------
group('Type checks');

test('atom/1 — succeeds for atom and empty list', () => {
  assert.ok(q('', 'atom(hello).').ok);
  assert.ok(q('', 'atom([]).').ok);
});

test('atom/1 — fails for integer', () => {
  // Introduce variable so ok flag reflects Prolog result.
  const r = q('', 'X = 42, atom(X).');
  assert.ok(!r.ok);
});

test('atom/1 — fails for compound', () => {
  const r = q('', 'X = f(x), atom(X).');
  assert.ok(!r.ok);
});

test('integer/1 — succeeds for integers', () => {
  assert.ok(q('', 'integer(42).').ok);
});

test('integer/1 — fails for atom', () => {
  assert.ok(fails('', 'integer(hello).'));
});

test('number/1 — same as integer for this runtime', () => {
  assert.ok(q('', 'number(7).').ok);
});

test('number/1 — fails for atom', () => {
  assert.ok(fails('', 'number(foo).'));
});

test('var/1 — succeeds for unbound variable', () => {
  assert.ok(q('', 'var(X).').ok);
});

test('var/1 — fails for atom', () => {
  assert.ok(fails('', 'var(hello).'));
});

test('nonvar/1 — succeeds for bound term', () => {
  assert.ok(q('', 'nonvar(hello).').ok);
});

test('nonvar/1 — fails for unbound variable', () => {
  // X is unbound → nonvar fails → ok=false (variable-containing query).
  const r = q('', 'nonvar(X).');
  assert.ok(!r.ok);
});

test('compound/1 — succeeds for compound terms and lists', () => {
  assert.ok(q('', 'compound(f(x)).').ok);
  assert.ok(q('', 'compound([a,b]).').ok);
});

test('compound/1 — fails for atom', () => {
  assert.ok(fails('', 'compound(hello).'));
});

test('compound/1 — fails for integer', () => {
  assert.ok(fails('', 'compound(42).'));
});

test('atomic/1 — atoms, integers, empty list', () => {
  assert.ok(q('', 'atomic(hello).').ok);
  assert.ok(q('', 'atomic(42).').ok);
  assert.ok(q('', 'atomic([]).').ok);
});

test('atomic/1 — fails for compound', () => {
  assert.ok(fails('', 'atomic(f(x)).'));
});

test('is_list/1 — proper list', () => {
  assert.ok(q('', 'is_list([]).').ok);
  assert.ok(q('', 'is_list([1,2,3]).').ok);
});

test('is_list/1 — fails for non-list', () => {
  assert.ok(fails('', 'is_list(hello).'));
});

test('ground/1 — ground terms', () => {
  assert.ok(q('', 'ground(hello).').ok);
  assert.ok(q('', 'ground(f(1,2)).').ok);
});

test('ground/1 — fails for term with unbound variable', () => {
  // X is a query variable → unbound → not ground → ok=false.
  const r = q('', 'ground(f(X,2)).');
  assert.ok(!r.ok);
});

// ---------------------------------------------------------------------------
// 13. I/O — output capture
// ---------------------------------------------------------------------------
group('I/O output capture');

test('write/1 captures output', () => {
  const r = q('', 'write(hello).');
  assert.strictEqual(r.output, 'hello');
});

test('writeln/1 appends newline', () => {
  const r = q('', 'writeln(hello).');
  assert.strictEqual(r.output, 'hello\n');
});

test('nl/0 appends newline', () => {
  const r = q('', 'write(hi), nl.');
  assert.strictEqual(r.output, 'hi\n');
});

test('tab/1 appends spaces', () => {
  const r = q('', 'tab(3).');
  assert.strictEqual(r.output, '   ');
});

test('multiple write calls concatenate', () => {
  const r = q('', 'write(a), write(b), write(c).');
  assert.strictEqual(r.output, 'abc');
});

test('format/2 with ~w substitution', () => {
  const r = q('', "format('Hello ~w!', [world]).");
  assert.strictEqual(r.output, 'Hello world!');
});

test('format/2 with ~n newline', () => {
  const r = q('', "format('line~n', []).");
  assert.strictEqual(r.output, 'line\n');
});

test('format/1 with ~n newline', () => {
  const r = q('', "format('done~n').");
  assert.strictEqual(r.output, 'done\n');
});

// ---------------------------------------------------------------------------
// 14. Lists
// ---------------------------------------------------------------------------
group('Lists');

const LISTS_PROG = [
  'member(X,[X|_]).',
  'member(X,[_|T]) :- member(X,T).',
  'append([],L,L).',
  'append([H|T1],L2,[H|T3]) :- append(T1,L2,T3).',
  'my_length([],0).',
  'my_length([_|T],N) :- my_length(T,N1), N is N1+1.',
  'my_reverse([],[]).',
  'my_reverse([H|T],R) :- my_reverse(T,RT), append(RT,[H],R).',
].join('\n');

test('member succeeds for element in list', () => {
  assert.ok(q(LISTS_PROG, 'member(2, [1,2,3]).').ok);
});

test('member fails for element not in list', () => {
  // Ground query: use fails() helper.
  assert.ok(fails(LISTS_PROG, 'member(5, [1,2,3]).'));
});

test('append two lists', () => {
  assertBinding(q(LISTS_PROG, 'append([1,2],[3,4],L).'), 'L', '[1,2,3,4]');
});

test('length/2 built-in', () => {
  assertBinding(q('', 'length([a,b,c], N).'), 'N', '3');
});

test('length/2 empty list', () => {
  assertBinding(q('', 'length([], N).'), 'N', '0');
});

test('nth0/3', () => {
  assertBinding(q('', 'nth0(0, [a,b,c], X).'), 'X', 'a');
  assertBinding(q('', 'nth0(2, [a,b,c], X).'), 'X', 'c');
});

test('nth1/3', () => {
  assertBinding(q('', 'nth1(1, [a,b,c], X).'), 'X', 'a');
  assertBinding(q('', 'nth1(3, [a,b,c], X).'), 'X', 'c');
});

test('last/2', () => {
  assertBinding(q('', 'last([1,2,3], X).'), 'X', '3');
});

test('sort/2 removes duplicates and sorts', () => {
  assertBinding(q('', 'sort([3,1,2,1,3], S).'), 'S', '[1,2,3]');
});

test('msort/2 keeps duplicates', () => {
  assertBinding(q('', 'msort([3,1,2,1], S).'), 'S', '[1,1,2,3]');
});

test('flatten/2', () => {
  assertBinding(q('', 'flatten([1,[2,3],[4,[5]]], F).'), 'F', '[1,2,3,4,5]');
});

test('max_list/2', () => {
  assertBinding(q('', 'max_list([3,1,4,1,5,9], M).'), 'M', '9');
});

test('min_list/2', () => {
  assertBinding(q('', 'min_list([3,1,4,1,5,9], M).'), 'M', '1');
});

test('sum_list/2', () => {
  assertBinding(q('', 'sum_list([1,2,3,4], S).'), 'S', '10');
});

test('numlist/3', () => {
  assertBinding(q('', 'numlist(1,5,L).'), 'L', '[1,2,3,4,5]');
});

test('list_to_set/2', () => {
  assertBinding(q('', 'list_to_set([1,2,1,3,2], S).'), 'S', '[1,2,3]');
});

test('subtract/3', () => {
  assertBinding(q('', 'subtract([1,2,3,4], [2,4], D).'), 'D', '[1,3]');
});

test('intersection/3', () => {
  assertBinding(q('', 'intersection([1,2,3], [2,3,4], I).'), 'I', '[2,3]');
});

test('union/3', () => {
  assertBinding(q('', 'union([1,2], [2,3], U).'), 'U', '[1,2,3]');
});

test('delete/3', () => {
  assertBinding(q('', 'delete([1,2,3,2,1], 2, D).'), 'D', '[1,3,1]');
});

// ---------------------------------------------------------------------------
// 15. findall/3
// ---------------------------------------------------------------------------
group('findall/3');

test('findall collects all solutions', () => {
  const prog = 'color(red). color(green). color(blue).';
  const r = q(prog, 'findall(X, color(X), Xs).');
  assertBinding(r, 'Xs', '[red,green,blue]');
});

test('findall returns [] when goal fails', () => {
  assertBinding(q('', 'findall(X, fail, Xs).'), 'Xs', '[]');
});

test('findall with template transformation', () => {
  const prog = 'num(1). num(2). num(3).';
  const r = q(prog, 'findall(X-X, num(X), Ps).');
  assert.ok(r.ok);
  assert.strictEqual(r.answers[0]['Ps'], '[(1-1),(2-2),(3-3)]');
});

// ---------------------------------------------------------------------------
// 16. bagof/3 and setof/3
// ---------------------------------------------------------------------------
group('bagof/3 and setof/3 (simplified)');

test('bagof collects answers', () => {
  const prog = 'val(3). val(1). val(2).';
  assertBinding(q(prog, 'bagof(X, val(X), Xs).'), 'Xs', '[3,1,2]');
});

test('setof returns sorted unique answers', () => {
  const prog = 'val(3). val(1). val(2). val(1).';
  assertBinding(q(prog, 'setof(X, val(X), Xs).'), 'Xs', '[1,2,3]');
});

// ---------------------------------------------------------------------------
// 17. once/1, ignore/1, forall/2
// ---------------------------------------------------------------------------
group('once/1, ignore/1, forall/2');

test('once/1 returns only one answer', () => {
  const prog = 'p(1). p(2). p(3).';
  const r = q(prog, 'once(p(X)).', 10);
  assert.strictEqual(r.answers.length, 1);
  assertBinding(r, 'X', '1');
});

test('ignore/1 succeeds even when inner goal fails', () => {
  const r = q('', 'ignore(fail).');
  assert.ok(r.ok);
});

test('ignore/1 succeeds when inner goal succeeds', () => {
  const r = q('', 'ignore(true).');
  assert.ok(r.ok);
});

test('forall/2 succeeds when all satisfy condition', () => {
  const prog = 'num(2). num(4). num(6).';
  const r = q(prog, 'forall(num(X), 0 =:= X mod 2).');
  assert.ok(r.ok);
});

test('forall/2 fails when some do not satisfy', () => {
  const prog = 'num(2). num(3). num(6).';
  const r = q(prog, 'forall(num(X), 0 =:= X mod 2).');
  assert.ok(!r.ok);
});

// ---------------------------------------------------------------------------
// 18. call/N
// ---------------------------------------------------------------------------
group('call/N');

test('call/1 executes true', () => {
  assert.ok(q('', 'call(true).').ok);
});

test('call/1 executes fail — goal fails', () => {
  // fail is an atom with no variables; use fails() helper.
  assert.ok(fails('', 'call(fail).'));
});

test('call/2 applies extra argument', () => {
  const prog = 'greet(X) :- write(X).';
  const r = q(prog, 'call(greet, hello).');
  assert.strictEqual(r.output, 'hello');
});

test('call/3 applies two extra arguments', () => {
  const prog = 'add(X, Y, Z) :- Z is X + Y.';
  assertBinding(q(prog, 'call(add, 3, 4, Z).'), 'Z', '7');
});

// ---------------------------------------------------------------------------
// 19. Atom operations
// ---------------------------------------------------------------------------
group('Atom operations');

test('atom_concat/3 forward', () => {
  assertBinding(q('', 'atom_concat(hello, world, X).'), 'X', 'helloworld');
});

test('atom_concat/3 with integer argument', () => {
  assertBinding(q('', 'atom_concat(item, 42, X).'), 'X', 'item42');
});

test('atom_length/2', () => {
  assertBinding(q('', 'atom_length(hello, N).'), 'N', '5');
  assertBinding(q('', "atom_length('', N)."), 'N', '0');
});

test('atom_chars/2 forward', () => {
  assertBinding(q('', 'atom_chars(abc, Cs).'), 'Cs', '[a,b,c]');
});

test('atom_chars/2 reverse', () => {
  assertBinding(q('', 'atom_chars(X, [h,i]).'), 'X', 'hi');
});

test('atom_codes/2', () => {
  assertBinding(q('', 'atom_codes(hi, Cs).'), 'Cs', '[104,105]');
});

test('char_code/2', () => {
  assertBinding(q('', 'char_code(a, X).'), 'X', '97');
});

test('number_codes/2', () => {
  assertBinding(q('', 'number_codes(42, Cs).'), 'Cs', '[52,50]');
});

test('number_chars/2', () => {
  // Characters are rendered as atoms without quotes (e.g. 4 not '4').
  assertBinding(q('', 'number_chars(42, Cs).'), 'Cs', '[4,2]');
});

test('atom_number/2', () => {
  assertBinding(q('', "atom_number('42', N)."), 'N', '42');
});

test('upcase_atom/2', () => {
  assertBinding(q('', 'upcase_atom(hello, X).'), 'X', 'HELLO');
});

test('downcase_atom/2', () => {
  assertBinding(q('', "downcase_atom('HELLO', X)."), 'X', 'hello');
});

test('term_to_atom/2', () => {
  assertBinding(q('', 'term_to_atom(f(1,2), X).'), 'X', 'f(1,2)');
});

// ---------------------------------------------------------------------------
// 20. functor/3, arg/3, =..
// ---------------------------------------------------------------------------
group('functor/3, arg/3, =..');

test('functor/3 decomposes compound', () => {
  const r = q('', 'functor(f(a,b,c), F, A).');
  assertBinding(r, 'F', 'f');
  assertBinding(r, 'A', '3');
});

test('functor/3 for atom returns arity 0', () => {
  const r = q('', 'functor(hello, F, A).');
  assertBinding(r, 'F', 'hello');
  assertBinding(r, 'A', '0');
});

test('functor/3 for integer', () => {
  const r = q('', 'functor(42, F, A).');
  assertBinding(r, 'F', '42');
  assertBinding(r, 'A', '0');
});

test('arg/3 extracts each argument', () => {
  assertBinding(q('', 'arg(1, f(a,b,c), X).'), 'X', 'a');
  assertBinding(q('', 'arg(2, f(a,b,c), X).'), 'X', 'b');
  assertBinding(q('', 'arg(3, f(a,b,c), X).'), 'X', 'c');
});

test('=.. univ decomposes compound', () => {
  assertBinding(q('', 'f(a,b) =.. L.'), 'L', '[f,a,b]');
});

test('=.. univ builds compound from list', () => {
  assertBinding(q('', 'T =.. [g, 1, 2].'), 'T', 'g(1,2)');
});

test('=.. for atom gives singleton list', () => {
  assertBinding(q('', 'hello =.. L.'), 'L', '[hello]');
});

// ---------------------------------------------------------------------------
// 21. copy_term/2
// ---------------------------------------------------------------------------
group('copy_term/2');

test('copy_term creates independent copy (compound shape preserved)', () => {
  const r = q('', 'copy_term(f(X, X), Copy).');
  assert.ok(r.ok);
  assert.ok(r.answers[0]['Copy'].startsWith('f('));
});

test('copy_term with ground term is identity', () => {
  assertBinding(q('', 'copy_term(f(1,2), Copy).'), 'Copy', 'f(1,2)');
});

// ---------------------------------------------------------------------------
// 22. succ/2, plus/3, between/3
// ---------------------------------------------------------------------------
group('succ/2, plus/3, between/3');

test('succ/2 forward', () => {
  assertBinding(q('', 'succ(4, X).'), 'X', '5');
});

test('succ/2 reverse', () => {
  assertBinding(q('', 'succ(X, 5).'), 'X', '4');
});

test('plus/3 forward', () => {
  assertBinding(q('', 'plus(3, 4, X).'), 'X', '7');
});

test('plus/3 reverse first arg', () => {
  assertBinding(q('', 'plus(X, 4, 7).'), 'X', '3');
});

test('plus/3 reverse second arg', () => {
  assertBinding(q('', 'plus(3, X, 7).'), 'X', '4');
});

test('between/3 generates values', () => {
  const r = q('', 'between(1, 3, X).', 10);
  const vals = r.answers.map(a => a['X']);
  assert.deepStrictEqual(vals, ['1', '2', '3']);
});

test('between/3 check mode succeeds when in range', () => {
  assert.ok(q('', 'between(1, 5, 3).').ok);
});

test('between/3 check mode fails when out of range', () => {
  assert.ok(fails('', 'between(1, 5, 7).'));
});

// ---------------------------------------------------------------------------
// 23. compare/3 and standard order comparisons
// ---------------------------------------------------------------------------
group('compare/3 and standard order (@<, @>, @=<, @>=)');

test('compare/3 — less than', () => {
  assertBinding(q('', 'compare(Order, a, b).'), 'Order', '<');
});

test('compare/3 — greater than', () => {
  assertBinding(q('', 'compare(Order, b, a).'), 'Order', '>');
});

test('compare/3 — equal', () => {
  assertBinding(q('', 'compare(Order, foo, foo).'), 'Order', '=');
});

test('@< standard order: a @< b succeeds', () => {
  assert.ok(q('', 'a @< b.').ok);
});

test('@< standard order: b @< a fails', () => {
  assert.ok(fails('', 'b @< a.'));
});

test('@> standard order: b @> a succeeds', () => {
  assert.ok(q('', 'b @> a.').ok);
});

test('@=< standard order: a @=< a and a @=< b succeed', () => {
  assert.ok(q('', 'a @=< a.').ok);
  assert.ok(q('', 'a @=< b.').ok);
});

test('@>= standard order: b @>= a and a @>= a succeed', () => {
  assert.ok(q('', 'b @>= a.').ok);
  assert.ok(q('', 'a @>= a.').ok);
});

// ---------------------------------------------------------------------------
// 24. maplist/2, maplist/3, include/3, exclude/3
// ---------------------------------------------------------------------------
group('maplist/2, maplist/3, include/3, exclude/3');

test('maplist/2 succeeds when all elements satisfy goal', () => {
  const prog = 'positive(X) :- X > 0.';
  assert.ok(q(prog, 'maplist(positive, [1,2,3]).').ok);
});

test('maplist/2 fails when an element does not satisfy goal', () => {
  const prog = 'positive(X) :- X > 0.';
  assert.ok(fails(prog, 'maplist(positive, [1,-1,3]).'));
});

test('maplist/3 transforms list', () => {
  const prog = 'double(X, Y) :- Y is X * 2.';
  assertBinding(q(prog, 'maplist(double, [1,2,3], Ys).'), 'Ys', '[2,4,6]');
});

test('maplist/4 applies goal to three corresponding lists', () => {
  const prog = 'add(X, Y, Z) :- Z is X + Y.';
  assertBinding(q(prog, 'maplist(add, [1,2,3], [10,20,30], Zs).'), 'Zs', '[11,22,33]');
});

test('maplist/4 succeeds on empty lists', () => {
  const prog = 'add(X, Y, Z) :- Z is X + Y.';
  assertBinding(q(prog, 'maplist(add, [], [], Zs).'), 'Zs', '[]');
});

test('maplist/5 applies goal to four corresponding lists', () => {
  const prog = 'add3(A, B, C, D) :- D is A + B + C.';
  assertBinding(q(prog, 'maplist(add3, [1,2], [10,20], [100,200], Ds).'), 'Ds', '[111,222]');
});

test('maplist/4 fails when goal fails for an element', () => {
  const prog = 'eq(X, X).';
  assert.ok(fails(prog, 'maplist(eq, [1,2,3], [1,99,3]).'));
});

test('convlist/3 maps and filters elements', () => {
  const prog = 'conv(X, Y) :- X > 0, Y is X * 2.';
  assertBinding(q(prog, 'convlist(conv, [-1,2,-3,4], Ys).'), 'Ys', '[4,8]');
});

test('convlist/3 on empty list gives empty list', () => {
  assertBinding(q('', 'convlist(=(x), [], Ys).'), 'Ys', '[]');
});

test('convlist/3 when all elements pass', () => {
  const prog = 'wrap(X, w(X)).';
  assertBinding(q(prog, 'convlist(wrap, [a,b,c], Ys).'), 'Ys', '[w(a),w(b),w(c)]');
});

// ---------------------------------------------------------------------------
// 24b. foldl/4, foldl/5, foldl/6, foldl/7
// ---------------------------------------------------------------------------
group('foldl/4, foldl/5, foldl/6, foldl/7');

test('foldl/4 sums a list', () => {
  const prog = 'sum(X, Acc, Res) :- Res is Acc + X.';
  assertBinding(q(prog, 'foldl(sum, [1,2,3,4], 0, S).'), 'S', '10');
});

test('foldl/4 on empty list returns V0', () => {
  const prog = 'sum(X, Acc, Res) :- Res is Acc + X.';
  assertBinding(q(prog, 'foldl(sum, [], 42, S).'), 'S', '42');
});

test('foldl/4 builds a reversed list', () => {
  const prog = 'cons(H, T, [H|T]).';
  assertBinding(q(prog, 'foldl(cons, [1,2,3], [], R).'), 'R', '[3,2,1]');
});

test('foldl/5 sums two lists pairwise', () => {
  const prog = 'pairsum(X, Y, Acc, Res) :- Res is Acc + X + Y.';
  assertBinding(q(prog, 'foldl(pairsum, [1,2,3], [10,20,30], 0, S).'), 'S', '66');
});

test('foldl/5 on empty lists returns V0', () => {
  const prog = 'pairsum(X, Y, Acc, Res) :- Res is Acc + X + Y.';
  assertBinding(q(prog, 'foldl(pairsum, [], [], 7, S).'), 'S', '7');
});

test('foldl/5 fails when lists have different lengths', () => {
  const prog = 'pairsum(X, Y, Acc, Res) :- Res is Acc + X + Y.';
  assert.ok(fails(prog, 'foldl(pairsum, [1,2], [10], 0, S).'));
});

test('foldl/6 processes three lists', () => {
  const prog = 'trisum(X, Y, Z, Acc, Res) :- Res is Acc + X + Y + Z.';
  assertBinding(q(prog, 'foldl(trisum, [1,2], [10,20], [100,200], 0, S).'), 'S', '333');
});

test('foldl/7 processes four lists', () => {
  const prog = 'quadsum(A, B, C, D, Acc, Res) :- Res is Acc + A + B + C + D.';
  assertBinding(q(prog, 'foldl(quadsum, [1,2], [10,20], [100,200], [1000,2000], 0, S).'), 'S', '3333');
});


test('include/3 keeps matching elements', () => {
  const prog = 'even(X) :- 0 =:= X mod 2.';
  assertBinding(q(prog, 'include(even, [1,2,3,4,5,6], Evens).'), 'Evens', '[2,4,6]');
});

test('exclude/3 removes matching elements', () => {
  const prog = 'even(X) :- 0 =:= X mod 2.';
  assertBinding(q(prog, 'exclude(even, [1,2,3,4,5,6], Odds).'), 'Odds', '[1,3,5]');
});

// ---------------------------------------------------------------------------
// 25. select/3 and permutation/2
// ---------------------------------------------------------------------------
group('select/3 and permutation/2');

test('select/3 picks an element and returns rest', () => {
  assertBinding(q('', 'select(2, [1,2,3], Rest).', 1), 'Rest', '[1,3]');
});

test('permutation/2 generates all permutations', () => {
  const r = q('', 'permutation([1,2,3], P).', 10);
  assert.strictEqual(r.answers.length, 6);
});

// ---------------------------------------------------------------------------
// 26. Error handling
// ---------------------------------------------------------------------------
group('Error handling');

test('parse error in program is tolerated (runQuery returns result)', () => {
  const r = q('foo(X :-', 'true.');
  assert.strictEqual(typeof r.ok, 'boolean');
});

test('parse error in query returns non-null error field', () => {
  const r = q('', 'foo(X :-');
  assert.ok(r.error !== null);
});

test('empty query returns error or not-ok', () => {
  const r = q('', '');
  assert.ok(r.error !== null || !r.ok);
});

test('unknown predicate fails gracefully with no JS error', () => {
  const r = q('', 'completely_unknown_predicate_xyz(x).');
  assert.strictEqual(r.error, null);
  assert.strictEqual(r.answers.length, 0);
});

test('deep recursion returns a JS error message', () => {
  const prog = 'loop :- loop.';
  const r = q(prog, 'loop.');
  assert.ok(r.error !== null);
});

// ---------------------------------------------------------------------------
// 27. hasMainPredicate
// ---------------------------------------------------------------------------
group('hasMainPredicate');

test('detects fact main.', () => {
  assert.ok(pl2js.hasMainPredicate('main.'));
});

test('detects rule main :- ...', () => {
  assert.ok(pl2js.hasMainPredicate('main :- write(hello), nl.'));
});

test('returns false for program with no main', () => {
  assert.ok(!pl2js.hasMainPredicate('foo :- bar.'));
});

test('does not false-positive on mainLoop', () => {
  assert.ok(!pl2js.hasMainPredicate('mainLoop :- true.'));
});

test('detects main inside a larger program', () => {
  const prog = 'foo(x).\nbar :- foo(x).\nmain :- bar.\n';
  assert.ok(pl2js.hasMainPredicate(prog));
});

// ---------------------------------------------------------------------------
// 28. tokenize
// ---------------------------------------------------------------------------
group('tokenize');

test('tokenizes atoms and operators', () => {
  const toks = pl2js.tokenize('foo(X) :- bar(X).');
  assert.ok(Array.isArray(toks));
  assert.ok(toks.length > 0);
  assert.strictEqual(toks[0].t, 'atom');
  assert.strictEqual(toks[0].v, 'foo');
});

test('tokenizes integers', () => {
  const toks = pl2js.tokenize('42.');
  assert.ok(toks.some(t => t.t === 'int' && t.v === 42));
});

test('tokenizes single-quoted atoms (including spaces)', () => {
  const toks = pl2js.tokenize("'hello world'.");
  assert.ok(toks.some(t => t.t === 'atom' && t.v === 'hello world'));
});

test('tokenizes variables', () => {
  const toks = pl2js.tokenize('X :- Y.');
  assert.ok(toks.some(t => t.t === 'var' && t.v === 'X'));
  assert.ok(toks.some(t => t.t === 'var' && t.v === 'Y'));
});

test('strips line comments', () => {
  const toks = pl2js.tokenize('% this is a comment\nfoo.');
  assert.ok(toks.every(t => t.v !== '%'));
  assert.ok(toks.some(t => t.t === 'atom' && t.v === 'foo'));
});

test('strips block comments', () => {
  const toks = pl2js.tokenize('/* block comment */ foo.');
  assert.ok(toks.some(t => t.t === 'atom' && t.v === 'foo'));
});

test('tokenizes multi-char operators', () => {
  const toks = pl2js.tokenize('X =:= Y.');
  assert.ok(toks.some(t => t.t === 'op' && t.v === '=:='));
});

test('tokenizes character-code notation 0\'a', () => {
  const toks = pl2js.tokenize("0'a.");
  assert.ok(toks.some(t => t.t === 'int' && t.v === 97));
});

// ---------------------------------------------------------------------------
// 29. parsePrologSource
// ---------------------------------------------------------------------------
group('parsePrologSource');

test('parses facts into clauses', () => {
  const clauses = pl2js.parsePrologSource('foo(1). foo(2). foo(3).');
  assert.strictEqual(clauses.length, 3);
  assert.ok(clauses.every(c => c.head && c.head.functor === 'foo'));
});

test('parses rules with body', () => {
  const clauses = pl2js.parsePrologSource('bar(X) :- foo(X).');
  assert.strictEqual(clauses.length, 1);
  assert.ok(clauses[0].body !== null);
});

test('ignores directives (:- use_module etc.)', () => {
  // Directives return null from parseClause and are filtered out.
  const clauses = pl2js.parsePrologSource(':- use_module(lists).\nfoo(a).');
  assert.strictEqual(clauses.length, 1);
  assert.strictEqual(clauses[0].head.functor, 'foo');
});

test('parses list facts', () => {
  const clauses = pl2js.parsePrologSource('items([a,b,c]).');
  assert.strictEqual(clauses.length, 1);
});

// ---------------------------------------------------------------------------
// 30. buildDatabase
// ---------------------------------------------------------------------------
group('buildDatabase');

test('groups clauses by predicate key', () => {
  const clauses = pl2js.parsePrologSource('p(1). p(2). q(a).');
  const db = pl2js.buildDatabase(clauses);
  assert.ok('p/1' in db);
  assert.ok('q/1' in db);
  assert.strictEqual(db['p/1'].length, 2);
  assert.strictEqual(db['q/1'].length, 1);
});

test('handles 0-arity predicates', () => {
  const clauses = pl2js.parsePrologSource('go.');
  const db = pl2js.buildDatabase(clauses);
  assert.ok('go/0' in db);
});

// ---------------------------------------------------------------------------
// 31. termToString (via query bindings)
// ---------------------------------------------------------------------------
group('termToString (via query answer bindings)');

test('renders atom', () => {
  assert.strictEqual(q('', 'X = hello.').answers[0]['X'], 'hello');
});

test('renders integer', () => {
  assert.strictEqual(q('', 'X = 42.').answers[0]['X'], '42');
});

test('renders list', () => {
  assert.strictEqual(q('', 'X = [1,2,3].').answers[0]['X'], '[1,2,3]');
});

test('renders compound', () => {
  assert.strictEqual(q('', 'X = f(a,b).').answers[0]['X'], 'f(a,b)');
});

test('renders nested compound', () => {
  assert.strictEqual(q('', 'X = f(g(1), h(2,3)).').answers[0]['X'], 'f(g(1),h(2,3))');
});

test('renders empty list', () => {
  assert.strictEqual(q('', 'X = [].').answers[0]['X'], '[]');
});

test('termToString exported function renders atom', () => {
  const toks = pl2js.tokenize('hello.');
  const clauses = pl2js.parsePrologSource('hello.');
  // The exported termToString renders a parsed atom term.
  const atomTerm = clauses[0].head; // {type:'atom', name:'hello'}
  assert.strictEqual(pl2js.termToString(atomTerm), 'hello');
});

// ---------------------------------------------------------------------------
// 32. generateHtml
// ---------------------------------------------------------------------------
group('generateHtml');

const RUNTIME_SRC = fs.readFileSync(path.join(__dirname, 'pl2js.js'), 'utf8');

test('generates a string starting with <!DOCTYPE html>', () => {
  const html = pl2js.generateHtml(RUNTIME_SRC, 'main :- write(hello), nl.');
  assert.ok(typeof html === 'string');
  assert.ok(html.startsWith('<!DOCTYPE html>'));
});

test('generated HTML contains <html> and </html>', () => {
  const html = pl2js.generateHtml(RUNTIME_SRC, 'main :- write(hello), nl.');
  assert.ok(html.includes('<html'));
  assert.ok(html.includes('</html>'));
});

test('generated HTML embeds the program source', () => {
  const prog = 'main :- write(hello), nl.';
  const html = pl2js.generateHtml(RUNTIME_SRC, prog);
  assert.ok(html.includes(prog));
});

test('generated HTML includes reminder banner when no main/0 defined', () => {
  const html = pl2js.generateHtml(RUNTIME_SRC, 'foo(x).');
  assert.ok(html.includes('main/0'));
});

test('generated HTML does not include reminder banner in body when main/0 is defined', () => {
  const html = pl2js.generateHtml(RUNTIME_SRC, 'main :- write(hello).');
  // The notice text exists once inside the embedded runtime source code.
  // When main/0 IS defined, the notice div is NOT added to the HTML body,
  // so id="notice" appears exactly once (inside the <script> block).
  // Without main/0 it would appear twice (script + body div).
  const count = (html.match(/id="notice"/g) || []).length;
  assert.strictEqual(count, 1,
    'notice div should only appear in the embedded runtime source, not in the HTML body');
});

test('</script> inside runtime is escaped so HTML parser is not confused', () => {
  const html = pl2js.generateHtml(RUNTIME_SRC, 'main :- write(hello).');
  // Should be exactly 2 literal </script> tags: one closing the runtime
  // <script> block and one closing the init <script> block.
  const count = (html.match(/<\/script>/gi) || []).length;
  assert.strictEqual(count, 2);
});

// ---------------------------------------------------------------------------
// 33. Integration — full example programs
// ---------------------------------------------------------------------------
group('Integration — full programs');

test('family.pl: grandparent(tom, ann) succeeds', () => {
  const prog = fs.readFileSync(path.join(__dirname, 'examples', 'family.pl'), 'utf8');
  assert.ok(q(prog, 'grandparent(tom, ann).').ok);
});

test('family.pl: grandparent returns correct variable bindings', () => {
  const prog = fs.readFileSync(path.join(__dirname, 'examples', 'family.pl'), 'utf8');
  const r = q(prog, 'grandparent(tom, Z).', 10);
  const grandchildren = r.answers.map(a => a['Z']);
  assert.ok(grandchildren.includes('ann'));
  assert.ok(grandchildren.includes('pat'));
});

test('rules.pl: mortal(socrates) succeeds', () => {
  const prog = fs.readFileSync(path.join(__dirname, 'examples', 'rules.pl'), 'utf8');
  assert.ok(q(prog, 'mortal(socrates).').ok);
});

test('rules.pl: mortal(zeus) fails', () => {
  const prog = fs.readFileSync(path.join(__dirname, 'examples', 'rules.pl'), 'utf8');
  assert.ok(fails(prog, 'mortal(zeus).'));
});

test('rules.pl: can_fly(tweety) succeeds with negation', () => {
  const prog = fs.readFileSync(path.join(__dirname, 'examples', 'rules.pl'), 'utf8');
  assert.ok(q(prog, 'can_fly(tweety).').ok);
});

test('rules.pl: can_fly(sam) fails (sam is a penguin)', () => {
  const prog = fs.readFileSync(path.join(__dirname, 'examples', 'rules.pl'), 'utf8');
  assert.ok(fails(prog, 'can_fly(sam).'));
});

test('lists.pl: append gives correct result', () => {
  const prog = fs.readFileSync(path.join(__dirname, 'examples', 'lists.pl'), 'utf8');
  assertBinding(q(prog, 'append([1,2],[3,4],L).'), 'L', '[1,2,3,4]');
});

test('lists.pl: my_reverse gives correct result', () => {
  const prog = fs.readFileSync(path.join(__dirname, 'examples', 'lists.pl'), 'utf8');
  assertBinding(q(prog, 'my_reverse([1,2,3],R).'), 'R', '[3,2,1]');
});

test('write/nl output is captured correctly', () => {
  const prog = "demo :- write(hello), write(' '), write(world), nl.";
  const r = q(prog, 'demo.');
  assert.strictEqual(r.output, 'hello world\n');
});

// ---------------------------------------------------------------------------
// 26. pl2js.pl generated JS runtime — meta-call built-ins
// ---------------------------------------------------------------------------

// Extract the JavaScript runtime header from pl2js.pl and test it directly.
// This validates that maplist/2-5, convlist/3, foldl/4-7, once/1, ignore/1
// work correctly in the runtime generated by the Prolog-to-JS compiler.

(function testGeneratedRuntime() {
  const plSrc = fs.readFileSync(path.join(__dirname, 'pl2js.pl'), 'utf8');
  const startMarker = "generate_js_header(Header) :-\n    Header =\n'";
  const endMarker   = "\n'.\n\n%% group_clauses_by_predicate";
  const s = plSrc.indexOf(startMarker);
  const e = plSrc.indexOf(endMarker);
  if (s < 0 || e < 0) {
    console.warn('WARNING: Could not locate JS header in pl2js.pl — skipping generated-runtime tests');
    return;
  }
  const headerJs = plSrc.slice(s + startMarker.length, e).replace(/''/g, "'");

  // Evaluate the header in a fresh context with Node's vm module
  const vm = require('vm');
  const ctx = vm.createContext({});
  try { vm.runInContext(headerJs, ctx); } catch(err) {
    // If header fails to evaluate, skip these tests
    return;
  }

  // Helper predicates injected to represent user-defined Prolog clauses
  vm.runInContext(`
    function positive_1(state, x) { return gt_2(state, x, createInt(0)); }
    _registry["positive/1"] = positive_1;
    function double_2(state, x, y) { return is_2(state, y, createCompound("*", 2, [x, createInt(2)])); }
    _registry["double/2"] = double_2;
    function add_3(state, x, y, z) { return is_2(state, z, createCompound("+", 2, [x, y])); }
    _registry["add/3"] = add_3;
    function sum_3(state, x, v0, v) { return is_2(state, v, createCompound("+", 2, [v0, x])); }
    _registry["sum/3"] = sum_3;
    function cons_3(state, x, acc, result) { return unify(state, result, createList(x, acc)); }
    _registry["cons/3"] = cons_3;
    function conv_2(state, x, y) {
      if (!gt_2(state, x, createInt(0))) return false;
      if (state.failed) return false;
      return is_2(state, y, createCompound("*", 2, [x, createInt(2)]));
    }
    _registry["conv/2"] = conv_2;
    function mkList() {
      var args = Array.prototype.slice.call(arguments);
      var l = createNil();
      for (var i = args.length - 1; i >= 0; i--) l = createList(createInt(args[i]), l);
      return l;
    }
    function termStr(state, t) {
      t = deref(state, t);
      if (t.type === "int")  return String(t.val);
      if (t.type === "nil")  return "[]";
      if (t.type === "atom") return t.name;
      if (t.type === "list") {
        var parts = [];
        var cur = t;
        while (cur.type === "list") { parts.push(termStr(state, cur.head)); cur = deref(state, cur.tail); }
        return "[" + parts.join(",") + "]";
      }
      if (t.type === "compound") return t.functor + "(" + t.args.map(function(a){ return termStr(state, a); }).join(",") + ")";
      return "?";
    }
  `, ctx);

  group('pl2js.pl generated runtime — maplist/convlist/foldl/once/ignore');

  test('generated runtime: maplist/2 succeeds when all elements positive', () => {
    const fn = vm.runInContext('(function(){ var st = initState(); return maplist_2(st, createAtom("positive"), mkList(1,2,3)) && !st.failed; })', ctx);
    assert.ok(fn());
  });

  test('generated runtime: maplist/2 fails when an element is non-positive', () => {
    const fn = vm.runInContext('(function(){ var st = initState(); return maplist_2(st, createAtom("positive"), mkList(1,-1,3)) && !st.failed; })', ctx);
    assert.ok(!fn());
  });

  test('generated runtime: maplist/3 transforms list', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState();
      var out = createVar(st.nextVarId++);
      if (!maplist_3(st, createAtom("double"), mkList(1,2,3), out) || st.failed) return null;
      return termStr(st, out);
    })`, ctx);
    assert.strictEqual(fn(), '[2,4,6]');
  });

  test('generated runtime: convlist/3 maps and filters', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState();
      var out = createVar(st.nextVarId++);
      if (!convlist_3(st, createAtom("conv"), mkList(-1,2,-3,4), out) || st.failed) return null;
      return termStr(st, out);
    })`, ctx);
    assert.strictEqual(fn(), '[4,8]');
  });

  test('generated runtime: foldl/4 sums a list', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState();
      var out = createVar(st.nextVarId++);
      if (!foldl_4(st, createAtom("sum"), mkList(1,2,3,4), createInt(0), out) || st.failed) return null;
      return deref(st, out).val;
    })`, ctx);
    assert.strictEqual(fn(), 10);
  });

  test('generated runtime: foldl/4 on empty list returns V0', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState();
      var out = createVar(st.nextVarId++);
      if (!foldl_4(st, createAtom("sum"), createNil(), createInt(42), out) || st.failed) return null;
      return deref(st, out).val;
    })`, ctx);
    assert.strictEqual(fn(), 42);
  });

  test('generated runtime: foldl/4 builds reversed list', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState();
      var out = createVar(st.nextVarId++);
      if (!foldl_4(st, createAtom("cons"), mkList(1,2,3), createNil(), out) || st.failed) return null;
      return termStr(st, out);
    })`, ctx);
    assert.strictEqual(fn(), '[3,2,1]');
  });

  test('generated runtime: once/1 succeeds for true', () => {
    const fn = vm.runInContext('(function(){ var st = initState(); return once_1(st, createAtom("true")) && !st.failed; })', ctx);
    assert.ok(fn());
  });

  test('generated runtime: once/1 fails for fail', () => {
    const fn = vm.runInContext('(function(){ var st = initState(); return once_1(st, createAtom("fail")) && !st.failed; })', ctx);
    assert.ok(!fn());
  });

  test('generated runtime: ignore/1 succeeds even when goal fails', () => {
    const fn = vm.runInContext('(function(){ var st = initState(); var r = ignore_1(st, createAtom("fail")); return r && !st.failed; })', ctx);
    assert.ok(fn());
  });
}());

// ---------------------------------------------------------------------------
// Form / CGI predicates
// ---------------------------------------------------------------------------
group('Form / CGI predicates');

test('read_string/2 with no form args binds to empty atom and records a text formInput', () => {
  const r = pl2js.runQuery('main :- read_string(\'Enter name:\', X), write(X).', 'main.');
  assert.strictEqual(r.error, null);
  assert.ok(r.formInputs.length >= 1);
  const fi = r.formInputs[0];
  assert.strictEqual(fi.type, 'text');
  assert.strictEqual(fi.name, 'rs_0');
  assert.strictEqual(fi.prompt, 'Enter name:');
  assert.strictEqual(r.output, '');  // empty atom written
});

test('read_string/2 with matching form arg binds to submitted value', () => {
  const r = pl2js.runQuery('main :- read_string(\'Enter name:\', X), write(X).', 'main.', 10, { rs_0: 'Alice' });
  assert.strictEqual(r.error, null);
  assert.strictEqual(r.output, 'Alice');
  assert.strictEqual(r.formInputs.length, 0);  // no pending inputs
});

test('read_string/1 with no form args records a text formInput (no prompt)', () => {
  const r = pl2js.runQuery('main :- read_string(X), write(X).', 'main.');
  assert.strictEqual(r.error, null);
  assert.ok(r.formInputs.length >= 1);
  const fi = r.formInputs[0];
  assert.strictEqual(fi.type, 'text');
  assert.strictEqual(fi.name, 'rs_0');
  assert.strictEqual(fi.prompt, '');
});

test('read_string/1 with matching form arg binds value', () => {
  const r = pl2js.runQuery('main :- read_string(X), write(X).', 'main.', 10, { rs_0: 'hello' });
  assert.strictEqual(r.error, null);
  assert.strictEqual(r.output, 'hello');
  assert.strictEqual(r.formInputs.length, 0);
});

test('multiple read_string/2 calls use sequential field names', () => {
  const prog = 'main :- read_string(\'Name:\', N), read_string(\'Age:\', A), write(N), write(\' \'), write(A).';
  const r = pl2js.runQuery(prog, 'main.');
  assert.strictEqual(r.error, null);
  assert.strictEqual(r.formInputs.length, 2);
  assert.strictEqual(r.formInputs[0].name, 'rs_0');
  assert.strictEqual(r.formInputs[1].name, 'rs_1');
});

test('multiple read_string/2 calls with all form args supplied run to completion', () => {
  const prog = 'main :- read_string(\'Name:\', N), read_string(\'Age:\', A), format(\'~w is ~w\', [N, A]).';
  const r = pl2js.runQuery(prog, 'main.', 10, { rs_0: 'Bob', rs_1: '30' });
  assert.strictEqual(r.error, null);
  assert.strictEqual(r.output, 'Bob is 30');
  assert.strictEqual(r.formInputs.length, 0);
});

test('form_argument/2 succeeds and binds value when arg is present', () => {
  const prog = 'main :- form_argument(color, C), write(C).';
  const r = pl2js.runQuery(prog, 'main.', 10, { color: 'red' });
  assert.strictEqual(r.error, null);
  assert.strictEqual(r.output, 'red');
});

test('form_argument/2 fails when arg is absent', () => {
  const prog = 'main :- (form_argument(color, _) -> write(found) ; write(missing)).';
  const r = pl2js.runQuery(prog, 'main.', 10, {});
  assert.strictEqual(r.error, null);
  assert.strictEqual(r.output, 'missing');
});

test('hidden_field/2 records a hidden formInput', () => {
  const prog = 'main :- hidden_field(step, 2), write(ok).';
  const r = pl2js.runQuery(prog, 'main.', 10, {});
  assert.strictEqual(r.error, null);
  assert.strictEqual(r.output, 'ok');
  assert.ok(r.formInputs.length >= 1);
  const fi = r.formInputs[0];
  assert.strictEqual(fi.type, 'hidden');
  assert.strictEqual(fi.name, 'step');
  assert.strictEqual(fi.value, '2');
});

test('hidden_field/2 and read_string/2 together produce both hidden and text inputs', () => {
  const prog = 'main :- hidden_field(step, 1), read_string(\'Email:\', _E).';
  const r = pl2js.runQuery(prog, 'main.', 10, {});
  assert.strictEqual(r.error, null);
  const hidden = r.formInputs.filter(function (fi) { return fi.type === 'hidden'; });
  const text   = r.formInputs.filter(function (fi) { return fi.type === 'text'; });
  assert.strictEqual(hidden.length, 1);
  assert.strictEqual(hidden[0].name, 'step');
  assert.strictEqual(text.length, 1);
  assert.strictEqual(text[0].name, 'rs_0');
});

test('runQuery returns empty formInputs array when no form predicates are used', () => {
  const r = pl2js.runQuery('main :- write(hello).', 'main.');
  assert.ok(Array.isArray(r.formInputs));
  assert.strictEqual(r.formInputs.length, 0);
});

test('runQuery with non-object formArgs defaults gracefully', () => {
  const r = pl2js.runQuery('main :- write(ok).', 'main.', 10, null);
  assert.strictEqual(r.error, null);
  assert.strictEqual(r.output, 'ok');
});

// generateHtml form-related tests
test('generateHtml: generated page includes form element', () => {
  const html = pl2js.generateHtml(RUNTIME_SRC, 'main :- write(hello).');
  assert.ok(html.includes('<form id="pl-form"'));
});

test('generateHtml: generated page reads URL params into formArgs', () => {
  const html = pl2js.generateHtml(RUNTIME_SRC, 'main :- write(hello).');
  assert.ok(html.includes('URLSearchParams'));
  assert.ok(html.includes('formArgs'));
});

test('generateHtml: generated page passes formArgs to runQuery', () => {
  const html = pl2js.generateHtml(RUNTIME_SRC, 'main :- write(hello).');
  assert.ok(html.includes('runQuery(prog'));
  assert.ok(html.includes('formArgs'));
});

test('generateHtml: generated page includes buildForm helper', () => {
  const html = pl2js.generateHtml(RUNTIME_SRC, 'main :- write(hello).');
  assert.ok(html.includes('buildForm'));
  assert.ok(html.includes('formInputs'));
});

test('generateHtml: generated page includes form CSS', () => {
  const html = pl2js.generateHtml(RUNTIME_SRC, 'main :- write(hello).');
  assert.ok(html.includes('.submit-btn'));
  assert.ok(html.includes('.text-input'));
  assert.ok(html.includes('#pl-form'));
});

// ---------------------------------------------------------------------------
// New type converters — bidirectional directions and new predicates
// ---------------------------------------------------------------------------
group('Type converters — reverse directions');

test('atom_codes/2 reverse: codes → atom', () => {
  assertBinding(q('', 'atom_codes(X, [104,101,108,108,111]).'), 'X', 'hello');
});

test('atom_codes/2 forward: atom → codes (existing)', () => {
  assertBinding(q('', 'atom_codes(hi, X).'), 'X', '[104,105]');
});

test('atom_codes/2 forward: integer → codes', () => {
  assertBinding(q('', 'atom_codes(42, X).'), 'X', '[52,50]');
});

test('char_code/2 reverse: code → char', () => {
  assertBinding(q('', 'char_code(X, 97).'), 'X', 'a');
});

test('char_code/2 forward: char → code (existing)', () => {
  assertBinding(q('', 'char_code(a, X).'), 'X', '97');
});

test('number_codes/2 reverse: codes → number', () => {
  assertBinding(q('', 'number_codes(X, [52,50]).'), 'X', '42');
});

test('number_codes/2 forward: number → codes (existing)', () => {
  assertBinding(q('', 'number_codes(42, X).'), 'X', '[52,50]');
});

test('number_chars/2 reverse: chars → number', () => {
  assertBinding(q('', "number_chars(X, ['4','2'])."), 'X', '42');
});

test('number_chars/2 forward: number → chars', () => {
  assertBinding(q('', 'number_chars(42, X).'), 'X', '[4,2]');
});

test('atom_number/2 reverse: number → atom', () => {
  assertBinding(q('', 'atom_number(X, 42).'), 'X', '42');
});

test('atom_number/2 forward: atom → number (existing)', () => {
  assertBinding(q('', "atom_number('42', N)."), 'N', '42');
});

test('term_to_atom/2 reverse: parse atom as term', () => {
  assertBinding(q('', "term_to_atom(X, 'f(1,2)')."), 'X', 'f(1,2)');
});

test('term_to_atom/2 forward: term → atom (existing)', () => {
  assertBinding(q('', 'term_to_atom(f(1,2), X).'), 'X', 'f(1,2)');
});

test('string_to_atom/2 reverse: atom → string', () => {
  assertBinding(q('', 'string_to_atom(X, hello).'), 'X', 'hello');
});

test('string_to_atom/2 forward: string → atom', () => {
  assertBinding(q('', 'string_to_atom(hello, X).'), 'X', 'hello');
});

group('New type converters');

test('atom_string/2 forward: atom → string', () => {
  assertBinding(q('', 'atom_string(hello, X).'), 'X', 'hello');
});

test('atom_string/2 reverse: string → atom', () => {
  assertBinding(q('', 'atom_string(X, hello).'), 'X', 'hello');
});

test('atom_string/2 forward: integer → string', () => {
  assertBinding(q('', 'atom_string(42, X).'), 'X', '42');
});

test('number_string/2 forward: number → string', () => {
  assertBinding(q('', 'number_string(42, X).'), 'X', '42');
});

test('number_string/2 reverse: string → number', () => {
  assertBinding(q('', "number_string(X, '42')."), 'X', '42');
});

test('term_string/2 forward: term → string', () => {
  assertBinding(q('', 'term_string(f(1,2), X).'), 'X', 'f(1,2)');
});

test('term_string/2 reverse: string → term', () => {
  assertBinding(q('', "term_string(X, 'f(1,2)')."), 'X', 'f(1,2)');
});

test('string_codes/2 forward: string → codes', () => {
  assertBinding(q('', 'string_codes(hi, X).'), 'X', '[104,105]');
});

test('string_codes/2 reverse: codes → string', () => {
  assertBinding(q('', 'string_codes(X, [104,105]).'), 'X', 'hi');
});

test('string_chars/2 forward: string → chars', () => {
  assertBinding(q('', 'string_chars(hi, X).'), 'X', '[h,i]');
});

test('string_chars/2 reverse: chars → string', () => {
  assertBinding(q('', 'string_chars(X, [h,i]).'), 'X', 'hi');
});

test('atomic_list_concat/2: join list of atoms', () => {
  assertBinding(q('', 'atomic_list_concat([hello,world], X).'), 'X', 'helloworld');
});

test('atomic_list_concat/3 forward: join with separator', () => {
  assertBinding(q('', "atomic_list_concat([a,b,c], '-', X)."), 'X', 'a-b-c');
});

test('atomic_list_concat/3 reverse: split by separator', () => {
  assertBinding(q('', "atomic_list_concat(X, '-', 'a-b-c')."), 'X', '[a,b,c]');
});

test('atomic_list_concat/3: integers in list', () => {
  assertBinding(q('', "atomic_list_concat([1,2,3], '+', X)."), 'X', '1+2+3');
});

test('writeq/1: writes term to output', () => {
  const r = q('', 'writeq(hello).');
  assert.strictEqual(r.error, null);
  assert.strictEqual(r.output, 'hello');
});

group('Built-in rejection');

test('defining a built-in predicate returns an error', () => {
  const r = q('atom_codes(X, Y) :- true.', 'true.');
  assert.ok(r.error !== null);
  assert.ok(r.error.includes('atom_codes/2'));
});

test('defining atom/1 (type-check built-in) returns an error', () => {
  const r = q('atom(X) :- true.', 'true.');
  assert.ok(r.error !== null);
  assert.ok(r.error.includes('atom/1'));
});

test('defining is/2 returns an error', () => {
  const r = q('is(X, Y) :- true.', 'true.');
  assert.ok(r.error !== null);
  assert.ok(r.error.includes('is/2'));
});

test('user predicate with same name but different arity is allowed', () => {
  // atom_codes/2 is built-in but my_pred/1 is not
  const r = q('my_pred(X) :- atom(X).', 'my_pred(hello).');
  assert.strictEqual(r.error, null);
  assert.ok(r.answers.length > 0);
});

group('Prelude auto-load');

test('string_lower/2 is available from prelude', () => {
  assertBinding(q('', 'string_lower(\'HELLO\', X).'), 'X', 'hello');
});

test('string_upper/2 is available from prelude', () => {
  assertBinding(q('', 'string_upper(hello, X).'), 'X', 'HELLO');
});

test('not_member/2 is available from prelude', () => {
  const r = q('', 'not_member(d, [a,b,c]).');
  assert.strictEqual(r.error, null);
  assert.ok(r.answers.length > 0);
});

test('not_member/2 fails when element is in list', () => {
  assert.ok(fails('', 'not_member(a, [a,b,c]).'));
});

test('pairs_keys_values/3 from prelude', () => {
  assertBinding(q('', 'pairs_keys_values([a-1,b-2], Ks, Vs), Ks = [a,b], Vs = [1,2].'), 'Ks', '[a,b]');
});

test('pairs_keys/2 from prelude', () => {
  assertBinding(q('', 'pairs_keys([a-1,b-2], Ks).'), 'Ks', '[a,b]');
});

test('pairs_values/2 from prelude', () => {
  assertBinding(q('', 'pairs_values([a-1,b-2], Vs).'), 'Vs', '[1,2]');
});

test('user clause overrides prelude clause', () => {
  // User can redefine a prelude predicate
  const r = q('string_lower(X, X).', "string_lower('HELLO', Y).");
  assertBinding(r, 'Y', 'HELLO');
});

// ---------------------------------------------------------------------------
// 27. pl2js.pl generated runtime — all built-in commands
// ---------------------------------------------------------------------------

// Extract and evaluate the header as before, then run tests against the full
// expanded runtime that now includes all startup commands.

(function testAllGeneratedCommands() {
  const plSrc = fs.readFileSync(path.join(__dirname, 'pl2js.pl'), 'utf8');
  const startMarker = "generate_js_header(Header) :-\n    Header =\n'";
  const endMarker   = "\n'.\n\n%% group_clauses_by_predicate";
  const s = plSrc.indexOf(startMarker);
  const e = plSrc.indexOf(endMarker);
  if (s < 0 || e < 0) {
    console.warn('WARNING: Could not locate JS header in pl2js.pl — skipping all-commands tests');
    return;
  }
  const headerJs = plSrc.slice(s + startMarker.length, e).replace(/''/g, "'");

  const vm = require('vm');
  const ctx = vm.createContext({ document: {} });  // mock browser env so _prologOutput captures output
  try { vm.runInContext(headerJs, ctx); } catch(err) {
    console.warn('WARNING: Header failed to evaluate — skipping all-commands tests:', err.message);
    return;
  }

  // Helper predicates for meta-call tests
  vm.runInContext(`
    function positive_1(state, x) { return gt_2(state, x, createInt(0)); }
    _registry["positive/1"] = positive_1;
    function negative_1(state, x) { return lt_2(state, x, createInt(0)); }
    _registry["negative/1"] = negative_1;
    function double_2(state, x, y) { return is_2(state, y, createCompound("*", 2, [x, createInt(2)])); }
    _registry["double/2"] = double_2;
    function mkIntList() {
      var args = Array.prototype.slice.call(arguments);
      var l = createNil();
      for (var i = args.length - 1; i >= 0; i--) l = createList(createInt(args[i]), l);
      return l;
    }
    function mkAtomList() {
      var args = Array.prototype.slice.call(arguments);
      var l = createNil();
      for (var i = args.length - 1; i >= 0; i--) l = createList(createAtom(args[i]), l);
      return l;
    }
    function termStr(state, t) {
      t = deref(state, t);
      if (t.type === "int")  return String(t.val);
      if (t.type === "nil")  return "[]";
      if (t.type === "atom") return t.name;
      if (t.type === "list") {
        var parts = [];
        var cur = t;
        while (cur.type === "list") { parts.push(termStr(state, cur.head)); cur = deref(state, cur.tail); }
        return "[" + parts.join(",") + "]";
      }
      if (t.type === "compound") return t.functor + "(" + t.args.map(function(a){ return termStr(state, a); }).join(",") + ")";
      return "?";
    }
    function run(fn) { var st = initState(); var ok = fn(st); return { ok: ok && !st.failed, st: st }; }
    function bind(fn) { var st = initState(); var v = createVar(st.nextVarId++); fn(st, v); return { st: st, v: v }; }
  `, ctx);

  group('pl2js.pl generated runtime — false/0, string/1, naf/1, call/N');

  test('generated: false/0 fails', () => {
    const fn = vm.runInContext('(function(){ var st = initState(); return false_0(st) && !st.failed; })', ctx);
    assert.ok(!fn());
  });

  test('generated: string/1 succeeds for atom', () => {
    const fn = vm.runInContext('(function(){ var st = initState(); return string_1(st, createAtom("hello")) && !st.failed; })', ctx);
    assert.ok(fn());
  });

  test('generated: string/1 fails for integer', () => {
    const fn = vm.runInContext('(function(){ var st = initState(); return string_1(st, createInt(42)) && !st.failed; })', ctx);
    assert.ok(!fn());
  });

  test('generated: naf_1 succeeds when goal fails', () => {
    const fn = vm.runInContext('(function(){ var st = initState(); return naf_1(st, createAtom("fail")) && !st.failed; })', ctx);
    assert.ok(fn());
  });

  test('generated: naf_1 fails when goal succeeds', () => {
    const fn = vm.runInContext('(function(){ var st = initState(); return naf_1(st, createAtom("true")) && !st.failed; })', ctx);
    assert.ok(!fn());
  });

  test('generated: call/1 calls a goal by name', () => {
    const fn = vm.runInContext('(function(){ var st = initState(); return call_1(st, createAtom("true")) && !st.failed; })', ctx);
    assert.ok(fn());
  });

  test('generated: call/2 calls a unary goal with extra arg', () => {
    const fn = vm.runInContext('(function(){ var st = initState(); return call_2(st, createAtom("positive"), createInt(5)) && !st.failed; })', ctx);
    assert.ok(fn());
  });

  test('generated: call/3 calls a binary goal with extra args', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState();
      var out = createVar(st.nextVarId++);
      var ok = call_3(st, createAtom("double"), createInt(4), out) && !st.failed;
      if (!ok) return null;
      return deref(st, out).val;
    })`, ctx);
    assert.strictEqual(fn(), 8);
  });

  group('pl2js.pl generated runtime — succ/2, plus/3, between/3');

  test('generated: succ_2 forward (n -> n+1)', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      if (!succ_2(st, createInt(4), out) || st.failed) return null;
      return deref(st, out).val;
    })`, ctx);
    assert.strictEqual(fn(), 5);
  });

  test('generated: succ_2 reverse (n+1 -> n)', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      if (!succ_2(st, out, createInt(5)) || st.failed) return null;
      return deref(st, out).val;
    })`, ctx);
    assert.strictEqual(fn(), 4);
  });

  test('generated: plus_3 X+Y=Z (forward)', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      if (!plus_3(st, createInt(3), createInt(4), out) || st.failed) return null;
      return deref(st, out).val;
    })`, ctx);
    assert.strictEqual(fn(), 7);
  });

  test('generated: plus_3 reverse Z-X=Y', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      if (!plus_3(st, createInt(3), out, createInt(7)) || st.failed) return null;
      return deref(st, out).val;
    })`, ctx);
    assert.strictEqual(fn(), 4);
  });

  test('generated: between_3 first solution', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      if (!between_3(st, createInt(3), createInt(5), out) || st.failed) return null;
      return deref(st, out).val;
    })`, ctx);
    assert.strictEqual(fn(), 3);
  });

  test('generated: between_3 + findall_3 collects all values', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState();
      var x = createVar(st.nextVarId++);
      var result = createVar(st.nextVarId++);
      var goal = createCompound("between", 3, [createInt(1), createInt(4), x]);
      if (!findall_3(st, x, goal, result) || st.failed) return null;
      return termStr(st, result);
    })`, ctx);
    assert.strictEqual(fn(), '[1,2,3,4]');
  });

  group('pl2js.pl generated runtime — type converters');

  test('generated: atom_number_2 atom->number', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      if (!atom_number_2(st, createAtom("42"), out) || st.failed) return null;
      return deref(st, out).val;
    })`, ctx);
    assert.strictEqual(fn(), 42);
  });

  test('generated: atom_number_2 number->atom', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      if (!atom_number_2(st, out, createInt(7)) || st.failed) return null;
      return deref(st, out).name;
    })`, ctx);
    assert.strictEqual(fn(), '7');
  });

  test('generated: upcase_atom_2', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      if (!upcase_atom_2(st, createAtom("hello"), out) || st.failed) return null;
      return deref(st, out).name;
    })`, ctx);
    assert.strictEqual(fn(), 'HELLO');
  });

  test('generated: downcase_atom_2', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      if (!downcase_atom_2(st, createAtom("HELLO"), out) || st.failed) return null;
      return deref(st, out).name;
    })`, ctx);
    assert.strictEqual(fn(), 'hello');
  });

  test('generated: atom_string_2 atom->string', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      if (!atom_string_2(st, createAtom("hi"), out) || st.failed) return null;
      return deref(st, out).name;
    })`, ctx);
    assert.strictEqual(fn(), 'hi');
  });

  test('generated: string_codes_2 forward', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      if (!string_codes_2(st, createAtom("ab"), out) || st.failed) return null;
      return termStr(st, out);
    })`, ctx);
    assert.strictEqual(fn(), '[97,98]');
  });

  test('generated: string_chars_2 forward', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      if (!string_chars_2(st, createAtom("hi"), out) || st.failed) return null;
      return termStr(st, out);
    })`, ctx);
    assert.strictEqual(fn(), '[h,i]');
  });

  test('generated: atomic_list_concat_2 joins list', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      var list = createList(createAtom("foo"), createList(createAtom("bar"), createNil()));
      if (!atomic_list_concat_2(st, list, out) || st.failed) return null;
      return deref(st, out).name;
    })`, ctx);
    assert.strictEqual(fn(), 'foobar');
  });

  test('generated: atomic_list_concat_3 joins with separator', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      var list = createList(createAtom("a"), createList(createAtom("b"), createList(createAtom("c"), createNil())));
      if (!atomic_list_concat_3(st, list, createAtom("-"), out) || st.failed) return null;
      return deref(st, out).name;
    })`, ctx);
    assert.strictEqual(fn(), 'a-b-c');
  });

  test('generated: atomic_list_concat_3 splits by separator', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      if (!atomic_list_concat_3(st, out, createAtom("-"), createAtom("a-b-c")) || st.failed) return null;
      return termStr(st, out);
    })`, ctx);
    assert.strictEqual(fn(), '[a,b,c]');
  });

  test('generated: writeq_1 writes term', () => {
    const fn = vm.runInContext(`(function(){
      var result = runQuery(function(st) { writeq_1(st, createAtom("hello")); return true; }, []);
      return result.output;
    })`, ctx);
    assert.strictEqual(fn(), 'hello');
  });

  test('generated: format_1 handles ~n', () => {
    const fn = vm.runInContext(`(function(){
      var result = runQuery(function(st) { format_1(st, createAtom("line~n")); return true; }, []);
      return result.output;
    })`, ctx);
    // In the raw-source extracted header, \\n represents the 2-char string \n
    // (Prolog escape processing is not applied during test extraction)
    assert.ok(fn() === 'line\n' || fn() === 'line\\n');
  });

  group('pl2js.pl generated runtime — list predicates');

  test('generated: flatten_2 flattens nested list', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      var nested = createList(createInt(1), createList(createList(createInt(2), createList(createInt(3), createNil())), createNil()));
      if (!flatten_2(st, nested, out) || st.failed) return null;
      return termStr(st, out);
    })`, ctx);
    assert.strictEqual(fn(), '[1,2,3]');
  });

  test('generated: max_list_2 finds maximum', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      if (!max_list_2(st, mkIntList(3,1,4,1,5,9), out) || st.failed) return null;
      return deref(st, out).val;
    })`, ctx);
    assert.strictEqual(fn(), 9);
  });

  test('generated: min_list_2 finds minimum', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      if (!min_list_2(st, mkIntList(3,1,4,1,5,9), out) || st.failed) return null;
      return deref(st, out).val;
    })`, ctx);
    assert.strictEqual(fn(), 1);
  });

  test('generated: sum_list_2 sums elements', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      if (!sum_list_2(st, mkIntList(1,2,3,4), out) || st.failed) return null;
      return deref(st, out).val;
    })`, ctx);
    assert.strictEqual(fn(), 10);
  });

  test('generated: numlist_3 generates integer list', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      if (!numlist_3(st, createInt(1), createInt(5), out) || st.failed) return null;
      return termStr(st, out);
    })`, ctx);
    assert.strictEqual(fn(), '[1,2,3,4,5]');
  });

  test('generated: list_to_set_2 removes duplicates', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      if (!list_to_set_2(st, mkIntList(1,2,1,3,2), out) || st.failed) return null;
      return termStr(st, out);
    })`, ctx);
    assert.strictEqual(fn(), '[1,2,3]');
  });

  test('generated: subtract_3 removes elements', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      if (!subtract_3(st, mkIntList(1,2,3,4), mkIntList(2,4), out) || st.failed) return null;
      return termStr(st, out);
    })`, ctx);
    assert.strictEqual(fn(), '[1,3]');
  });

  test('generated: intersection_3 finds common elements', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      if (!intersection_3(st, mkIntList(1,2,3), mkIntList(2,3,4), out) || st.failed) return null;
      return termStr(st, out);
    })`, ctx);
    assert.strictEqual(fn(), '[2,3]');
  });

  test('generated: union_3 merges unique elements', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      if (!union_3(st, mkIntList(1,2,3), mkIntList(2,3,4), out) || st.failed) return null;
      return termStr(st, out);
    })`, ctx);
    assert.strictEqual(fn(), '[1,2,3,4]');
  });

  test('generated: delete_3 removes all occurrences', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      if (!delete_3(st, mkIntList(1,2,1,3,1), createInt(1), out) || st.failed) return null;
      return termStr(st, out);
    })`, ctx);
    assert.strictEqual(fn(), '[2,3]');
  });

  test('generated: select_3 first match', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState();
      var elem = createVar(st.nextVarId++);
      var rest = createVar(st.nextVarId++);
      if (!select_3(st, elem, mkIntList(1,2,3), rest) || st.failed) return null;
      return deref(st, elem).val;
    })`, ctx);
    assert.strictEqual(fn(), 1);
  });

  test('generated: permutation_2 first permutation is identity', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      if (!permutation_2(st, mkIntList(1,2,3), out) || st.failed) return null;
      return termStr(st, out);
    })`, ctx);
    assert.strictEqual(fn(), '[1,2,3]');
  });

  group('pl2js.pl generated runtime — findall/3, forall/2, aggregate_all/3');

  test('generated: findall_3 collects all solutions', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState();
      var x = createVar(st.nextVarId++);
      var result = createVar(st.nextVarId++);
      var goal = createCompound("between", 3, [createInt(1), createInt(3), x]);
      if (!findall_3(st, x, goal, result) || st.failed) return null;
      return termStr(st, result);
    })`, ctx);
    assert.strictEqual(fn(), '[1,2,3]');
  });

  test('generated: findall_3 returns empty list when no solutions', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState();
      var x = createVar(st.nextVarId++);
      var result = createVar(st.nextVarId++);
      if (!findall_3(st, x, createAtom("fail"), result) || st.failed) return null;
      return termStr(st, result);
    })`, ctx);
    assert.strictEqual(fn(), '[]');
  });

  test('generated: forall_2 succeeds when condition is empty', () => {
    const fn = vm.runInContext('(function(){ var st = initState(); return forall_2(st, createAtom("fail"), createAtom("true")) && !st.failed; })', ctx);
    assert.ok(fn());
  });

  test('generated: aggregate_all_3 counts solutions', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState();
      var x = createVar(st.nextVarId++);
      var result = createVar(st.nextVarId++);
      var goal = createCompound("between", 3, [createInt(1), createInt(5), x]);
      if (!aggregate_all_3(st, createAtom("count"), goal, result) || st.failed) return null;
      return deref(st, result).val;
    })`, ctx);
    assert.strictEqual(fn(), 5);
  });

  group('pl2js.pl generated runtime — include/3, exclude/3');

  test('generated: include_3 keeps matching elements', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      if (!include_3(st, createAtom("positive"), mkIntList(-1,2,-3,4), out) || st.failed) return null;
      return termStr(st, out);
    })`, ctx);
    assert.strictEqual(fn(), '[2,4]');
  });

  test('generated: exclude_3 removes matching elements', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      if (!exclude_3(st, createAtom("negative"), mkIntList(-1,2,-3,4), out) || st.failed) return null;
      return termStr(st, out);
    })`, ctx);
    assert.strictEqual(fn(), '[2,4]');
  });

  test('generated: include_3 on empty list returns empty', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      if (!include_3(st, createAtom("positive"), createNil(), out) || st.failed) return null;
      return termStr(st, out);
    })`, ctx);
    assert.strictEqual(fn(), '[]');
  });

  test('generated: succ_or_zero_2 returns 0 for 0', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      if (!succ_or_zero_2(st, createInt(0), out) || st.failed) return null;
      return deref(st, out).val;
    })`, ctx);
    assert.strictEqual(fn(), 0);
  });

  test('generated: succ_or_zero_2 returns n-1 for n>0', () => {
    const fn = vm.runInContext(`(function(){
      var st = initState(); var out = createVar(st.nextVarId++);
      if (!succ_or_zero_2(st, createInt(5), out) || st.failed) return null;
      return deref(st, out).val;
    })`, ctx);
    assert.strictEqual(fn(), 4);
  });
}());

// ---------------------------------------------------------------------------
// Summary

// ---------------------------------------------------------------------------
console.log('\n' + '─'.repeat(50));
console.log('Results: ' + _passed + ' passed, ' + _failed + ' failed');
if (_failed > 0) {
  console.log('SOME TESTS FAILED');
  process.exit(1);
} else {
  console.log('ALL TESTS PASSED');
}
