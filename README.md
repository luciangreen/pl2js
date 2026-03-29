# pl2js — Prolog to JavaScript Compiler

`pl2js` is a source-to-source compiler that translates a Prolog source file into equivalent JavaScript code. It is based on the same overall design as [`pl2c`](../pl2c.pl), but targets JavaScript instead of C.

The compiler reads Prolog clauses, groups them by predicate, and emits a self-contained JavaScript file that contains:

- A minimal runtime library (term representation, variable bindings, unification, choice points, backtracking, cut, arithmetic, and built-in predicates).
- A generated JavaScript function for every predicate in the source file.
- An entry point that calls `main/0` if it is defined.

---

## Repository structure

```
pl2js/
  pl2js.pl           — Prolog-to-JavaScript compiler module
  README.md          — this file
  examples/
    family.pl        — sample Prolog source (family facts, rules, lists)
    family.js        — compiled JavaScript output from family.pl
    index.html       — minimal HTML page that runs queries in the browser
```

---

## Requirements

- **SWI-Prolog** (≥ 8.0) to run the compiler (`pl2js.pl`).
- A modern web browser (Chrome, Firefox, Safari, Edge) to run the generated JavaScript.
- **Node.js** (optional) to run the generated JavaScript from the command line.

---

## How to compile a `.pl` file to `.js`

### From SWI-Prolog

```prolog
?- [pl2js].
?- compile_prolog_to_js('examples/family.pl', 'examples/family_compiled.js').
```

Or use the convenience predicate:

```prolog
?- compile_file('examples/family', 'examples/family_out').
% Writes examples/family_out.js
```

### From the command line (one-liner)

```bash
swipl -g "use_module('pl2js'), compile_prolog_to_js('examples/family.pl', 'examples/family.js')" -t halt
```

---

## How to run the generated JavaScript

### In a browser (desktop, iPhone, Android)

1. Open `examples/index.html` directly in your browser.
   - On desktop: double-click the file, or use `File › Open` in your browser.
   - On iPhone / Android: transfer the `examples/` folder to your device and open `index.html` with Safari / Chrome.
2. The page loads `family.js` and provides buttons to run queries interactively.

> **Note:** Some browsers block local `<script src="...">` loads when the page is opened from the filesystem (`file://`). If you see no output, serve the files with a local HTTP server:
>
> ```bash
> # Python 3
> python3 -m http.server 8080
> # then open http://localhost:8080/examples/index.html
> ```

### With Node.js (command line)

```bash
node examples/family.js
```

Expected output:

```
=== Family Relationships ===
grandparent(tom, ann) = true
member(bob, [tom,bob,liz]) = true
max(3,5) = 5
=== Done ===
```

---

## How to test with a small sample predicate and query

Write a file `hello.pl`:

```prolog
greet(X) :- write('Hello, '), write(X), nl.

main :- greet(world).
```

Compile it:

```prolog
?- [pl2js].
?- compile_prolog_to_js('hello.pl', 'hello.js').
```

Run it:

```bash
node hello.js
# Hello, world
```

---

## Public API (`pl2js.pl`)

| Predicate | Description |
|---|---|
| `compile_prolog_to_js(+PrologFile, +JSFile)` | Compile a Prolog source file to a JavaScript file. |
| `compile_file(+PrologFile, +OutputBase)` | Compile `PrologFile` and write `OutputBase.js`. |
| `verify_equivalence(+PrologFile)` | Run both SWI-Prolog and Node.js on the source and diff their output (requires `node`). |

---

## Supported Prolog subset

| Feature | Status |
|---|---|
| Facts | ✅ |
| Rules | ✅ |
| Grouping clauses by predicate | ✅ |
| Deterministic predicates | ✅ |
| Nondeterministic predicates (choice points, backtracking) | ✅ |
| Conjunction (`,`) | ✅ |
| Disjunction (`;`) | ✅ |
| If-then-else (`-> ;`) | ✅ |
| Cut (`!`) | ✅ |
| `true` / `fail` | ✅ |
| Unification (`=`) | ✅ |
| Structural equality (`==`, `\==`) | ✅ |
| Atoms | ✅ |
| Integers | ✅ |
| Compound terms | ✅ |
| Lists (`[H\|T]`, `[]`) | ✅ |
| `is/2` and arithmetic (`+`, `-`, `*`, `/`, `//`, `mod`, `**`, bit ops) | ✅ |
| Comparison (`>`, `<`, `>=`, `=<`) | ✅ |
| Standard order comparison (`@<`, `@>`, `@=<`, `@>=`, `compare/3`) | ✅ |
| `write/1`, `writeln/1`, `nl/0`, `tab/1`, `format/2` | ✅ |
| Type checking (`atom/1`, `integer/1`, `var/1`, `nonvar/1`, `compound/1`, `atomic/1`, `is_list/1`, `ground/1`) | ✅ |
| `length/2`, `nth0/3`, `nth1/3`, `last/2`, `reverse/2` | ✅ |
| `atom_length/2`, `atom_concat/3`, `atom_chars/2`, `atom_codes/2`, `char_code/2` | ✅ |
| `functor/3`, `arg/3`, `=../2` (univ) | ✅ |
| `copy_term/2` | ✅ |
| `sort/2`, `msort/2` | ✅ |
| `findall/3` | ✅ |

### Not yet supported / partial

| Feature | Status |
|---|---|
| Body backtracking (retrying an earlier goal when a later goal fails) | ❌ (known limitation — same as pl2c) |
| Floats | ❌ (integers only) |
| `number_vars/3` | ❌ |
| `assert/retract` | ❌ |
| `bagof/3`, `setof/3` | ❌ |
| `call/N` (meta-call) | ❌ |
| Exceptions (`throw/1`, `catch/3`) | ❌ |
| Operator definitions (`op/3`) | ❌ |
| DCG (`-->`) | ❌ |
| `sub_atom/5` (non-deterministic) | partial |
| `once/1`, `ignore/1` | partial (simplified) |
| ISO character I/O (`get_char/1`, `put_char/1`) | ❌ |
| File I/O | ❌ |

> **Note on body backtracking:** When a nondeterministic predicate `P` is called as a goal in a rule body, and a *later* goal in the same body fails, the compiler does not automatically retry `P` with its next clause. This mirrors the same limitation in `pl2c`. Predicates that rely on body backtracking should be restructured so the first matching clause succeeds on first try, or use explicit disjunction (`;`) at the predicate level instead.

---

## Design notes

`pl2js.pl` follows the same pipeline as `pl2c.pl`:

1. Read Prolog clauses with `read_term/3`.
2. Group clauses by predicate signature (`Name/Arity`).
3. For each predicate group:
   - Single clause → generate a simple JS function.
   - Multiple clauses → generate a nondeterministic JS function with an explicit choice-point stack.
4. Emit a JS runtime library as the file header.
5. Emit all generated predicate functions.
6. Emit a simple entry-point footer.

The generated JS uses plain objects for terms and a mutable state object for bindings, the choice-point stack, and backtracking flags — mirroring the C struct used in `pl2c`.

---

## License

Same as the parent `pl2c` repository (see [LICENSE](https://github.com/luciangreen/pl2js/blob/main/LICENSE)).
