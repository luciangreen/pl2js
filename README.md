# pl2js — Prolog to JavaScript Translator

`pl2js` has two complementary parts:

1. **`pl2js.pl`** — a SWI-Prolog source-to-source compiler that translates a Prolog file into a self-contained JavaScript file (same design as [`pl2c`](https://github.com/luciangreen/pl2c), targeting JavaScript instead of C).

2. **`pl2js.js` + `index.html`** — a browser-side translator/runtime that lets you write, load, save, and run Prolog **directly in the browser** with no server or installation required.  The browser tool parses Prolog source text on the fly, builds a clause database, and executes queries against it — all in JavaScript.  It intentionally avoids building a full interpreter or WAM; instead it uses simple clause-structure iteration with explicit unification and continuation-passing backtracking.


---

* NEW: Run code directly in browser without installation with [pl2js](https://luciangreen.github.io/pl2js/).

* Programming tip: You can find library predicates such as my_reverse in the examples folder. When using my_reverse, make sure the append predicate is also defined, as it is required for correct execution.

---

## Quick start — browser editor (no installation needed)

1. Clone or download the repository.
2. Open **`index.html`** in any modern browser (Chrome, Firefox, Safari, Edge).
3. Type or paste a Prolog program in the editor, or click **Load .pl** to open a file.
4. Enter a query in the query box (e.g. `grandparent(X, Z).`) and click **Run Query**.
5. Results appear immediately on the same screen.
6. Click **Save .pl** to download the current program.

> **Note — file:// restrictions:** Most browsers allow loading `index.html` directly from the filesystem (file://). If you see no output or a script-load error, serve the folder with a local HTTP server instead:
>
> ```bash
> # Python 3
> python3 -m http.server 8080
> # then open: http://localhost:8080/index.html
> ```

The editor automatically remembers your most recent program text and query in `localStorage`, so your work is preserved between visits. If you close or navigate away with unsaved changes, the page reminds you first.

---

## Repository structure

```
pl2js/
  pl2js.js           — browser-side Prolog translator/runtime (NEW)
  index.html         — standalone one-screen browser editor (NEW)
  pl2js.pl           — SWI-Prolog source-to-source compiler module
  README.md          — this file
  extras/
    strings.pl       — prelude: string_lower/2, string_upper/2
    lists.pl         — prelude: not_member/2, max_member/2, min_member/2
    pairs.pl         — prelude: pairs_keys_values/3, pairs_keys/2, pairs_values/2
  examples/
    family.pl        — family facts and rules
    family.js        — compiled JavaScript output from family.pl
    lists.pl         — list operations (member, append, reverse, …)
    rules.pl         — rule chains, negation-as-failure, classification
    index.html       — demo page for the pre-compiled family.js
```

---

## Requirements

- **Browser editor (`pl2js.js` / `index.html`):** Any modern web browser — no installation.
- **SWI-Prolog compiler (`pl2js.pl`):** SWI-Prolog ≥ 8.0.
- **Node.js:** Optional — to run compiled `.js` files from the command line.
---

## How to compile a `.pl` file to `.js` (SWI-Prolog compiler)

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

## Public API — `pl2js.js` (browser translator)

`pl2js.js` exposes a single global object `window.pl2js` (or `module.exports` in Node.js):

```javascript
const result = pl2js.runQuery(programSource, queryString, maxAnswers, formArgs);
// programSource : string — Prolog source text
// queryString   : string — query to run (trailing '.' optional)
// maxAnswers    : number — maximum solutions to collect (default: 10)
// formArgs      : object — optional key/value map of form/URL parameters
//                          (passed to Prolog as named arguments accessible via
//                          form_argument/2 and read_string/1-2)
//
// result: { ok, answers, output, formInputs, error }
//   ok:         true if at least one answer was found (or query succeeded with no variables)
//   answers:    array of { varName: stringValue } bindings
//   output:     text written by write/nl/writeln etc.
//   formInputs: array of form field descriptors collected by read_string/1-2
//               and hidden_field/2 — use these to render an interactive form
//   error:      string if something went wrong, otherwise null
```

```javascript
const html = pl2js.generateHtml(runtimeSource, programSource);
// runtimeSource : string — raw text of pl2js.js (fetched by the caller)
// programSource : string — Prolog program text to embed
//
// Returns a fully self-contained HTML string that embeds the runtime and program,
// auto-runs main/0 on page load, and supports interactive forms via the
// form predicates described below.
```

```javascript
pl2js.registerFile(path, content);
// path    : string — file path as used in a :- include(path). directive
//                    (e.g. 'extras/strings.pl')
// content : string — Prolog source text of the file
//
// Registers a file in the virtual file system so that :- include(path).
// directives can resolve it.  In Node.js the extras/ directory is loaded
// automatically; call registerFile() in browser environments before runQuery().
```

---

## Built-in predicates — `pl2js.js`

`pl2js.js` includes two tiers of built-in predicates.

### Hardcoded built-ins (JS-native, cannot be overridden)

These predicates are implemented directly in JavaScript.  Any attempt by user
code to define a clause with the same name/arity is rejected with a
`Permission error`.

| Group | Predicates |
|---|---|
| Control flow | `true/0`, `fail/0`, `false/0`, `nl/0`, `!/0`, `,/2`, `;/2`, `->/2`, `\+/1`, `not/1` |
| Unification / comparison | `=/2`, `\=/2`, `==/2`, `\==/2`, `@</2`, `@>/2`, `@=</2`, `@>=/2`, `compare/3` |
| Arithmetic | `is/2`, `>/2`, `</2`, `>=/2`, `=</2`, `=:=/2`, `=\=/2` |
| I/O | `write/1`, `writeln/1`, `writeq/1`, `write_term/2`, `print/1`, `tab/1`, `format/1`, `format/2` |
| Type checks | `atom/1`, `integer/1`, `number/1`, `float/1`, `var/1`, `nonvar/1`, `compound/1`, `atomic/1`, `callable/1`, `is_list/1`, `ground/1`, `string/1` |
| Term manipulation | `functor/3`, `arg/3`, `=../2`, `copy_term/2` |
| Atom / string / char | `atom_length/2`, `atom_concat/3`, `atom_chars/2`, `atom_codes/2`, `atom_number/2`, `atom_string/2`, `number_codes/2`, `number_chars/2`, `number_string/2`, `char_code/2`, `term_to_atom/2`, `term_string/2`, `upcase_atom/2`, `downcase_atom/2`, `string_concat/3`, `string_to_atom/2`, `string_length/2`, `string_codes/2`, `string_chars/2`, `atomic_list_concat/2`, `atomic_list_concat/3`, `char_type/2` |
| Lists | `length/2`, `last/2`, `nth0/3`, `nth1/3`, `reverse/2`, `sort/2`, `msort/2`, `flatten/2`, `max_list/2`, `min_list/2`, `sum_list/2`, `numlist/3`, `list_to_set/2`, `permutation/2`, `select/3`, `subtract/3`, `intersection/3`, `union/3`, `delete/3` |
| Findall family | `findall/3`, `aggregate_all/3`, `bagof/3`, `setof/3`, `forall/2` |
| Control / meta | `once/1`, `ignore/1`, `call/1`–`call/8` |
| Arithmetic helpers | `succ/2`, `plus/3`, `between/3`, `succ_or_zero/2` |
| Higher-order | `maplist/2`–`maplist/5`, `include/3`, `exclude/3`, `convlist/3`, `foldl/4`–`foldl/7` |
| Side-effect / meta | `assert/1`, `asserta/1`, `assertz/1`, `retract/1`, `abolish/1`, `nb_getval/2`, `nb_setval/2`, `b_setval/2`, `b_getval/2`, `read_term/2`, `with_output_to/2`, `predsort/3` |
| Form / CGI | `read_string/1`, `read_string/2`, `form_argument/2`, `hidden_field/2` |
| File / folder I/O | `read_file/2`, `save_file/2`, `read_folder/2`, `save_folder/2` |

### File / folder I/O predicates

#### `read_file(+Path, -Content)`

Reads the file at `Path` (an atom) and unifies `Content` with its text content
as an atom.

- **Node.js**: reads directly from the real filesystem using `fs.readFileSync`.
- **Browser**: looks the path up in the internal virtual file system (populated
  via `pl2js.registerFile/2`).  Throws if the path is not registered.

```prolog
:- read_file('data/input.txt', Content), writeln(Content).
```

#### `save_file(+Path, +Content)`

Writes `Content` (an atom) to the file at `Path` (an atom).

- **Node.js**: writes to the real filesystem using `fs.writeFileSync`.
- **Browser**: triggers a browser download of the content as a text file named
  after the last path component.

```prolog
:- save_file('output/result.txt', 'Hello, world!').
```

#### `read_folder(+Path, -Files)`

Unifies `Files` with a list of relative file path atoms found inside the
directory at `Path`.  Subdirectories are traversed recursively, so nested
files are returned as paths like `'subdir/file.txt'`.

- **Node.js**: walks the directory tree recursively using `fs.readdirSync`
  with `withFileTypes: true`.
- **Browser**: collects VFS keys whose path starts with `Path + '/'` and
  returns each key's relative path (including nested paths such as
  `'subdir/file.txt'`).

```prolog
:- read_folder('src', Files), maplist(writeln, Files).
```

#### `save_folder(+Path, +FileList)`

Creates the directory `Path` and writes a set of files into it.  `FileList`
must be a proper Prolog list of `file(Name, Content)` terms, where both `Name`
and `Content` are atoms.  `Name` may contain path separators to place files in
nested subdirectories (e.g. `'subdir/file.txt'`).

- **Node.js**: creates the directory (and any required subdirectories) using
  `fs.mkdirSync` with `{recursive: true}`, and writes each named file using
  `fs.writeFileSync`.
- **Browser**: builds a ZIP archive (stored, no compression) containing all
  the files under a top-level folder named after `Path`, preserving any nested
  paths, then triggers a browser download of the archive named `<Path>.zip`.

```prolog
Files = [file('main.pl', ':- writeln(hello).'),
         file('lib/utils.pl', ':- writeln(utils).'),
         file('readme.txt', 'Example project')],
save_folder('myproject', Files).
```

### Prelude predicates (Prolog-defined, can be overridden)

These predicates are defined in Prolog source files under the `extras/`
directory.  They are loaded automatically into every query database via
`:- include(File).` directives (see below), **before** user clauses.
User code may redefine any of them.

| File | Predicates |
|---|---|
| `extras/strings.pl` | `string_lower/2`, `string_upper/2` |
| `extras/lists.pl` | `not_member/2`, `max_member/2`, `min_member/2` |
| `extras/pairs.pl` | `pairs_keys_values/3`, `pairs_keys/2`, `pairs_values/2` |

---

## The `:- include(File).` directive

`pl2js.js` supports the standard Prolog directive

```prolog
:- include('path/to/file.pl').
```

When this directive appears in a program source (or in the prelude), the
runtime looks up `'path/to/file.pl'` in an internal **virtual file system**
and inlines the clauses from that file at the point of the directive.  The
included source is parsed recursively, so included files may themselves
contain further `include` directives.

**In Node.js** the `extras/` directory is populated automatically at
module-load time using `fs.readFileSync`, so the prelude files are always
available.

**In browser environments** there is no file-system access.  Call
`pl2js.registerFile(path, content)` before the first `runQuery()` call to
register any files you want `include` to resolve:

```javascript
// Register an extra file so :- include('extras/strings.pl'). can resolve it.
pl2js.registerFile('extras/strings.pl', prologSourceString);
```

You can also use `:- include(File).` in your own Prolog programs to split
large programs into multiple logical units, as long as the referenced files
have been registered first.

---

## Supported Prolog subset — browser (`pl2js.js`)

| Feature | Status |
|---|---|
| Facts and rules | ✅ |
| Atoms, integers, compound terms | ✅ |
| Variables | ✅ |
| Lists `[H\|T]`, `[]` | ✅ |
| Conjunction `,` | ✅ |
| Disjunction `;` | ✅ |
| If-then-else `(Cond -> Then ; Else)` | ✅ |
| If-then `(Cond -> Then)` | ✅ |
| Cut `!` | ✅ |
| Negation as failure `\+` | ✅ |
| Unification `=/2`, non-unification `\=/2` | ✅ |
| Structural equality `==/2`, `\==/2` | ✅ |
| Arithmetic `is/2`, `>/2`, `</2`, `>=/2`, `=</2`, `=:=/2`, `=\=/2` | ✅ |
| `true/0`, `fail/0`, `nl/0`, `write/1`, `writeln/1`, `tab/1`, `format/2` | ✅ |
| `atom/1`, `integer/1`, `number/1`, `var/1`, `nonvar/1`, `compound/1`, `atomic/1`, `is_list/1`, `ground/1` | ✅ |
| `atom_concat/3`, `atom_length/2`, `atom_chars/2`, `atom_codes/2`, `char_code/2` | ✅ |
| `functor/3`, `arg/3`, `=../2`, `copy_term/2` | ✅ |
| `length/2`, `nth0/3`, `nth1/3`, `sort/2`, `msort/2` | ✅ |
| `findall/3` | ✅ |
| `bagof/3`, `setof/3` (simplified — no grouping by free vars) | ✅ partial |
| `once/1`, `ignore/1`, `forall/2` | ✅ |
| `call/1`, `call/N` | ✅ |
| `maplist/2`, `maplist/3`, `maplist/4`, `maplist/5`, `convlist/3`, `foldl/4`–`foldl/7`, `include/3`, `exclude/3` | ✅ |
| `succ/2`, `plus/3`, `between/3` | ✅ |
| `compare/3`, `@</2`, `@>/2`, `@=</2`, `@>=/2` | ✅ |
| `read_string/1`, `read_string/2` | ✅ |
| `form_argument/2` | ✅ |
| `hidden_field/2` | ✅ |
| Floats | ❌ (treated as integers) |
| `assert/retract` (dynamic predicates) | ❌ |
| Exceptions `throw/1`, `catch/3` | ❌ |
| Operator declarations `op/3` | ❌ |
| DCG `-->` | ❌ |
| Full body backtracking across multiple nondeterministic calls | ✅ (supported via CPS) |
| Recursion depth limit | 500 calls (configurable) |
| Maximum answers per query | 10 (configurable) |

### Known limitations

- **Floats** are parsed but converted to integers (`3.14` becomes `3`).
- **assert/retract** are silently ignored (dynamic databases not supported).
- **Exceptions** (`throw/catch`) are not supported.
- **Recursion depth** is limited to 500 to prevent browser hangs.
- **ISO compliance** is not a goal; many edge cases differ from standard Prolog.

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

## Form / CGI support

`pl2js.js` lets a Prolog program interact with the user through HTML forms — without
any server.  The pattern works like classic CGI: the program reads input values, and
if an input is not yet available the runtime records a form field so the browser can
render a `<form>` for the user to fill in.

### How it works

1. On first execution `read_string/1-2` binds the value to the empty atom `''` and
   adds a text-input descriptor to `result.formInputs`.
2. The page renders the form (or `generateHtml` does this automatically).
3. When the user submits, the browser appends the field values to the URL as query
   parameters.
4. On re-execution `runQuery` receives those parameters via the `formArgs` argument;
   `read_string` now finds the matching value and unifies it with the variable.

### Form predicates

| Predicate | Description |
|---|---|
| `read_string(?Value)` | Bind `Value` to a submitted text-input value.  On first call (no form data yet) binds to `''` and records a text field.  Field names are generated automatically as `rs_0`, `rs_1`, … |
| `read_string(+Prompt, ?Value)` | Same as `read_string/1` but associates a visible label `Prompt` with the field. |
| `form_argument(+Name, ?Value)` | Unify `Value` with the URL query parameter named `Name`.  Fails if the parameter is absent. |
| `hidden_field(+Name, +Value)` | Record a hidden `<input type="hidden">` field in the form, preserving state across submissions. |

### Minimal example

```prolog
main :-
    read_string('Your name', Name),
    (   Name = ''
    ->  true                          % first run — form will be shown
    ;   write('Hello, '), write(Name), nl
    ).
```

When embedded in a page via `generateHtml/2`, opening it shows a text field labeled
"Your name".  Submitting the form reruns `main/0` with `Name` bound to the entered
text and prints the greeting.

---

## Design notes — `pl2js.js` (browser translator)

`pl2js.js` intentionally avoids building a new full interpreter, WAM, or bytecode engine. Instead:

1. **Tokenize** the Prolog source into tokens (atoms, variables, numbers, operators, punctuation).
2. **Parse** using a recursive-descent operator-precedence parser into JavaScript term data structures (`{type:'atom',name:'foo'}`, `{type:'compound',functor:'parent',arity:2,args:[…]}`, etc.).
3. **Build a clause database**: group `{head, body}` pairs by predicate key (`name/arity`).
4. **Execute queries** by iterating the clause database with explicit unification and continuation-passing backtracking. No virtual machine; each clause is tried in order by copying the environment and unifying the query with the clause head, then executing the body.
5. **Variable renaming** gives every clause attempt fresh variable IDs so separate attempts don't share bindings.

This is "translated executable structures, not a full independent runtime language engine" as required.

---

## Design notes — `pl2js.pl` (SWI-Prolog compiler)

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
