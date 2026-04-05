% pl2js.pl - Prolog to JavaScript Compiler
% Converts Prolog code into equivalent JavaScript code with explicit loops and if-then statements
% Closely mirrors the architecture of pl2c.pl, but targeting JavaScript instead of C.

:- module(pl2js, [
    compile_prolog_to_js/2,
    compile_file/2,
    verify_equivalence/1
]).

:- use_module(library(lists)).
:- use_module(library(readutil)).

% b_setval key used to store the ordered list of clause variables during compilation
% (b_setval preserves variable identity, unlike assert/retract)

%% compile_prolog_to_js(+PrologFile, +JSFile)
% Main entry point: compiles a Prolog file to JavaScript
compile_prolog_to_js(PrologFile, JSFile) :-
    read_prolog_file(PrologFile, Clauses),
    translate_program(Clauses, JSCode),
    write_js_file(JSFile, JSCode).

%% read_prolog_file(+File, -Clauses)
% Reads and parses Prolog clauses from a file
read_prolog_file(File, Clauses) :-
    open(File, read, Stream),
    read_clauses(Stream, Clauses),
    close(Stream).

read_clauses(Stream, Clauses) :-
    read_term(Stream, Term, []),
    (   Term == end_of_file
    ->  Clauses = []
    ;   Clauses = [Term|Rest],
        read_clauses(Stream, Rest)
    ).

%% translate_program(+Clauses, -JSCode)
% Translates a list of Prolog clauses to JavaScript code
translate_program(Clauses, JSCode) :-
    generate_js_header(Header),
    group_clauses_by_predicate(Clauses, GroupedClauses),
    translate_predicate_groups(GroupedClauses, PredicateDefs),
    generate_js_footer(Footer),
    atomic_list_concat([Header, PredicateDefs, Footer], '\n', JSCode).

%% generate_js_header(-Header)
% Generates the JavaScript runtime library (term representation, unification, built-ins)
generate_js_header(Header) :-
    Header =
'// pl2js - Prolog to JavaScript compiled output
// Runtime library

// ---- Term constructors ----
function createVar(id) { return {type: "var", id: id}; }
function createAtom(name) { return {type: "atom", name: name}; }
function createInt(val) { return {type: "int", val: val}; }
function createCompound(functor, arity, args) {
    return {type: "compound", functor: functor, arity: arity, args: args};
}
function createList(head, tail) { return {type: "list", head: head, tail: tail}; }
function createNil() { return {type: "nil"}; }

// ---- Predicate registry for meta-calls ----
const _registry = {};
function _registerBuiltin(name, arity, fn) { _registry[name + "/" + arity] = fn; }

// ---- State management ----
function initState() {
    return {
        bindings: [],
        choiceStack: [],
        cutLevel: 0,
        failed: false,
        nextVarId: 1000,
        backtracking: false
    };
}

function pushChoicePoint(state, predId, clauseIdx, callArgs) {
    state.choiceStack.push({
        predId: predId,
        clauseIdx: clauseIdx,
        savedBindingsSize: state.bindings.length,
        callArgs: callArgs !== undefined ? callArgs : null
    });
}

function popChoicePoint(state) {
    if (state.choiceStack.length === 0) return false;
    const cp = state.choiceStack.pop();
    state.bindings = state.bindings.slice(0, cp.savedBindingsSize);
    return true;
}

function _retryBody(state, minCpDepth) {
    while (state.choiceStack.length > minCpDepth) {
        const cp = state.choiceStack[state.choiceStack.length - 1];
        /* Skip choice points that have no stored callArgs (e.g. disjunction
           markers pushed with null predId); they cannot be retried by
           re-invoking a predicate, so just discard them and keep looking. */
        if (!cp.callArgs) { state.choiceStack.pop(); continue; }
        state.bindings = state.bindings.slice(0, cp.savedBindingsSize);
        state.failed = false;
        state.backtracking = true;
        const result = cp.predId(state, ...cp.callArgs);
        if (result && !state.failed) return true;
        state.failed = false;
    }
    return false;
}

function performCut(state) {
    // Remove all choice points at or above the current cut level
    while (state.choiceStack.length > 0) {
        const cp = state.choiceStack[state.choiceStack.length - 1];
        if (typeof cp.predId === "number" ? cp.predId >= state.cutLevel : true) {
            state.choiceStack.pop();
        } else {
            break;
        }
    }
}

// ---- Dereference ----
function deref(state, term) {
    if (term.type !== "var") return term;
    for (let i = state.bindings.length - 1; i >= 0; i--) {
        if (state.bindings[i].varId === term.id) {
            return deref(state, state.bindings[i].value);
        }
    }
    return term;
}

// ---- Unification ----
function unify(state, t1, t2) {
    t1 = deref(state, t1);
    t2 = deref(state, t2);
    if (t1 === t2) return true;
    if (t1.type === "var") {
        state.bindings.push({varId: t1.id, value: t2});
        return true;
    }
    if (t2.type === "var") {
        state.bindings.push({varId: t2.id, value: t1});
        return true;
    }
    if (t1.type !== t2.type) return false;
    switch (t1.type) {
        case "atom": return t1.name === t2.name;
        case "int":  return t1.val === t2.val;
        case "nil":  return true;
        case "compound":
            if (t1.functor !== t2.functor || t1.arity !== t2.arity) return false;
            for (let i = 0; i < t1.arity; i++) {
                if (!unify(state, t1.args[i], t2.args[i])) return false;
            }
            return true;
        case "list":
            return unify(state, t1.head, t2.head) &&
                   unify(state, t1.tail, t2.tail);
        default: return false;
    }
}

// ---- Structural equality (no unification) ----
function termsEqual(t1, t2) {
    if (t1 === t2) return true;
    if (t1.type !== t2.type) return false;
    switch (t1.type) {
        case "var":  return t1.id === t2.id;
        case "atom": return t1.name === t2.name;
        case "int":  return t1.val === t2.val;
        case "nil":  return true;
        case "compound":
            if (t1.functor !== t2.functor || t1.arity !== t2.arity) return false;
            for (let i = 0; i < t1.arity; i++) {
                if (!termsEqual(t1.args[i], t2.args[i])) return false;
            }
            return true;
        case "list":
            return termsEqual(t1.head, t2.head) && termsEqual(t1.tail, t2.tail);
        default: return false;
    }
}

// ---- Arithmetic evaluation ----
function evalArithmetic(state, expr) {
    const t = deref(state, expr);
    if (t.type === "int") return t.val;
    if (t.type === "compound") {
        const f = t.functor;
        const a = t.arity;
        if (a === 2) {
            const l = evalArithmetic(state, t.args[0]);
            const r = evalArithmetic(state, t.args[1]);
            if (f === "+")   return l + r;
            if (f === "-")   return l - r;
            if (f === "*")   return l * r;
            if (f === "/")   return Math.trunc(l / r);
            if (f === "//")  return Math.trunc(l / r);
            if (f === "mod") return ((l % r) + r) % r;
            if (f === "rem") return l % r;
            if (f === "**" || f === "^") return Math.pow(l, r) | 0;
            if (f === ">>")  return l >> r;
            if (f === "<<")  return l << r;
            if (f === "/\\\\") return l & r;
            if (f === "\\\\/") return l | r;
            if (f === "xor") return l ^ r;
            if (f === "min") return Math.min(l, r);
            if (f === "max") return Math.max(l, r);
        }
        if (a === 1) {
            const v = evalArithmetic(state, t.args[0]);
            if (f === "-")        return -v;
            if (f === "+")        return v;
            if (f === "abs")      return Math.abs(v);
            if (f === "sign")     return Math.sign(v);
            if (f === "sqrt")     return Math.sqrt(v) | 0;
            if (f === "floor")    return Math.floor(v);
            if (f === "ceiling")  return Math.ceil(v);
            if (f === "round")    return Math.round(v);
            if (f === "truncate") return Math.trunc(v);
            if (f === "float_integer_part") return Math.trunc(v);
            if (f === "\\\\")       return ~v;
        }
    }
    return 0;
}

// ---- Built-in arithmetic / comparison predicates ----
function is_2(state, arg1, arg2) {
    const result = evalArithmetic(state, arg2);
    return unify(state, arg1, createInt(result));
}
function gt_2(state, arg1, arg2) {
    const t1 = deref(state, arg1); const t2 = deref(state, arg2);
    if (t1.type === "int" && t2.type === "int") return t1.val > t2.val;
    state.failed = true; return false;
}
function lt_2(state, arg1, arg2) {
    const t1 = deref(state, arg1); const t2 = deref(state, arg2);
    if (t1.type === "int" && t2.type === "int") return t1.val < t2.val;
    state.failed = true; return false;
}
function gte_2(state, arg1, arg2) {
    const t1 = deref(state, arg1); const t2 = deref(state, arg2);
    if (t1.type === "int" && t2.type === "int") return t1.val >= t2.val;
    state.failed = true; return false;
}
function lte_2(state, arg1, arg2) {
    const t1 = deref(state, arg1); const t2 = deref(state, arg2);
    if (t1.type === "int" && t2.type === "int") return t1.val <= t2.val;
    state.failed = true; return false;
}
function eq_2(state, arg1, arg2) {
    return unify(state, arg1, arg2);
}
function neq_2(state, arg1, arg2) {
    const savedSize = state.bindings.length;
    const ok = unify(state, arg1, arg2);
    state.bindings = state.bindings.slice(0, savedSize);
    return !ok;
}
function eqeq_2(state, arg1, arg2) {
    return termsEqual(deref(state, arg1), deref(state, arg2));
}
function neqeq_2(state, arg1, arg2) {
    return !eqeq_2(state, arg1, arg2);
}

// ---- Term standard order comparison ----
function termCompare(t1, t2) {
    const order = {var: 0, int: 1, atom: 2, nil: 2, compound: 3, list: 3};
    const o1 = order[t1.type] !== undefined ? order[t1.type] : 99;
    const o2 = order[t2.type] !== undefined ? order[t2.type] : 99;
    if (o1 !== o2) return o1 - o2;
    switch (t1.type) {
        case "var":  return t1.id - t2.id;
        case "int":  return t1.val - t2.val;
        case "atom": return t1.name < t2.name ? -1 : t1.name > t2.name ? 1 : 0;
        case "nil":  return 0;
        case "compound": {
            const fc = t1.functor < t2.functor ? -1 : t1.functor > t2.functor ? 1 : 0;
            if (fc !== 0) return fc;
            const ac = t1.arity - t2.arity;
            if (ac !== 0) return ac;
            for (let i = 0; i < t1.arity; i++) {
                const c = termCompare(t1.args[i], t2.args[i]);
                if (c !== 0) return c;
            }
            return 0;
        }
        case "list": {
            const hc = termCompare(t1.head, t2.head);
            return hc !== 0 ? hc : termCompare(t1.tail, t2.tail);
        }
        default: return 0;
    }
}
function term_lt_2(state, a, b)  { return termCompare(deref(state,a), deref(state,b)) <  0; }
function term_gt_2(state, a, b)  { return termCompare(deref(state,a), deref(state,b)) >  0; }
function term_lte_2(state, a, b) { return termCompare(deref(state,a), deref(state,b)) <= 0; }
function term_gte_2(state, a, b) { return termCompare(deref(state,a), deref(state,b)) >= 0; }
function compare_3(state, order, a, b) {
    const c = termCompare(deref(state,a), deref(state,b));
    const sym = c < 0 ? "<" : c > 0 ? ">" : "=";
    return unify(state, order, createAtom(sym));
}

// ---- I/O ----
let _prologOutput = "";
function _prologWrite(s) {
    if (typeof document !== "undefined") {
        _prologOutput += s;
    } else if (typeof process !== "undefined" && process.stdout) {
        process.stdout.write(s);
    }
}

function termToString(state, term) {
    term = deref(state, term);
    switch (term.type) {
        case "atom":     return term.name;
        case "int":      return String(term.val);
        case "nil":      return "[]";
        case "var":      return "_" + term.id;
        case "list": {
            const parts = [];
            let cur = term;
            while (cur.type === "list") {
                parts.push(termToString(state, cur.head));
                cur = deref(state, cur.tail);
            }
            if (cur.type !== "nil") {
                return "[" + parts.join(",") + "|" + termToString(state, cur) + "]";
            }
            return "[" + parts.join(",") + "]";
        }
        case "compound": {
            const args = term.args.map(a => termToString(state, a));
            return term.functor + "(" + args.join(",") + ")";
        }
        default: return "?";
    }
}

function write_1(state, arg1) {
    _prologWrite(termToString(state, deref(state, arg1)));
    return true;
}
function writeln_1(state, arg1) {
    _prologWrite(termToString(state, deref(state, arg1)));
    _prologWrite("\\n");
    return true;
}
function nl_0(state) { _prologWrite("\\n"); return true; }
function tab_1(state, arg1) {
    const t = deref(state, arg1);
    if (t.type !== "int") { state.failed = true; return false; }
    _prologWrite(" ".repeat(t.val));
    return true;
}
function format_2(state, arg1, arg2) {
    const fmt = deref(state, arg1);
    if (fmt.type !== "atom") { state.failed = true; return false; }
    let fmtStr = fmt.name;
    let args = arg2;
    let out = "";
    let i = 0;
    while (i < fmtStr.length) {
        if (fmtStr[i] === "~" && i + 1 < fmtStr.length) {
            const spec = fmtStr[i + 1];
            if (spec === "w") {
                args = deref(state, args);
                if (args.type === "list") {
                    out += termToString(state, args.head);
                    args = deref(state, args.tail);
                }
                i += 2;
            } else if (spec === "n") {
                out += "\\n"; i += 2;
            } else if (spec === "a") {
                args = deref(state, args);
                if (args.type === "list") {
                    out += termToString(state, args.head);
                    args = deref(state, args.tail);
                }
                i += 2;
            } else {
                out += fmtStr[i]; i++;
            }
        } else {
            out += fmtStr[i]; i++;
        }
    }
    _prologWrite(out);
    return true;
}

// ---- Type checking ----
function true_0(state) { return true; }
function fail_0(state) { state.failed = true; return false; }
function atom_1(state, arg1) { return deref(state, arg1).type === "atom"; }
function number_1(state, arg1) { return deref(state, arg1).type === "int"; }
function integer_1(state, arg1) { return deref(state, arg1).type === "int"; }
function float_1(state, arg1) { state.failed = true; return false; }
function var_1(state, arg1) { return deref(state, arg1).type === "var"; }
function nonvar_1(state, arg1) { return deref(state, arg1).type !== "var"; }
function compound_1(state, arg1) {
    const t = deref(state, arg1);
    return t.type === "compound" || t.type === "list";
}
function atomic_1(state, arg1) {
    const t = deref(state, arg1);
    return t.type === "atom" || t.type === "int" || t.type === "nil";
}
function callable_1(state, arg1) {
    const t = deref(state, arg1);
    return t.type === "atom" || t.type === "compound";
}
function is_list_1(state, arg1) {
    let t = deref(state, arg1);
    while (t.type === "list") t = deref(state, t.tail);
    return t.type === "nil";
}
function ground_1(state, arg1) {
    const t = deref(state, arg1);
    if (t.type === "var") return false;
    if (t.type === "compound") return t.args.every(a => ground_1(state, a));
    if (t.type === "list") return ground_1(state, t.head) && ground_1(state, t.tail);
    return true;
}

// ---- List predicates ----
function length_2(state, list, length) {
    let l = deref(state, list);
    let count = 0;
    while (l.type === "list") { count++; l = deref(state, l.tail); }
    if (l.type !== "nil") { state.failed = true; return false; }
    return unify(state, length, createInt(count));
}
function nth0_3(state, n, list, elem) {
    const nd = deref(state, n);
    if (nd.type !== "int") { state.failed = true; return false; }
    let l = deref(state, list);
    for (let i = 0; i < nd.val; i++) {
        if (l.type !== "list") { state.failed = true; return false; }
        l = deref(state, l.tail);
    }
    if (l.type !== "list") { state.failed = true; return false; }
    return unify(state, elem, l.head);
}
function nth1_3(state, n, list, elem) {
    const nd = deref(state, n);
    if (nd.type !== "int") { state.failed = true; return false; }
    return nth0_3(state, createInt(nd.val - 1), list, elem);
}
function last_2(state, list, last) {
    let l = deref(state, list);
    if (l.type !== "list") { state.failed = true; return false; }
    let head = l.head;
    l = deref(state, l.tail);
    while (l.type === "list") { head = l.head; l = deref(state, l.tail); }
    if (l.type !== "nil") { state.failed = true; return false; }
    return unify(state, last, head);
}
function reverse_2(state, list, reversed) {
    let l = deref(state, list);
    let result = createNil();
    while (l.type === "list") {
        result = createList(l.head, result);
        l = deref(state, l.tail);
    }
    if (l.type !== "nil") { state.failed = true; return false; }
    return unify(state, reversed, result);
}

// ---- Atom/string predicates ----
function atom_length_2(state, atom, length) {
    const a = deref(state, atom);
    if (a.type !== "atom") { state.failed = true; return false; }
    return unify(state, length, createInt(a.name.length));
}
function atom_concat_3(state, atom1, atom2, result) {
    const a1 = deref(state, atom1); const a2 = deref(state, atom2);
    if (a1.type !== "atom" || a2.type !== "atom") { state.failed = true; return false; }
    return unify(state, result, createAtom(a1.name + a2.name));
}
function atom_chars_2(state, atom, chars) {
    const a = deref(state, atom); const c = deref(state, chars);
    if (a.type === "atom") {
        let result = createNil();
        for (let i = a.name.length - 1; i >= 0; i--) {
            result = createList(createAtom(a.name[i]), result);
        }
        return unify(state, chars, result);
    } else if (c.type === "list" || c.type === "nil") {
        let s = ""; let l = c;
        while (l.type === "list") {
            const h = deref(state, l.head);
            if (h.type !== "atom") { state.failed = true; return false; }
            s += h.name; l = deref(state, l.tail);
        }
        if (l.type !== "nil") { state.failed = true; return false; }
        return unify(state, atom, createAtom(s));
    }
    state.failed = true; return false;
}
function atom_codes_2(state, atom, codes) {
    const a = deref(state, atom); const c = deref(state, codes);
    if (a.type === "atom") {
        let result = createNil();
        for (let i = a.name.length - 1; i >= 0; i--) {
            result = createList(createInt(a.name.charCodeAt(i)), result);
        }
        return unify(state, codes, result);
    } else if (c.type === "list" || c.type === "nil") {
        let s = ""; let l = c;
        while (l.type === "list") {
            const h = deref(state, l.head);
            if (h.type !== "int") { state.failed = true; return false; }
            s += String.fromCharCode(h.val); l = deref(state, l.tail);
        }
        if (l.type !== "nil") { state.failed = true; return false; }
        return unify(state, atom, createAtom(s));
    }
    state.failed = true; return false;
}
function number_codes_2(state, num, codes) {
    const n = deref(state, num);
    if (n.type === "int") {
        const s = String(n.val);
        let result = createNil();
        for (let i = s.length - 1; i >= 0; i--) {
            result = createList(createInt(s.charCodeAt(i)), result);
        }
        return unify(state, codes, result);
    }
    state.failed = true; return false;
}
function number_chars_2(state, num, chars) {
    const n = deref(state, num);
    if (n.type === "int") {
        const s = String(n.val);
        let result = createNil();
        for (let i = s.length - 1; i >= 0; i--) {
            result = createList(createAtom(s[i]), result);
        }
        return unify(state, chars, result);
    }
    state.failed = true; return false;
}
function char_code_2(state, ch, code) {
    const c = deref(state, ch); const co = deref(state, code);
    if (c.type === "atom" && c.name.length === 1) {
        return unify(state, code, createInt(c.name.charCodeAt(0)));
    }
    if (co.type === "int") {
        return unify(state, ch, createAtom(String.fromCharCode(co.val)));
    }
    state.failed = true; return false;
}

// ---- Term manipulation ----
function functor_3(state, term, functor, arity) {
    const t = deref(state, term);
    if (t.type === "compound") {
        return unify(state, functor, createAtom(t.functor)) &&
               unify(state, arity, createInt(t.arity));
    }
    if (t.type === "atom") {
        return unify(state, functor, t) && unify(state, arity, createInt(0));
    }
    if (t.type === "int") {
        return unify(state, functor, t) && unify(state, arity, createInt(0));
    }
    const f = deref(state, functor); const a = deref(state, arity);
    if (f.type === "atom" && a.type === "int") {
        if (a.val === 0) return unify(state, term, f);
        const args = Array.from({length: a.val}, (_, i) => createVar(state.nextVarId++));
        return unify(state, term, createCompound(f.name, a.val, args));
    }
    state.failed = true; return false;
}
function arg_3(state, n, term, arg) {
    const nd = deref(state, n); const t = deref(state, term);
    if (nd.type !== "int" || t.type !== "compound") { state.failed = true; return false; }
    if (nd.val < 1 || nd.val > t.arity) { state.failed = true; return false; }
    return unify(state, arg, t.args[nd.val - 1]);
}
function univ_2(state, term, list) {
    const t = deref(state, term); const l = deref(state, list);
    if (t.type !== "var") {
        if (t.type === "compound") {
            let result = createNil();
            for (let i = t.arity - 1; i >= 0; i--) result = createList(t.args[i], result);
            return unify(state, list, createList(createAtom(t.functor), result));
        }
        if (t.type === "atom" || t.type === "int") {
            return unify(state, list, createList(t, createNil()));
        }
    } else if (l.type === "list") {
        const head = deref(state, l.head);
        let tail = deref(state, l.tail);
        if (tail.type === "nil") return unify(state, term, head);
        if (head.type === "atom") {
            const argList = [];
            while (tail.type === "list") {
                argList.push(tail.head);
                tail = deref(state, tail.tail);
            }
            if (tail.type !== "nil") { state.failed = true; return false; }
            return unify(state, term, createCompound(head.name, argList.length, argList));
        }
    }
    state.failed = true; return false;
}
function copyTermHelper(state, term, varMap) {
    const t = deref(state, term);
    if (t.type === "var") {
        if (!varMap.has(t.id)) varMap.set(t.id, createVar(state.nextVarId++));
        return varMap.get(t.id);
    }
    if (t.type === "atom") return createAtom(t.name);
    if (t.type === "int")  return createInt(t.val);
    if (t.type === "nil")  return createNil();
    if (t.type === "list") {
        return createList(copyTermHelper(state, t.head, varMap),
                          copyTermHelper(state, t.tail, varMap));
    }
    if (t.type === "compound") {
        return createCompound(t.functor, t.arity,
                              t.args.map(a => copyTermHelper(state, a, varMap)));
    }
    return createVar(state.nextVarId++);
}
function copy_term_2(state, term, copy) {
    const varMap = new Map();
    return unify(state, copy, copyTermHelper(state, term, varMap));
}

// ---- Sorting ----
function sort_2(state, list, sorted) {
    let l = deref(state, list);
    const elems = [];
    while (l.type === "list") { elems.push(deref(state, l.head)); l = deref(state, l.tail); }
    if (l.type !== "nil") { state.failed = true; return false; }
    elems.sort(termCompare);
    const unique = elems.filter((e, i) => i === 0 || termCompare(e, elems[i-1]) !== 0);
    let result = createNil();
    for (let i = unique.length - 1; i >= 0; i--) result = createList(unique[i], result);
    return unify(state, sorted, result);
}
function msort_2(state, list, sorted) {
    let l = deref(state, list);
    const elems = [];
    while (l.type === "list") { elems.push(deref(state, l.head)); l = deref(state, l.tail); }
    if (l.type !== "nil") { state.failed = true; return false; }
    elems.sort(termCompare);
    let result = createNil();
    for (let i = elems.length - 1; i >= 0; i--) result = createList(elems[i], result);
    return unify(state, sorted, result);
}

// ---- Control ----
function once_1(state, goal) {
    const savedCp = state.choiceStack.length;
    const result = _callGoal(state, goal, []);
    while (state.choiceStack.length > savedCp) state.choiceStack.pop();
    return result;
}
function ignore_1(state, goal) {
    const savedCp = state.choiceStack.length;
    const savedSize = state.bindings.length;
    const result = _callGoal(state, goal, []);
    if (!result || state.failed) {
        state.bindings = state.bindings.slice(0, savedSize);
        state.failed = false;
    }
    while (state.choiceStack.length > savedCp) state.choiceStack.pop();
    return true;
}

// ---- findall helper ----
function _copyTermForFindall(outerState, innerState, term) {
    return copyTermHelper(innerState, term, new Map());
}

// ---- Public query entry point ----
function runQuery(predFn, args) {
    _prologOutput = "";
    const state = initState();
    const result = predFn(state, ...args);
    return { success: result && !state.failed, output: _prologOutput, state: state };
}

// ---- Register all built-in predicates ----
_registerBuiltin("true", 0, true_0);
_registerBuiltin("fail", 0, fail_0);
_registerBuiltin("atom", 1, atom_1);
_registerBuiltin("number", 1, number_1);
_registerBuiltin("integer", 1, integer_1);
_registerBuiltin("float", 1, float_1);
_registerBuiltin("var", 1, var_1);
_registerBuiltin("nonvar", 1, nonvar_1);
_registerBuiltin("compound", 1, compound_1);
_registerBuiltin("atomic", 1, atomic_1);
_registerBuiltin("callable", 1, callable_1);
_registerBuiltin("is_list", 1, is_list_1);
_registerBuiltin("ground", 1, ground_1);
_registerBuiltin("length", 2, length_2);
_registerBuiltin("nth0", 3, nth0_3);
_registerBuiltin("nth1", 3, nth1_3);
_registerBuiltin("last", 2, last_2);
_registerBuiltin("reverse", 2, reverse_2);
_registerBuiltin("atom_length", 2, atom_length_2);
_registerBuiltin("atom_concat", 3, atom_concat_3);
_registerBuiltin("atom_chars", 2, atom_chars_2);
_registerBuiltin("atom_codes", 2, atom_codes_2);
_registerBuiltin("number_codes", 2, number_codes_2);
_registerBuiltin("number_chars", 2, number_chars_2);
_registerBuiltin("char_code", 2, char_code_2);
_registerBuiltin("functor", 3, functor_3);
_registerBuiltin("arg", 3, arg_3);
_registerBuiltin("=..", 2, univ_2);
_registerBuiltin("copy_term", 2, copy_term_2);
_registerBuiltin("sort", 2, sort_2);
_registerBuiltin("msort", 2, msort_2);
_registerBuiltin("once", 1, once_1);
_registerBuiltin("ignore", 1, ignore_1);
_registerBuiltin("is", 2, is_2);
_registerBuiltin(">", 2, gt_2);
_registerBuiltin("<", 2, lt_2);
_registerBuiltin(">=", 2, gte_2);
_registerBuiltin("=<", 2, lte_2);
_registerBuiltin("=", 2, eq_2);
_registerBuiltin("\\=", 2, neq_2);
_registerBuiltin("==", 2, eqeq_2);
_registerBuiltin("\\==", 2, neqeq_2);
_registerBuiltin("@<", 2, term_lt_2);
_registerBuiltin("@>", 2, term_gt_2);
_registerBuiltin("@=<", 2, term_lte_2);
_registerBuiltin("@>=", 2, term_gte_2);
_registerBuiltin("compare", 3, compare_3);
_registerBuiltin("write", 1, write_1);
_registerBuiltin("writeln", 1, writeln_1);
_registerBuiltin("nl", 0, nl_0);
_registerBuiltin("tab", 1, tab_1);
_registerBuiltin("format", 2, format_2);

// ---- Meta-call support ----
function _callGoal(state, goal, extraArgs) {
    const g = deref(state, goal);
    let functor, goalArgs;
    if (g.type === "atom") { functor = g.name; goalArgs = []; }
    else if (g.type === "compound") { functor = g.functor; goalArgs = g.args.slice(); }
    else { state.failed = true; return false; }
    const allArgs = goalArgs.concat(extraArgs);
    const key = functor + "/" + allArgs.length;
    const fn = _registry[key];
    if (!fn) { state.failed = true; return false; }
    const result = fn(state, ...allArgs);
    return result && !state.failed;
}

// ---- maplist/2-5 ----
function maplist_2(state, pred, list) {
    let l = deref(state, list);
    while (l.type === "list") {
        if (!_callGoal(state, pred, [deref(state, l.head)])) { state.failed = true; return false; }
        l = deref(state, l.tail);
    }
    if (l.type !== "nil") { state.failed = true; return false; }
    return true;
}
function maplist_3(state, pred, list1, list2) {
    let l1 = deref(state, list1);
    const out = [];
    while (l1.type === "list") {
        const v = createVar(state.nextVarId++);
        if (!_callGoal(state, pred, [deref(state, l1.head), v])) { state.failed = true; return false; }
        out.push(deref(state, v));
        l1 = deref(state, l1.tail);
    }
    if (l1.type !== "nil") { state.failed = true; return false; }
    let r = createNil();
    for (let i = out.length - 1; i >= 0; i--) r = createList(out[i], r);
    return unify(state, list2, r);
}
function maplist_4(state, pred, list1, list2, list3) {
    let l1 = deref(state, list1);
    const o2 = [], o3 = [];
    while (l1.type === "list") {
        const v2 = createVar(state.nextVarId++);
        const v3 = createVar(state.nextVarId++);
        if (!_callGoal(state, pred, [deref(state, l1.head), v2, v3])) { state.failed = true; return false; }
        o2.push(deref(state, v2)); o3.push(deref(state, v3));
        l1 = deref(state, l1.tail);
    }
    if (l1.type !== "nil") { state.failed = true; return false; }
    let r2 = createNil(), r3 = createNil();
    for (let i = o2.length - 1; i >= 0; i--) { r2 = createList(o2[i], r2); r3 = createList(o3[i], r3); }
    return unify(state, list2, r2) && unify(state, list3, r3);
}
function maplist_5(state, pred, list1, list2, list3, list4) {
    let l1 = deref(state, list1);
    const o2 = [], o3 = [], o4 = [];
    while (l1.type === "list") {
        const v2 = createVar(state.nextVarId++);
        const v3 = createVar(state.nextVarId++);
        const v4 = createVar(state.nextVarId++);
        if (!_callGoal(state, pred, [deref(state, l1.head), v2, v3, v4])) { state.failed = true; return false; }
        o2.push(deref(state, v2)); o3.push(deref(state, v3)); o4.push(deref(state, v4));
        l1 = deref(state, l1.tail);
    }
    if (l1.type !== "nil") { state.failed = true; return false; }
    let r2 = createNil(), r3 = createNil(), r4 = createNil();
    for (let i = o2.length - 1; i >= 0; i--) {
        r2 = createList(o2[i], r2); r3 = createList(o3[i], r3); r4 = createList(o4[i], r4);
    }
    return unify(state, list2, r2) && unify(state, list3, r3) && unify(state, list4, r4);
}

// ---- convlist/3 ----
function convlist_3(state, pred, list, result) {
    let l = deref(state, list);
    const acc = [];
    while (l.type === "list") {
        const v = createVar(state.nextVarId++);
        const savedSize = state.bindings.length;
        const savedCp = state.choiceStack.length;
        const ok = _callGoal(state, pred, [deref(state, l.head), v]);
        if (ok) {
            acc.push(deref(state, v));
        } else {
            state.bindings = state.bindings.slice(0, savedSize);
            while (state.choiceStack.length > savedCp) state.choiceStack.pop();
            state.failed = false;
        }
        l = deref(state, l.tail);
    }
    if (l.type !== "nil") { state.failed = true; return false; }
    let res = createNil();
    for (let i = acc.length - 1; i >= 0; i--) res = createList(acc[i], res);
    return unify(state, result, res);
}

// ---- foldl/4-7 ----
function foldl_4(state, pred, list, v0, v) {
    let l = deref(state, list);
    let vi = deref(state, v0);
    while (l.type === "list") {
        const nv = createVar(state.nextVarId++);
        if (!_callGoal(state, pred, [deref(state, l.head), vi, nv])) { state.failed = true; return false; }
        vi = deref(state, nv);
        l = deref(state, l.tail);
    }
    if (l.type !== "nil") { state.failed = true; return false; }
    return unify(state, v, vi);
}
function foldl_5(state, pred, list1, list2, v0, v) {
    let l1 = deref(state, list1), l2 = deref(state, list2);
    let vi = deref(state, v0);
    while (l1.type === "list" && l2.type === "list") {
        const nv = createVar(state.nextVarId++);
        if (!_callGoal(state, pred, [deref(state, l1.head), deref(state, l2.head), vi, nv])) { state.failed = true; return false; }
        vi = deref(state, nv);
        l1 = deref(state, l1.tail); l2 = deref(state, l2.tail);
    }
    if (l1.type !== "nil" || l2.type !== "nil") { state.failed = true; return false; }
    return unify(state, v, vi);
}
function foldl_6(state, pred, list1, list2, list3, v0, v) {
    let l1 = deref(state, list1), l2 = deref(state, list2), l3 = deref(state, list3);
    let vi = deref(state, v0);
    while (l1.type === "list" && l2.type === "list" && l3.type === "list") {
        const nv = createVar(state.nextVarId++);
        if (!_callGoal(state, pred, [deref(state, l1.head), deref(state, l2.head), deref(state, l3.head), vi, nv])) { state.failed = true; return false; }
        vi = deref(state, nv);
        l1 = deref(state, l1.tail); l2 = deref(state, l2.tail); l3 = deref(state, l3.tail);
    }
    if (l1.type !== "nil" || l2.type !== "nil" || l3.type !== "nil") { state.failed = true; return false; }
    return unify(state, v, vi);
}
function foldl_7(state, pred, list1, list2, list3, list4, v0, v) {
    let l1 = deref(state, list1), l2 = deref(state, list2), l3 = deref(state, list3), l4 = deref(state, list4);
    let vi = deref(state, v0);
    while (l1.type === "list" && l2.type === "list" && l3.type === "list" && l4.type === "list") {
        const nv = createVar(state.nextVarId++);
        if (!_callGoal(state, pred, [deref(state, l1.head), deref(state, l2.head), deref(state, l3.head), deref(state, l4.head), vi, nv])) { state.failed = true; return false; }
        vi = deref(state, nv);
        l1 = deref(state, l1.tail); l2 = deref(state, l2.tail); l3 = deref(state, l3.tail); l4 = deref(state, l4.tail);
    }
    if (l1.type !== "nil" || l2.type !== "nil" || l3.type !== "nil" || l4.type !== "nil") { state.failed = true; return false; }
    return unify(state, v, vi);
}
_registerBuiltin("maplist", 2, maplist_2);
_registerBuiltin("maplist", 3, maplist_3);
_registerBuiltin("maplist", 4, maplist_4);
_registerBuiltin("maplist", 5, maplist_5);
_registerBuiltin("convlist", 3, convlist_3);
_registerBuiltin("foldl", 4, foldl_4);
_registerBuiltin("foldl", 5, foldl_5);
_registerBuiltin("foldl", 6, foldl_6);
_registerBuiltin("foldl", 7, foldl_7);

// ---- false/0, string/1 ----
function false_0(state) { state.failed = true; return false; }
function string_1(state, arg1) { return deref(state, arg1).type === "atom"; }

// ---- Negation-as-failure (\\+/1, not/1) ----
function naf_1(state, goal) {
    const savedCp = state.choiceStack.length;
    const savedBindings = state.bindings.length;
    state.failed = false;
    const ok = _callGoal(state, goal, []);
    state.bindings = state.bindings.slice(0, savedBindings);
    while (state.choiceStack.length > savedCp) state.choiceStack.pop();
    if (ok && !state.failed) { state.failed = true; return false; }
    state.failed = false;
    return true;
}

// ---- call/1-8 ----
function call_1(state, goal) { return _callGoal(state, goal, []); }
function call_2(state, goal, a1) { return _callGoal(state, goal, [a1]); }
function call_3(state, goal, a1, a2) { return _callGoal(state, goal, [a1, a2]); }
function call_4(state, goal, a1, a2, a3) { return _callGoal(state, goal, [a1, a2, a3]); }
function call_5(state, goal, a1, a2, a3, a4) { return _callGoal(state, goal, [a1, a2, a3, a4]); }
function call_6(state, goal, a1, a2, a3, a4, a5) { return _callGoal(state, goal, [a1, a2, a3, a4, a5]); }
function call_7(state, goal, a1, a2, a3, a4, a5, a6) { return _callGoal(state, goal, [a1, a2, a3, a4, a5, a6]); }
function call_8(state, goal, a1, a2, a3, a4, a5, a6, a7) { return _callGoal(state, goal, [a1, a2, a3, a4, a5, a6, a7]); }

// ---- succ/2, plus/3, between/3, succ_or_zero/2 ----
function succ_2(state, x, y) {
    const t = deref(state, x); const t2 = deref(state, y);
    if (t.type === "int" && t.val >= 0) return unify(state, y, createInt(t.val + 1));
    if (t2.type === "int" && t2.val > 0) return unify(state, x, createInt(t2.val - 1));
    state.failed = true; return false;
}
function plus_3(state, x, y, z) {
    const t1 = deref(state, x); const t2 = deref(state, y); const t3 = deref(state, z);
    if (t1.type === "int" && t2.type === "int") return unify(state, z, createInt(t1.val + t2.val));
    if (t1.type === "int" && t3.type === "int") return unify(state, y, createInt(t3.val - t1.val));
    if (t2.type === "int" && t3.type === "int") return unify(state, x, createInt(t3.val - t2.val));
    state.failed = true; return false;
}
function between_3(state, lo, hi, x) {
    const l = deref(state, lo); const h = deref(state, hi);
    if (l.type !== "int" || h.type !== "int") { state.failed = true; return false; }
    let start;
    const _top = state.choiceStack.length > 0 ? state.choiceStack[state.choiceStack.length - 1] : null;
    if (state.backtracking && _top && _top.predId === between_3) {
        start = _top.clauseIdx;
        popChoicePoint(state);
        state.backtracking = false;
    } else {
        start = l.val;
    }
    if (start > h.val) { state.failed = true; return false; }
    if (start < h.val) pushChoicePoint(state, between_3, start + 1, null);
    return unify(state, x, createInt(start));
}
function succ_or_zero_2(state, x, y) {
    const t = deref(state, x);
    if (t.type === "int") return unify(state, y, createInt(t.val > 0 ? t.val - 1 : 0));
    state.failed = true; return false;
}

// ---- New type converters ----
function atom_number_2(state, atom, num) {
    const a = deref(state, atom); const n = deref(state, num);
    if (a.type === "atom") {
        const v = Number(a.name);
        if (isNaN(v)) { state.failed = true; return false; }
        return unify(state, num, createInt(Math.trunc(v)));
    }
    if (n.type === "int") return unify(state, atom, createAtom(String(n.val)));
    state.failed = true; return false;
}
function atom_string_2(state, atom, str) {
    const a = deref(state, atom); const s = deref(state, str);
    if (a.type === "atom" || a.type === "int")
        return unify(state, str, createAtom(a.type === "atom" ? a.name : String(a.val)));
    if (s.type === "atom") return unify(state, atom, s);
    state.failed = true; return false;
}
function number_string_2(state, num, str) {
    const n = deref(state, num); const s = deref(state, str);
    if (n.type === "int") return unify(state, str, createAtom(String(n.val)));
    if (s.type === "atom") {
        const v = Number(s.name);
        if (isNaN(v)) { state.failed = true; return false; }
        return unify(state, num, createInt(Math.trunc(v)));
    }
    state.failed = true; return false;
}
function term_to_atom_2(state, term, atom) {
    const t = deref(state, term); const a = deref(state, atom);
    if (t.type !== "var") return unify(state, atom, createAtom(termToString(state, t)));
    if (a.type === "atom") {
        const n = Number(a.name);
        if (!isNaN(n) && Number.isInteger(n)) return unify(state, term, createInt(n));
        return unify(state, term, createAtom(a.name));
    }
    state.failed = true; return false;
}
function term_string_2(state, term, str) { return term_to_atom_2(state, term, str); }
function upcase_atom_2(state, atom, upper) {
    const a = deref(state, atom);
    if (a.type !== "atom") { state.failed = true; return false; }
    return unify(state, upper, createAtom(a.name.toUpperCase()));
}
function downcase_atom_2(state, atom, lower) {
    const a = deref(state, atom);
    if (a.type !== "atom") { state.failed = true; return false; }
    return unify(state, lower, createAtom(a.name.toLowerCase()));
}
function string_to_atom_2(state, str, atom) {
    const s = deref(state, str); const a = deref(state, atom);
    if (s.type === "atom") return unify(state, atom, s);
    if (a.type === "atom" || a.type === "int")
        return unify(state, str, createAtom(a.type === "atom" ? a.name : String(a.val)));
    state.failed = true; return false;
}
function string_concat_3(state, s1, s2, result) {
    const a = deref(state, s1); const b = deref(state, s2);
    if (a.type !== "atom" || b.type !== "atom") { state.failed = true; return false; }
    return unify(state, result, createAtom(a.name + b.name));
}
function string_length_2(state, str, length) {
    const s = deref(state, str);
    if (s.type !== "atom") { state.failed = true; return false; }
    return unify(state, length, createInt(s.name.length));
}
function string_codes_2(state, str, codes) {
    const s = deref(state, str); const c = deref(state, codes);
    if (s.type === "atom") {
        let result = createNil();
        for (let i = s.name.length - 1; i >= 0; i--)
            result = createList(createInt(s.name.charCodeAt(i)), result);
        return unify(state, codes, result);
    }
    if (c.type === "list" || c.type === "nil") {
        let str2 = ""; let lc = c;
        while (lc.type === "list") {
            const h = deref(state, lc.head);
            if (h.type !== "int") { state.failed = true; return false; }
            str2 += String.fromCharCode(h.val); lc = deref(state, lc.tail);
        }
        return unify(state, str, createAtom(str2));
    }
    state.failed = true; return false;
}
function string_chars_2(state, str, chars) {
    const s = deref(state, str); const c = deref(state, chars);
    if (s.type === "atom") {
        let result = createNil();
        for (let i = s.name.length - 1; i >= 0; i--)
            result = createList(createAtom(s.name[i]), result);
        return unify(state, chars, result);
    }
    if (c.type === "list" || c.type === "nil") {
        let str2 = ""; let lc = c;
        while (lc.type === "list") {
            const h = deref(state, lc.head);
            if (h.type !== "atom") { state.failed = true; return false; }
            str2 += h.name; lc = deref(state, lc.tail);
        }
        return unify(state, str, createAtom(str2));
    }
    state.failed = true; return false;
}
function atomic_list_concat_2(state, list, result) {
    let l = deref(state, list); let s = "";
    while (l.type === "list") {
        const d = deref(state, l.head);
        if (d.type === "atom") s += d.name;
        else if (d.type === "int") s += String(d.val);
        else { state.failed = true; return false; }
        l = deref(state, l.tail);
    }
    if (l.type !== "nil") { state.failed = true; return false; }
    return unify(state, result, createAtom(s));
}
function atomic_list_concat_3(state, list, sep, result) {
    const listT = deref(state, list); const sepT = deref(state, sep); const resultT = deref(state, result);
    if (listT.type === "list" || listT.type === "nil") {
        const sepStr = sepT.type === "atom" ? sepT.name : (sepT.type === "int" ? String(sepT.val) : "");
        let l = listT; const parts = [];
        while (l.type === "list") {
            const d = deref(state, l.head);
            if (d.type === "atom") parts.push(d.name);
            else if (d.type === "int") parts.push(String(d.val));
            else { state.failed = true; return false; }
            l = deref(state, l.tail);
        }
        return unify(state, result, createAtom(parts.join(sepStr)));
    }
    if (resultT.type === "atom" && (sepT.type === "atom" || sepT.type === "int")) {
        const sepStr = sepT.type === "atom" ? sepT.name : String(sepT.val);
        const parts = sepStr === "" ? resultT.name.split("") : resultT.name.split(sepStr);
        let res = createNil();
        for (let i = parts.length - 1; i >= 0; i--) res = createList(createAtom(parts[i]), res);
        return unify(state, list, res);
    }
    state.failed = true; return false;
}
function writeq_1(state, arg1) { _prologWrite(termToString(state, deref(state, arg1))); return true; }
function write_term_2(state, arg1, _opts) { _prologWrite(termToString(state, deref(state, arg1))); return true; }
function print_1(state, arg1) { _prologWrite(termToString(state, deref(state, arg1))); return true; }
function format_1(state, fmt) {
    const f = deref(state, fmt);
    if (f.type !== "atom") { state.failed = true; return false; }
    let out = "";
    for (let i = 0; i < f.name.length; i++) {
        if (f.name[i] === "~" && i + 1 < f.name.length) {
            const spec = f.name[i + 1]; i++;
            if (spec === "n") out += String.fromCharCode(10);
            else if (spec === "~") out += "~";
            else out += "~" + spec;
        } else { out += f.name[i]; }
    }
    _prologWrite(out); return true;
}
function char_type_2(state, ch, type) {
    const c = deref(state, ch); const tp = deref(state, type);
    if (c.type !== "atom" || c.name.length !== 1) { state.failed = true; return false; }
    const code = c.name.charCodeAt(0);
    const typeName = tp.type === "atom" ? tp.name : (tp.type === "compound" ? tp.functor : "");
    if (typeName === "alpha") return (code >= 65 && code <= 90) || (code >= 97 && code <= 122) ? true : (state.failed = true, false);
    if (typeName === "alnum") return (code >= 48 && code <= 57) || (code >= 65 && code <= 90) || (code >= 97 && code <= 122) ? true : (state.failed = true, false);
    if (typeName === "digit") {
        if (tp.type === "compound" && tp.arity === 1)
            return (code >= 48 && code <= 57) ? unify(state, tp.args[0], createInt(code - 48)) : (state.failed = true, false);
        return (code >= 48 && code <= 57) ? true : (state.failed = true, false);
    }
    if (typeName === "space" || typeName === "white") return (code === 32 || code === 9 || code === 10 || code === 13) ? true : (state.failed = true, false);
    if (typeName === "upper") return (code >= 65 && code <= 90) ? true : (state.failed = true, false);
    if (typeName === "lower") return (code >= 97 && code <= 122) ? true : (state.failed = true, false);
    if (typeName === "ascii") return (code >= 0 && code <= 127) ? true : (state.failed = true, false);
    state.failed = true; return false;
}

// ---- List predicates ----
function flatten_2(state, list, flat) {
    function flatHelper(t) {
        t = deref(state, t);
        if (t.type === "nil") return [];
        if (t.type === "list") {
            const h = deref(state, t.head);
            if (h.type === "list" || h.type === "nil")
                return flatHelper(h).concat(flatHelper(deref(state, t.tail)));
            return [h].concat(flatHelper(deref(state, t.tail)));
        }
        return [t];
    }
    const elems = flatHelper(deref(state, list));
    let res = createNil();
    for (let i = elems.length - 1; i >= 0; i--) res = createList(elems[i], res);
    return unify(state, flat, res);
}
function max_list_2(state, list, max) {
    let l = deref(state, list); const vals = [];
    while (l.type === "list") {
        const h = deref(state, l.head);
        if (h.type !== "int") { state.failed = true; return false; }
        vals.push(h.val); l = deref(state, l.tail);
    }
    if (vals.length === 0) { state.failed = true; return false; }
    return unify(state, max, createInt(Math.max(...vals)));
}
function min_list_2(state, list, min) {
    let l = deref(state, list); const vals = [];
    while (l.type === "list") {
        const h = deref(state, l.head);
        if (h.type !== "int") { state.failed = true; return false; }
        vals.push(h.val); l = deref(state, l.tail);
    }
    if (vals.length === 0) { state.failed = true; return false; }
    return unify(state, min, createInt(Math.min(...vals)));
}
function sum_list_2(state, list, sum) {
    let l = deref(state, list); let total = 0;
    while (l.type === "list") {
        const h = deref(state, l.head);
        if (h.type !== "int") { state.failed = true; return false; }
        total += h.val; l = deref(state, l.tail);
    }
    return unify(state, sum, createInt(total));
}
function numlist_3(state, lo, hi, list) {
    const l = deref(state, lo); const h = deref(state, hi);
    if (l.type !== "int" || h.type !== "int") { state.failed = true; return false; }
    let res = createNil();
    for (let i = h.val; i >= l.val; i--) res = createList(createInt(i), res);
    return unify(state, list, res);
}
function list_to_set_2(state, list, set) {
    let l = deref(state, list); const seen = []; const result = [];
    while (l.type === "list") {
        const h = deref(state, l.head);
        if (!seen.some(s => termsEqual(s, h))) { seen.push(h); result.push(h); }
        l = deref(state, l.tail);
    }
    let res = createNil();
    for (let i = result.length - 1; i >= 0; i--) res = createList(result[i], res);
    return unify(state, set, res);
}
function select_3(state, elem, list, rest) {
    let startIdx = 0;
    const _top = state.choiceStack.length > 0 ? state.choiceStack[state.choiceStack.length - 1] : null;
    if (state.backtracking && _top && _top.predId === select_3) {
        startIdx = _top.clauseIdx;
        popChoicePoint(state);
        state.backtracking = false;
    }
    const elems = [];
    let cur = deref(state, list);
    while (cur.type === "list") { elems.push(deref(state, cur.head)); cur = deref(state, cur.tail); }
    if (startIdx >= elems.length) { state.failed = true; return false; }
    if (startIdx + 1 < elems.length) pushChoicePoint(state, select_3, startIdx + 1, null);
    if (!unify(state, elem, elems[startIdx])) { state.failed = true; return false; }
    const restElems = elems.filter((_, i) => i !== startIdx);
    let restList = createNil();
    for (let i = restElems.length - 1; i >= 0; i--) restList = createList(restElems[i], restList);
    return unify(state, rest, restList);
}
function subtract_3(state, set, del, result) {
    let s = deref(state, set); let d = deref(state, del); const delE = [];
    while (d.type === "list") { delE.push(deref(state, d.head)); d = deref(state, d.tail); }
    const res_arr = [];
    while (s.type === "list") {
        const h = deref(state, s.head);
        if (!delE.some(e => termsEqual(h, e))) res_arr.push(h);
        s = deref(state, s.tail);
    }
    let res = createNil();
    for (let i = res_arr.length - 1; i >= 0; i--) res = createList(res_arr[i], res);
    return unify(state, result, res);
}
function intersection_3(state, set1, set2, result) {
    let s1 = deref(state, set1); let tmp = deref(state, set2); const s2e = [];
    while (tmp.type === "list") { s2e.push(deref(state, tmp.head)); tmp = deref(state, tmp.tail); }
    const res_arr = [];
    while (s1.type === "list") {
        const h = deref(state, s1.head);
        if (s2e.some(e => termsEqual(h, e))) res_arr.push(h);
        s1 = deref(state, s1.tail);
    }
    let res = createNil();
    for (let i = res_arr.length - 1; i >= 0; i--) res = createList(res_arr[i], res);
    return unify(state, result, res);
}
function union_3(state, set1, set2, result) {
    let s1 = deref(state, set1); let s2 = deref(state, set2); const res_arr = [];
    while (s1.type === "list") { res_arr.push(deref(state, s1.head)); s1 = deref(state, s1.tail); }
    while (s2.type === "list") {
        const h = deref(state, s2.head);
        if (!res_arr.some(e => termsEqual(h, e))) res_arr.push(h);
        s2 = deref(state, s2.tail);
    }
    let res = createNil();
    for (let i = res_arr.length - 1; i >= 0; i--) res = createList(res_arr[i], res);
    return unify(state, result, res);
}
function delete_3(state, list, elem, result) {
    let l = deref(state, list); const e = deref(state, elem); const res_arr = [];
    while (l.type === "list") {
        const h = deref(state, l.head);
        if (!termsEqual(h, e)) res_arr.push(h);
        l = deref(state, l.tail);
    }
    let res = createNil();
    for (let i = res_arr.length - 1; i >= 0; i--) res = createList(res_arr[i], res);
    return unify(state, result, res);
}
function permutation_2(state, list, perm) {
    let l = deref(state, list); const elems = [];
    while (l.type === "list") { elems.push(deref(state, l.head)); l = deref(state, l.tail); }
    let startPerm = 0;
    const _top = state.choiceStack.length > 0 ? state.choiceStack[state.choiceStack.length - 1] : null;
    if (state.backtracking && _top && _top.predId === permutation_2) {
        startPerm = _top.clauseIdx;
        popChoicePoint(state);
        state.backtracking = false;
    }
    const allPerms = [];
    (function genPerms(arr, cur) {
        if (arr.length === 0) { allPerms.push(cur.slice()); return; }
        for (let i = 0; i < arr.length; i++) {
            cur.push(arr[i]);
            genPerms(arr.filter((_, idx) => idx !== i), cur);
            cur.pop();
        }
    })(elems, []);
    if (startPerm >= allPerms.length) { state.failed = true; return false; }
    if (startPerm + 1 < allPerms.length) pushChoicePoint(state, permutation_2, startPerm + 1, null);
    let res = createNil();
    for (let i = allPerms[startPerm].length - 1; i >= 0; i--) res = createList(allPerms[startPerm][i], res);
    return unify(state, perm, res);
}

// ---- findall/3, forall/2, aggregate_all/3 ----
function findall_3(state, template, goal, result) {
    const solutions = [];
    const outerBindings = state.bindings.length;
    const outerCp = state.choiceStack.length;
    state.backtracking = false; state.failed = false;
    let ok = _callGoal(state, goal, []);
    while (ok && !state.failed) {
        solutions.push(copyTermHelper(state, template, new Map()));
        state.bindings = state.bindings.slice(0, outerBindings);
        if (state.choiceStack.length <= outerCp) break;
        state.backtracking = true; state.failed = false;
        ok = _callGoal(state, goal, []);
    }
    while (state.choiceStack.length > outerCp) state.choiceStack.pop();
    state.bindings = state.bindings.slice(0, outerBindings);
    state.failed = false; state.backtracking = false;
    let res = createNil();
    for (let i = solutions.length - 1; i >= 0; i--) res = createList(solutions[i], res);
    return unify(state, result, res);
}
function forall_2(state, cond, action) {
    const savedCp = state.choiceStack.length;
    const savedBindings = state.bindings.length;
    state.backtracking = false; state.failed = false;
    let condOk = _callGoal(state, cond, []);
    while (condOk && !state.failed) {
        const afterCondCp = state.choiceStack.length;
        const afterCondBindings = state.bindings.length;
        const actionOk = _callGoal(state, action, []);
        const actionFailed = !actionOk || state.failed;
        state.bindings = state.bindings.slice(0, afterCondBindings);
        while (state.choiceStack.length > afterCondCp) state.choiceStack.pop();
        state.failed = false;
        if (actionFailed) {
            state.bindings = state.bindings.slice(0, savedBindings);
            while (state.choiceStack.length > savedCp) state.choiceStack.pop();
            state.failed = true; return false;
        }
        state.bindings = state.bindings.slice(0, savedBindings);
        if (state.choiceStack.length <= savedCp) break;
        state.backtracking = true; state.failed = false;
        condOk = _callGoal(state, cond, []);
    }
    while (state.choiceStack.length > savedCp) state.choiceStack.pop();
    state.bindings = state.bindings.slice(0, savedBindings);
    state.failed = false; return true;
}
function aggregate_all_3(state, aggType, goal, result) {
    const agg = deref(state, aggType);
    if (agg.type === "atom" && agg.name === "count") {
        const outerBindings = state.bindings.length;
        const outerCp = state.choiceStack.length;
        let count = 0;
        state.backtracking = false; state.failed = false;
        let ok = _callGoal(state, goal, []);
        while (ok && !state.failed) {
            count++;
            state.bindings = state.bindings.slice(0, outerBindings);
            if (state.choiceStack.length <= outerCp) break;
            state.backtracking = true; state.failed = false;
            ok = _callGoal(state, goal, []);
        }
        while (state.choiceStack.length > outerCp) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, outerBindings);
        state.failed = false; state.backtracking = false;
        return unify(state, result, createInt(count));
    }
    state.failed = true; return false;
}

// ---- include/3, exclude/3 ----
function include_3(state, pred, list, filtered) {
    let l = deref(state, list); const result = [];
    while (l.type === "list") {
        const h = deref(state, l.head);
        const savedCp = state.choiceStack.length;
        const savedBindings = state.bindings.length;
        state.failed = false;
        const ok = _callGoal(state, pred, [h]);
        if (ok && !state.failed) result.push(h);
        state.bindings = state.bindings.slice(0, savedBindings);
        while (state.choiceStack.length > savedCp) state.choiceStack.pop();
        state.failed = false;
        l = deref(state, l.tail);
    }
    let res = createNil();
    for (let i = result.length - 1; i >= 0; i--) res = createList(result[i], res);
    return unify(state, filtered, res);
}
function exclude_3(state, pred, list, filtered) {
    let l = deref(state, list); const result = [];
    while (l.type === "list") {
        const h = deref(state, l.head);
        const savedCp = state.choiceStack.length;
        const savedBindings = state.bindings.length;
        state.failed = false;
        const ok = _callGoal(state, pred, [h]);
        const included = ok && !state.failed;
        state.bindings = state.bindings.slice(0, savedBindings);
        while (state.choiceStack.length > savedCp) state.choiceStack.pop();
        state.failed = false;
        if (!included) result.push(h);
        l = deref(state, l.tail);
    }
    let res = createNil();
    for (let i = result.length - 1; i >= 0; i--) res = createList(result[i], res);
    return unify(state, filtered, res);
}
_registerBuiltin("false", 0, false_0);
_registerBuiltin("string", 1, string_1);
_registerBuiltin("\\\\+", 1, naf_1); /* "\\\\+" in Prolog source = "\\+" in JS = the 2-char key \+ */
_registerBuiltin("not", 1, naf_1);
_registerBuiltin("call", 1, call_1);
_registerBuiltin("call", 2, call_2);
_registerBuiltin("call", 3, call_3);
_registerBuiltin("call", 4, call_4);
_registerBuiltin("call", 5, call_5);
_registerBuiltin("call", 6, call_6);
_registerBuiltin("call", 7, call_7);
_registerBuiltin("call", 8, call_8);
_registerBuiltin("succ", 2, succ_2);
_registerBuiltin("plus", 3, plus_3);
_registerBuiltin("between", 3, between_3);
_registerBuiltin("succ_or_zero", 2, succ_or_zero_2);
_registerBuiltin("atom_number", 2, atom_number_2);
_registerBuiltin("atom_string", 2, atom_string_2);
_registerBuiltin("number_string", 2, number_string_2);
_registerBuiltin("term_to_atom", 2, term_to_atom_2);
_registerBuiltin("term_string", 2, term_string_2);
_registerBuiltin("upcase_atom", 2, upcase_atom_2);
_registerBuiltin("downcase_atom", 2, downcase_atom_2);
_registerBuiltin("string_to_atom", 2, string_to_atom_2);
_registerBuiltin("string_concat", 3, string_concat_3);
_registerBuiltin("string_length", 2, string_length_2);
_registerBuiltin("string_codes", 2, string_codes_2);
_registerBuiltin("string_chars", 2, string_chars_2);
_registerBuiltin("atomic_list_concat", 2, atomic_list_concat_2);
_registerBuiltin("atomic_list_concat", 3, atomic_list_concat_3);
_registerBuiltin("writeq", 1, writeq_1);
_registerBuiltin("write_term", 2, write_term_2);
_registerBuiltin("print", 1, print_1);
_registerBuiltin("format", 1, format_1);
_registerBuiltin("char_type", 2, char_type_2);
_registerBuiltin("flatten", 2, flatten_2);
_registerBuiltin("max_list", 2, max_list_2);
_registerBuiltin("min_list", 2, min_list_2);
_registerBuiltin("sum_list", 2, sum_list_2);
_registerBuiltin("numlist", 3, numlist_3);
_registerBuiltin("list_to_set", 2, list_to_set_2);
_registerBuiltin("select", 3, select_3);
_registerBuiltin("subtract", 3, subtract_3);
_registerBuiltin("intersection", 3, intersection_3);
_registerBuiltin("union", 3, union_3);
_registerBuiltin("delete", 3, delete_3);
_registerBuiltin("permutation", 2, permutation_2);
_registerBuiltin("findall", 3, findall_3);
_registerBuiltin("forall", 2, forall_2);
_registerBuiltin("aggregate_all", 3, aggregate_all_3);
_registerBuiltin("include", 3, include_3);
_registerBuiltin("exclude", 3, exclude_3);

// End of runtime library
'.

%% group_clauses_by_predicate(+Clauses, -GroupedClauses)
% Groups clauses by their predicate name/arity
group_clauses_by_predicate([], []).
group_clauses_by_predicate(Clauses, Grouped) :-
    Clauses \= [],
    collect_predicate_signatures(Clauses, Signatures),
    group_by_signature(Signatures, Clauses, Grouped).

collect_predicate_signatures([], []).
collect_predicate_signatures([Clause|Rest], [Sig|Sigs]) :-
    clause_signature(Clause, Sig),
    collect_predicate_signatures(Rest, Sigs).

clause_signature((Head :- _), Name/Arity) :-
    !,
    extract_predicate_info(Head, Name, Arity, _).
clause_signature(Head, Name/Arity) :-
    extract_predicate_info(Head, Name, Arity, _).

group_by_signature([], [], []).
group_by_signature(Sigs, Clauses, [Group|RestGroups]) :-
    Sigs \= [],
    Sigs = [FirstSig|_],
    collect_matching_clauses(FirstSig, Sigs, Clauses, MatchingClauses, RemainingClauses, RemainingSigs),
    Group = FirstSig-MatchingClauses,
    group_by_signature(RemainingSigs, RemainingClauses, RestGroups).

collect_matching_clauses(_, [], [], [], [], []).
collect_matching_clauses(TargetSig, [Sig|Sigs], [Clause|Clauses], [Clause|Matching], Remaining, RemainingSigs) :-
    Sig = TargetSig,
    !,
    collect_matching_clauses(TargetSig, Sigs, Clauses, Matching, Remaining, RemainingSigs).
collect_matching_clauses(TargetSig, [Sig|Sigs], [Clause|Clauses], Matching, [Clause|Remaining], [Sig|RemainingSigs]) :-
    collect_matching_clauses(TargetSig, Sigs, Clauses, Matching, Remaining, RemainingSigs).

%% translate_predicate_groups(+Groups, -JSCode)
translate_predicate_groups([], '').
translate_predicate_groups([Group|Rest], JSCode) :-
    translate_predicate_group(Group, GroupCode),
    translate_predicate_groups(Rest, RestCode),
    atomic_list_concat([GroupCode, RestCode], '\n', JSCode).

%% translate_predicate_group(+Group, -JSCode)
translate_predicate_group(Name/Arity-Clauses, FinalCode) :-
    Clauses = [FirstClause|_],
    clause_head(FirstClause, Head),
    extract_predicate_info(Head, _, _, Args),
    translate_args_to_params(Args, Params),
    sanitize_predicate_name(Name, SanitizedName),
    format(atom(FuncName), '~w_~w', [SanitizedName, Arity]),
    length(Clauses, NumClauses),
    ( NumClauses > 1 ->
        translate_nondeterministic_predicate(Clauses, FuncName, Params, Arity, FuncCode)
    ;
        translate_predicate_clauses(Clauses, 1, ClausesCode),
        format(atom(FuncCode),
'function ~w(state~w) {
~w
    return false; /* No clause matched */
}', [FuncName, Params, ClausesCode])
    ),
    format(atom(RegLine), '\n_registry["~w/~w"] = ~w;', [Name, Arity, FuncName]),
    atom_concat(FuncCode, RegLine, FinalCode).

%% translate_nondeterministic_predicate(+Clauses, +FuncName, +Params, +Arity, -JSCode)
translate_nondeterministic_predicate(Clauses, FuncName, Params, Arity, JSCode) :-
    length(Clauses, NumClauses),
    generate_args_array(Arity, ArgsArr),
    translate_predicate_clauses_with_choicepoints(Clauses, FuncName, 1, NumClauses, ArgsArr, ClausesCode),
    format(atom(JSCode),
'function ~w(state~w) {
    /* Check if resuming from a choice point (only when backtracking) */
    let startClause = 1;
    const _top = state.choiceStack.length > 0
        ? state.choiceStack[state.choiceStack.length - 1] : null;
    if (state.backtracking && _top && _top.predId === ~w) {
        startClause = _top.clauseIdx;
        popChoicePoint(state);
        /* Reset backtracking flag so inner calls start fresh */
        state.backtracking = false;
        /* Check for sentinel - all clauses exhausted */
        if (startClause >= 9999) {
            state.failed = true;
            return false;
        }
    }

~w
    return false; /* No clause matched */
}', [FuncName, Params, FuncName, ClausesCode]).

%% translate_predicate_clauses_with_choicepoints(+Clauses, +FuncName, +Index, +Total, +ArgsArr, -JSCode)
translate_predicate_clauses_with_choicepoints([], _, _, _, _, '').
translate_predicate_clauses_with_choicepoints([Clause|Rest], FuncName, Index, Total, ArgsArr, JSCode) :-
    NextIndex is Index + 1,
    ( NextIndex > Total -> IsLast = true ; IsLast = false ),
    translate_single_clause_with_choicepoint(Clause, FuncName, Index, IsLast, ArgsArr, ClauseCode),
    translate_predicate_clauses_with_choicepoints(Rest, FuncName, NextIndex, Total, ArgsArr, RestCode),
    atomic_list_concat([ClauseCode, RestCode], '', JSCode).

%% translate_single_clause_with_choicepoint(+Clause, +FuncName, +Index, +IsLast, +ArgsArr, -JSCode)
translate_single_clause_with_choicepoint((Head :- Body), FuncName, Index, IsLast, ArgsArr, JSCode) :-
    !,
    term_variables((Head, Body), AllVars),
    create_var_map(AllVars),
    setup_call_cleanup(
        true,
        (
            generate_var_declarations(AllVars, VarDecls),
            translate_head_unifications_with_check(Head, Index, HeadCode),
            translate_body(Body, BodyCode, 0),
            copy_term((Head, Body), (HeadDisp, BodyDisp)),
            numbervars((HeadDisp, BodyDisp), 0, _),
            NextIndex is Index + 1,
            ( IsLast ->
                format(atom(JSCode),
'    /* Clause ~w: ~w :- ~w */
    if (startClause <= ~w) {
        const _cpDepth~w = state.choiceStack.length;
        const _savedBindingsSize~w = state.bindings.length;
        /* Push sentinel choice point before trying last clause */
        pushChoicePoint(state, ~w, 9999, ~w);
        const _bodyCp = state.choiceStack.length;
~w~w
            do {
~w            } while (false);
            if (!state.failed) return true;
        }
        /* Clause failed: pop all CPs pushed during this attempt */
        while (state.choiceStack.length > _cpDepth~w) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize~w);
        state.failed = false;
    }
', [Index, HeadDisp, BodyDisp, Index, Index, Index, FuncName, ArgsArr, VarDecls, HeadCode, BodyCode, Index, Index])
            ;
                format(atom(JSCode),
'    /* Clause ~w: ~w :- ~w */
    if (startClause <= ~w) {
        const _cpDepth~w = state.choiceStack.length;
        const _savedBindingsSize~w = state.bindings.length;
        /* Push choice point for next clause before trying this one */
        pushChoicePoint(state, ~w, ~w, ~w);
        const _bodyCp = state.choiceStack.length;
~w~w
            do {
~w            } while (false);
            if (!state.failed) return true;
        }
        /* Clause failed: pop all CPs pushed during this attempt */
        while (state.choiceStack.length > _cpDepth~w) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize~w);
        state.failed = false;
    }
', [Index, HeadDisp, BodyDisp, Index, Index, Index, FuncName, NextIndex, ArgsArr, VarDecls, HeadCode, BodyCode, Index, Index])
            )
        ),
        b_setval(pl2js_clause_vars, [])
    ).

translate_single_clause_with_choicepoint(Head, FuncName, Index, IsLast, ArgsArr, JSCode) :-
    % Fact (clause without body)
    term_variables(Head, AllVars),
    create_var_map(AllVars),
    setup_call_cleanup(
        true,
        (
            generate_var_declarations(AllVars, VarDecls),
            translate_head_unifications_with_check(Head, Index, HeadCode),
            copy_term(Head, HeadDisp),
            numbervars(HeadDisp, 0, _),
            NextIndex is Index + 1,
            ( IsLast ->
                format(atom(JSCode),
'    /* Clause ~w: ~w */
    if (startClause <= ~w) {
        const _cpDepth~w = state.choiceStack.length;
        const _savedBindingsSize~w = state.bindings.length;
        /* Push sentinel choice point before trying last clause */
        pushChoicePoint(state, ~w, 9999, ~w);
~w~w
            return true;
        }
        /* Clause failed: pop all CPs pushed during this attempt */
        while (state.choiceStack.length > _cpDepth~w) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize~w);
        state.failed = false;
    }
', [Index, HeadDisp, Index, Index, Index, FuncName, ArgsArr, VarDecls, HeadCode, Index, Index])
            ;
                format(atom(JSCode),
'    /* Clause ~w: ~w */
    if (startClause <= ~w) {
        const _cpDepth~w = state.choiceStack.length;
        const _savedBindingsSize~w = state.bindings.length;
        /* Push choice point for next clause before trying this one */
        pushChoicePoint(state, ~w, ~w, ~w);
~w~w
            return true;
        }
        /* Clause failed: pop all CPs pushed during this attempt */
        while (state.choiceStack.length > _cpDepth~w) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize~w);
        state.failed = false;
    }
', [Index, HeadDisp, Index, Index, Index, FuncName, NextIndex, ArgsArr, VarDecls, HeadCode, Index, Index])
            )
        ),
        b_setval(pl2js_clause_vars, [])
    ).

clause_head((Head :- _), Head) :- !.
clause_head(Head, Head).

%% sanitize_predicate_name(+Name, -SanitizedName)
sanitize_predicate_name('>', 'gt') :- !.
sanitize_predicate_name('<', 'lt') :- !.
sanitize_predicate_name('>=', 'gte') :- !.
sanitize_predicate_name('=<', 'lte') :- !.
sanitize_predicate_name('=', 'eq') :- !.
sanitize_predicate_name('==', 'eqeq') :- !.
sanitize_predicate_name('\\=', 'neq') :- !.
sanitize_predicate_name('\\==', 'neqeq') :- !.
sanitize_predicate_name('is', 'is') :- !.
sanitize_predicate_name('+', 'plus') :- !.
sanitize_predicate_name('-', 'minus') :- !.
sanitize_predicate_name('*', 'times') :- !.
sanitize_predicate_name('/', 'div') :- !.
sanitize_predicate_name('//', 'intdiv') :- !.
sanitize_predicate_name('mod', 'mod') :- !.
sanitize_predicate_name('@<', 'term_lt') :- !.
sanitize_predicate_name('@>', 'term_gt') :- !.
sanitize_predicate_name('@=<', 'term_lte') :- !.
sanitize_predicate_name('@>=', 'term_gte') :- !.
sanitize_predicate_name('=..', 'univ') :- !.
sanitize_predicate_name('!', 'cut') :- !.
sanitize_predicate_name('true', 'true') :- !.
sanitize_predicate_name('->', 'if_then') :- !.
sanitize_predicate_name(';', 'semicolon') :- !.
sanitize_predicate_name('\\+', 'naf') :- !.
sanitize_predicate_name(Name, Name).

%% translate_predicate_clauses(+Clauses, +Index, -JSCode)
translate_predicate_clauses([], _, '').
translate_predicate_clauses([Clause|Rest], Index, JSCode) :-
    translate_single_clause(Clause, Index, ClauseCode),
    NextIndex is Index + 1,
    translate_predicate_clauses(Rest, NextIndex, RestCode),
    atomic_list_concat([ClauseCode, RestCode], '', JSCode).

%% translate_single_clause(+Clause, +Index, -JSCode)
translate_single_clause((Head :- Body), Index, JSCode) :-
    !,
    term_variables((Head, Body), AllVars),
    create_var_map(AllVars),
    setup_call_cleanup(
        true,
        (
            generate_var_declarations(AllVars, VarDecls),
            translate_head_unifications_with_check(Head, Index, HeadCode),
            translate_body(Body, BodyCode, 0),
            copy_term((Head, Body), (HeadDisp, BodyDisp)),
            numbervars((HeadDisp, BodyDisp), 0, _),
            format(atom(JSCode),
'    /* Clause ~w: ~w :- ~w */
    {
        const _cpDepth = state.choiceStack.length;
        const _savedBindingsSize = state.bindings.length;
        const _bodyCp = state.choiceStack.length;
~w~w
            do {
~w            } while (false);
            if (!state.failed) return true;
        }
        /* Restore bindings and clean up any orphaned CPs */
        while (state.choiceStack.length > _cpDepth) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize);
        state.failed = false;
    }
', [Index, HeadDisp, BodyDisp, VarDecls, HeadCode, BodyCode])
        ),
        b_setval(pl2js_clause_vars, [])
    ).

translate_single_clause(Head, Index, JSCode) :-
    % Fact (clause without body)
    term_variables(Head, AllVars),
    create_var_map(AllVars),
    setup_call_cleanup(
        true,
        (
            generate_var_declarations(AllVars, VarDecls),
            translate_head_unifications_with_check(Head, Index, HeadCode),
            copy_term(Head, HeadDisp),
            numbervars(HeadDisp, 0, _),
            format(atom(JSCode),
'    /* Clause ~w: ~w */
    {
        const _savedBindingsSize = state.bindings.length;
~w~w
            return true;
        }
        /* Restore bindings for next clause */
        state.bindings = state.bindings.slice(0, _savedBindingsSize);
        state.failed = false;
    }
', [Index, HeadDisp, VarDecls, HeadCode])
        ),
        b_setval(pl2js_clause_vars, [])
    ).

%% extract_predicate_info(+Term, -Name, -Arity, -Args)
extract_predicate_info(Term, Name, Arity, Args) :-
    Term =.. [Name|Args],
    length(Args, Arity).

%% generate_args_array(+Arity, -ArgsArr)
% Generates a JavaScript array literal "[arg1, arg2, ...]" for the given arity
generate_args_array(0, '[]') :- !.
generate_args_array(N, ArgsArr) :-
    N > 0,
    findall(A, (between(1, N, I), format(atom(A), 'arg~w', [I])), ArgList),
    atomic_list_concat(ArgList, ', ', ArgsStr),
    format(atom(ArgsArr), '[~w]', [ArgsStr]).

%% translate_args_to_params(+Args, -Params)
% Generates ", arg1, arg2, ..." for a JS function signature
translate_args_to_params([], '').
translate_args_to_params(Args, Params) :-
    Args \= [],
    length(Args, N),
    findall(P, (between(1, N, I), format(atom(P), ', arg~w', [I])), ParamList),
    atomic_list_concat(ParamList, '', Params).

%% translate_head_unifications_with_check(+Head, +Index, -JSCode)
translate_head_unifications_with_check(Head, _, JSCode) :-
    extract_predicate_info(Head, _, _, Args),
    translate_head_args_with_check(Args, 1, [], UnifyList),
    ( UnifyList = [] ->
        JSCode = '        {\n'
    ;
        atomic_list_concat(UnifyList, ' &&\n            ', UnifyCondition),
        format(atom(JSCode), '        if (~w) {\n', [UnifyCondition])
    ).

translate_head_args_with_check([], _, Acc, Acc).
translate_head_args_with_check([Arg|Args], N, Acc, Result) :-
    translate_head_arg_check(Arg, N, ArgCode),
    N1 is N + 1,
    append(Acc, [ArgCode], NewAcc),
    translate_head_args_with_check(Args, N1, NewAcc, Result).

translate_head_arg_check(Var, N, JSCode) :-
    var(Var),
    !,
    get_var_index(Var, Index),
    format(atom(JSCode), 'unify(state, var__~w, arg~w)', [Index, N]).
translate_head_arg_check(Arg, N, JSCode) :-
    term_to_js_expr(Arg, JSExpr),
    format(atom(JSCode), 'unify(state, ~w, arg~w)', [JSExpr, N]).

%% translate_body(+Body, -JSCode, +Depth)
translate_body(true, '    /* true */\n', _) :- !.
translate_body(fail, '    state.failed = true;\n    break;\n', _) :- !.
translate_body(!, '    performCut(state);\n', _) :- !.
translate_body((A, B), JSCode, Depth) :-
    !,
    translate_body(A, ACode, Depth),
    translate_body(B, BCode, Depth),
    format(atom(JSCode), '~w~w', [ACode, BCode]).
translate_body((Cond -> Then ; Else), JSCode, Depth) :-
    !,
    translate_body(Cond, CondCode, Depth),
    translate_body(Then, ThenCode, Depth),
    translate_body(Else, ElseCode, Depth),
    format(atom(JSCode),
'    /* If-then-else */
    {
        const _ite_saved = state.bindings.length;
        const _ite_cp~w = state.choiceStack.length;
        (function() { do {
~w        } while (false); })();
        if (!state.failed) {
            /* Condition succeeded: commit (cut alternatives), execute then-branch */
            while (state.choiceStack.length > _ite_cp~w) state.choiceStack.pop();
            do {
~w            } while (false);
        } else {
            /* Condition failed, execute else branch */
            state.bindings = state.bindings.slice(0, _ite_saved);
            while (state.choiceStack.length > _ite_cp~w) state.choiceStack.pop();
            state.failed = false;
            do {
~w            } while (false);
        }
        if (state.failed) break;
    }
', [Depth, CondCode, Depth, ThenCode, Depth, ElseCode]).
translate_body((A ; B), JSCode, Depth) :-
    !,
    NextDepth is Depth + 1,
    translate_body(A, ACode, NextDepth),
    translate_body(B, BCode, NextDepth),
    format(atom(JSCode),
'    /* Disjunction */
    {
        const _disj_cp~w = state.choiceStack.length;
        (function() { do {
~w        } while (false); })();
        if (state.failed) {
            state.failed = false;
            while (state.choiceStack.length > _disj_cp~w) state.choiceStack.pop();
            do {
~w            } while (false);
        }
        if (state.failed) break;
    }
', [Depth, ACode, Depth, BCode]).
translate_body(findall(Template, Goal, Result), JSCode, Depth) :-
    !,
    translate_body(Goal, GoalCodeTemplate, Depth),
    % Replace state. -> findallState. etc. for findall's isolated execution
    atom_codes(GoalCodeTemplate, GoalCodes),
    atom_codes('state.', StateDotCodes),
    atom_codes('findallState.', FindallStateDotCodes),
    replace_all_occurrences(GoalCodes, StateDotCodes, FindallStateDotCodes, TempCodes1),
    atom_codes('(state,', StateCommaCodes),
    atom_codes('(findallState,', FindallStateCommaCodes),
    replace_all_occurrences(TempCodes1, StateCommaCodes, FindallStateCommaCodes, TempCodes2),
    atom_codes('(state)', StateParenCodes),
    atom_codes('(findallState)', FindallStateParenCodes),
    replace_all_occurrences(TempCodes2, StateParenCodes, FindallStateParenCodes, ModifiedGoalCodes),
    atom_codes(GoalCode, ModifiedGoalCodes),
    term_to_js_expr(Template, TemplateExpr),
    term_to_js_expr(Result, ResultExpr),
    format(atom(JSCode),
'    /* findall/3 */
    {
        let _solutions = [];
        const _findallState = initState();

        /* Copy current bindings so goal can access outer variables */
        _findallState.bindings = state.bindings.slice();
        _findallState.nextVarId = state.nextVarId;

        const _initialBindingsSize = _findallState.bindings.length;

        /* Enumerate all solutions */
        while (true) {
            _findallState.failed = false;
            /* Execute the goal in _findallState */
            (function(findallState) {
~w
            })(_findallState);
            if (_findallState.failed) break;

            /* Collect solution: copy the instantiated template */
            _solutions.push(copyTermHelper(_findallState, ~w, new Map()));

            /* Check if there are more solutions via choice points */
            if (_findallState.choiceStack.length === 0) break;

            /* Enable backtracking to resume from the next clause */
            _findallState.backtracking = true;
            _findallState.bindings = _findallState.bindings.slice(0, _initialBindingsSize);
        }

        /* Build result list */
        let _resultList = createNil();
        for (let _i = _solutions.length - 1; _i >= 0; _i--) {
            _resultList = createList(_solutions[_i], _resultList);
        }

        /* Unify Result with collected solutions */
        if (!unify(state, ~w, _resultList)) {
            state.failed = true;
        }
    }
', [GoalCode, TemplateExpr, ResultExpr]).
translate_body(Call, JSCode, _) :-
    % Regular predicate call
    extract_predicate_info(Call, Name, Arity, Args),
    sanitize_predicate_name(Name, SanitizedName),
    format(atom(FuncName), '~w_~w', [SanitizedName, Arity]),
    translate_call_args(Args, ArgStr),
    format(atom(JSCode), '    /* retry loop: if goal fails, backtrack into an earlier choice point */\n    while (!~w(state~w)) {\n        state.failed = false;\n        if (!_retryBody(state, _bodyCp)) { state.failed = true; break; }\n    }\n    if (state.failed) break;\n', [FuncName, ArgStr]).

translate_call_args([], '').
translate_call_args([Arg|Args], Result) :-
    term_to_js_expr(Arg, JSExpr),
    translate_call_args(Args, Rest),
    format(atom(Result), ', ~w~w', [JSExpr, Rest]).

%% replace_all_occurrences(+Input, +Pattern, +Replacement, -Output)
replace_all_occurrences([], _, _, []).
replace_all_occurrences(Input, Pattern, Replacement, Output) :-
    append(Pattern, Rest, Input),
    !,
    append(Replacement, RestOutput, Output),
    replace_all_occurrences(Rest, Pattern, Replacement, RestOutput).
replace_all_occurrences([C|Rest], Pattern, Replacement, [C|Output]) :-
    replace_all_occurrences(Rest, Pattern, Replacement, Output).

%% escape_js_string(+InputCodes, -OutputCodes)
escape_js_string([], []).
escape_js_string([10|Rest], [92, 110|EscapedRest]) :- % \n
    !, escape_js_string(Rest, EscapedRest).
escape_js_string([13|Rest], [92, 114|EscapedRest]) :- % \r
    !, escape_js_string(Rest, EscapedRest).
escape_js_string([9|Rest],  [92, 116|EscapedRest]) :- % \t
    !, escape_js_string(Rest, EscapedRest).
escape_js_string([34|Rest], [92, 34|EscapedRest]) :- % \"
    !, escape_js_string(Rest, EscapedRest).
escape_js_string([92|Rest], [92, 92|EscapedRest]) :- % \\
    !, escape_js_string(Rest, EscapedRest).
escape_js_string([C|Rest], [C|EscapedRest]) :-
    escape_js_string(Rest, EscapedRest).

%% create_var_map(+Vars)
% Stores the ordered list of clause variables using b_setval to preserve
% variable identity (b_setval does not copy terms, unlike assert/retract)
create_var_map(Vars) :-
    b_setval(pl2js_clause_vars, Vars).

%% find_var_index(+Var, +VarList, -Index)
% Finds the position (0-based) of Var in VarList using identity comparison (==/2)
find_var_index(Var, List, Index) :-
    find_var_index_(Var, List, 0, Index).

find_var_index_(Var, [V|_], N, N) :- Var == V, !.
find_var_index_(Var, [_|Vs], N, Index) :-
    N1 is N + 1,
    find_var_index_(Var, Vs, N1, Index).

%% get_var_index(+Var, -Index)
get_var_index(Var, Index) :-
    b_getval(pl2js_clause_vars, Vars),
    find_var_index(Var, Vars, Index),
    !.
get_var_index(Var, _) :-
    format(user_error, 'ERROR: Variable ~w not found in mapping~n', [Var]),
    fail.

%% generate_var_declarations(+Vars, -Decls)
generate_var_declarations([], '').
generate_var_declarations(Vars, Decls) :-
    Vars \= [],
    generate_var_decls_with_ids(Vars, 0, DeclList),
    atomic_list_concat(DeclList, '', Decls).

generate_var_decls_with_ids([], _, []).
generate_var_decls_with_ids([V|Vs], N, [Decl|Decls]) :-
    get_var_index(V, Index),
    format(atom(Decl), '        const var__~w = createVar(state.nextVarId++);\n', [Index]),
    N1 is N + 1,
    generate_var_decls_with_ids(Vs, N1, Decls).

%% term_to_js_expr(+Term, -JSExpr)
% Converts a Prolog term to a JavaScript expression creating that term
term_to_js_expr(Var, Expr) :-
    var(Var),
    !,
    get_var_index(Var, Index),
    format(atom(Expr), 'var__~w', [Index]).
term_to_js_expr(Atom, Expr) :-
    atom(Atom),
    !,
    atom_codes(Atom, Codes),
    escape_js_string(Codes, EscapedCodes),
    atom_codes(EscapedAtom, EscapedCodes),
    format(atom(Expr), 'createAtom("~w")', [EscapedAtom]).
term_to_js_expr(Int, Expr) :-
    integer(Int),
    !,
    format(atom(Expr), 'createInt(~w)', [Int]).
term_to_js_expr([], 'createNil()') :- !.
term_to_js_expr([H|T], Expr) :-
    !,
    term_to_js_expr(H, HExpr),
    term_to_js_expr(T, TExpr),
    format(atom(Expr), 'createList(~w, ~w)', [HExpr, TExpr]).
term_to_js_expr(Compound, Expr) :-
    Compound =.. [Functor|Args],
    length(Args, Arity),
    maplist(term_to_js_expr, Args, JSArgs),
    atomic_list_concat(JSArgs, ', ', ArgsStr),
    format(atom(Expr), 'createCompound("~w", ~w, [~w])', [Functor, Arity, ArgsStr]).

%% generate_js_footer(-Footer)
% Generates the entry-point code at the bottom of the output file
generate_js_footer(Footer) :-
    Footer =
'
/* ---- Entry point ---- */
if (typeof document !== "undefined") {
    /* Browser environment: expose helpers, let HTML page drive execution */
    window.prologRunQuery = runQuery;
    window.prologOutput = function() { return _prologOutput; };
} else if (typeof main_0 !== "undefined") {
    /* Non-browser environment (e.g. Node.js): run main_0 automatically */
    const _mainState = initState();
    main_0(_mainState);
}
'.

%% write_js_file(+File, +JSCode)
write_js_file(File, JSCode) :-
    open(File, write, Stream),
    write(Stream, JSCode),
    close(Stream).

%% compile_file(+PrologBase, +OutputBase)
% Compiles Prolog file (auto-appending .pl if needed) to JavaScript
compile_file(PrologBase, OutputBase) :-
    ( file_name_extension(_, pl, PrologBase) ->
        PrologFile = PrologBase
    ;
        file_name_extension(PrologBase, pl, PrologFile)
    ),
    format(atom(JSFile), '~w.js', [OutputBase]),
    compile_prolog_to_js(PrologFile, JSFile).

%% verify_equivalence(+PrologFile)
% Verifies that compiled JS output matches SWI-Prolog output (requires node.js)
verify_equivalence(PrologFile) :-
    format(atom(PrologCmd), 'swipl -g main -t halt ~w > prolog_output.txt', [PrologFile]),
    shell(PrologCmd),
    atom_concat(Base, '.pl', PrologFile),
    compile_file(PrologFile, Base),
    format(atom(JSCmd), 'node ~w.js > js_output.txt', [Base]),
    shell(JSCmd),
    shell('diff prolog_output.txt js_output.txt'),
    write('Verification successful: outputs match!\n').
