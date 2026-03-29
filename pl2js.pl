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

% Dynamic predicate to store variable-name-to-index mapping during compilation
:- dynamic var_name_index_map/2.

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
    // Simplified: just succeeds (full implementation requires meta-call)
    return true;
}
function ignore_1(state, goal) {
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
translate_predicate_group(Name/Arity-Clauses, JSCode) :-
    Clauses = [FirstClause|_],
    clause_head(FirstClause, Head),
    extract_predicate_info(Head, _, _, Args),
    translate_args_to_params(Args, Params),
    sanitize_predicate_name(Name, SanitizedName),
    format(atom(FuncName), '~w_~w', [SanitizedName, Arity]),
    length(Clauses, NumClauses),
    ( NumClauses > 1 ->
        translate_nondeterministic_predicate(Clauses, FuncName, Params, Arity, JSCode)
    ;
        translate_predicate_clauses(Clauses, 1, ClausesCode),
        format(atom(JSCode),
'function ~w(state~w) {
~w
    return false; /* No clause matched */
}', [FuncName, Params, ClausesCode])
    ).

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
        retractall(var_name_index_map(_, _))
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
        retractall(var_name_index_map(_, _))
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
        retractall(var_name_index_map(_, _))
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
        retractall(var_name_index_map(_, _))
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
create_var_map(Vars) :-
    retractall(var_name_index_map(_, _)),
    format(atom(_), '~w', [Vars]),
    create_var_map_impl(Vars, 0).

create_var_map_impl([], _).
create_var_map_impl([V|Vs], N) :-
    format(atom(VarName), '~w', [V]),
    assert(var_name_index_map(VarName, N)),
    N1 is N + 1,
    create_var_map_impl(Vs, N1).

%% get_var_index(+Var, -Index)
get_var_index(Var, Index) :-
    format(atom(VarName), '~w', [Var]),
    var_name_index_map(VarName, Index),
    !.
get_var_index(Var, _) :-
    format(atom(VarName), '~w', [Var]),
    format(user_error, 'ERROR: Variable ~w (name: ~w) not found in mapping~n', [Var, VarName]),
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

%% compile_file(+PrologFile, +OutputBase)
% Compiles Prolog file to JavaScript
compile_file(PrologFile, OutputBase) :-
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
