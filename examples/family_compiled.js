// pl2js - Prolog to JavaScript compiled output
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
            if (f === "/\\") return l & r;
            if (f === "\\/") return l | r;
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
            if (f === "\\")       return ~v;
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
    _prologWrite("\n");
    return true;
}
function nl_0(state) { _prologWrite("\n"); return true; }
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
                out += "\n"; i += 2;
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

function parent_2(state, arg1, arg2) {
    /* Check if resuming from a choice point (only when backtracking) */
    let startClause = 1;
    const _top = state.choiceStack.length > 0
        ? state.choiceStack[state.choiceStack.length - 1] : null;
    if (state.backtracking && _top && _top.predId === parent_2) {
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

    /* Clause 1: parent(tom,bob) */
    if (startClause <= 1) {
        const _cpDepth1 = state.choiceStack.length;
        const _savedBindingsSize1 = state.bindings.length;
        /* Push choice point for next clause before trying this one */
        pushChoicePoint(state, parent_2, 2, [arg1, arg2]);
        if (unify(state, createAtom("tom"), arg1) &&
            unify(state, createAtom("bob"), arg2)) {

            return true;
        }
        /* Clause failed: pop all CPs pushed during this attempt */
        while (state.choiceStack.length > _cpDepth1) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize1);
        state.failed = false;
    }
    /* Clause 2: parent(tom,liz) */
    if (startClause <= 2) {
        const _cpDepth2 = state.choiceStack.length;
        const _savedBindingsSize2 = state.bindings.length;
        /* Push choice point for next clause before trying this one */
        pushChoicePoint(state, parent_2, 3, [arg1, arg2]);
        if (unify(state, createAtom("tom"), arg1) &&
            unify(state, createAtom("liz"), arg2)) {

            return true;
        }
        /* Clause failed: pop all CPs pushed during this attempt */
        while (state.choiceStack.length > _cpDepth2) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize2);
        state.failed = false;
    }
    /* Clause 3: parent(bob,ann) */
    if (startClause <= 3) {
        const _cpDepth3 = state.choiceStack.length;
        const _savedBindingsSize3 = state.bindings.length;
        /* Push choice point for next clause before trying this one */
        pushChoicePoint(state, parent_2, 4, [arg1, arg2]);
        if (unify(state, createAtom("bob"), arg1) &&
            unify(state, createAtom("ann"), arg2)) {

            return true;
        }
        /* Clause failed: pop all CPs pushed during this attempt */
        while (state.choiceStack.length > _cpDepth3) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize3);
        state.failed = false;
    }
    /* Clause 4: parent(bob,pat) */
    if (startClause <= 4) {
        const _cpDepth4 = state.choiceStack.length;
        const _savedBindingsSize4 = state.bindings.length;
        /* Push choice point for next clause before trying this one */
        pushChoicePoint(state, parent_2, 5, [arg1, arg2]);
        if (unify(state, createAtom("bob"), arg1) &&
            unify(state, createAtom("pat"), arg2)) {

            return true;
        }
        /* Clause failed: pop all CPs pushed during this attempt */
        while (state.choiceStack.length > _cpDepth4) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize4);
        state.failed = false;
    }
    /* Clause 5: parent(pat,jim) */
    if (startClause <= 5) {
        const _cpDepth5 = state.choiceStack.length;
        const _savedBindingsSize5 = state.bindings.length;
        /* Push sentinel choice point before trying last clause */
        pushChoicePoint(state, parent_2, 9999, [arg1, arg2]);
        if (unify(state, createAtom("pat"), arg1) &&
            unify(state, createAtom("jim"), arg2)) {

            return true;
        }
        /* Clause failed: pop all CPs pushed during this attempt */
        while (state.choiceStack.length > _cpDepth5) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize5);
        state.failed = false;
    }

    return false; /* No clause matched */
}
function grandparent_2(state, arg1, arg2) {
    /* Clause 1: grandparent(A,B) :- parent(A,C),parent(C,B) */
    {
        const _cpDepth = state.choiceStack.length;
        const _savedBindingsSize = state.bindings.length;
        const _bodyCp = state.choiceStack.length;
        const var__0 = createVar(state.nextVarId++);
        const var__1 = createVar(state.nextVarId++);
        const var__2 = createVar(state.nextVarId++);
        if (unify(state, var__0, arg1) &&
            unify(state, var__1, arg2)) {

            do {
    /* retry loop: if goal fails, backtrack into an earlier choice point */
    while (!parent_2(state, var__0, var__2)) {
        state.failed = false;
        if (!_retryBody(state, _bodyCp)) { state.failed = true; break; }
    }
    if (state.failed) break;
    /* retry loop: if goal fails, backtrack into an earlier choice point */
    while (!parent_2(state, var__2, var__1)) {
        state.failed = false;
        if (!_retryBody(state, _bodyCp)) { state.failed = true; break; }
    }
    if (state.failed) break;
            } while (false);
            if (!state.failed) return true;
        }
        /* Restore bindings and clean up any orphaned CPs */
        while (state.choiceStack.length > _cpDepth) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize);
        state.failed = false;
    }

    return false; /* No clause matched */
}
function ancestor_2(state, arg1, arg2) {
    /* Check if resuming from a choice point (only when backtracking) */
    let startClause = 1;
    const _top = state.choiceStack.length > 0
        ? state.choiceStack[state.choiceStack.length - 1] : null;
    if (state.backtracking && _top && _top.predId === ancestor_2) {
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

    /* Clause 1: ancestor(A,B) :- parent(A,B) */
    if (startClause <= 1) {
        const _cpDepth1 = state.choiceStack.length;
        const _savedBindingsSize1 = state.bindings.length;
        /* Push choice point for next clause before trying this one */
        pushChoicePoint(state, ancestor_2, 2, [arg1, arg2]);
        const _bodyCp = state.choiceStack.length;
        const var__0 = createVar(state.nextVarId++);
        const var__1 = createVar(state.nextVarId++);
        if (unify(state, var__0, arg1) &&
            unify(state, var__1, arg2)) {

            do {
    /* retry loop: if goal fails, backtrack into an earlier choice point */
    while (!parent_2(state, var__0, var__1)) {
        state.failed = false;
        if (!_retryBody(state, _bodyCp)) { state.failed = true; break; }
    }
    if (state.failed) break;
            } while (false);
            if (!state.failed) return true;
        }
        /* Clause failed: pop all CPs pushed during this attempt */
        while (state.choiceStack.length > _cpDepth1) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize1);
        state.failed = false;
    }
    /* Clause 2: ancestor(A,B) :- parent(A,C),ancestor(C,B) */
    if (startClause <= 2) {
        const _cpDepth2 = state.choiceStack.length;
        const _savedBindingsSize2 = state.bindings.length;
        /* Push sentinel choice point before trying last clause */
        pushChoicePoint(state, ancestor_2, 9999, [arg1, arg2]);
        const _bodyCp = state.choiceStack.length;
        const var__0 = createVar(state.nextVarId++);
        const var__1 = createVar(state.nextVarId++);
        const var__2 = createVar(state.nextVarId++);
        if (unify(state, var__0, arg1) &&
            unify(state, var__1, arg2)) {

            do {
    /* retry loop: if goal fails, backtrack into an earlier choice point */
    while (!parent_2(state, var__0, var__2)) {
        state.failed = false;
        if (!_retryBody(state, _bodyCp)) { state.failed = true; break; }
    }
    if (state.failed) break;
    /* retry loop: if goal fails, backtrack into an earlier choice point */
    while (!ancestor_2(state, var__2, var__1)) {
        state.failed = false;
        if (!_retryBody(state, _bodyCp)) { state.failed = true; break; }
    }
    if (state.failed) break;
            } while (false);
            if (!state.failed) return true;
        }
        /* Clause failed: pop all CPs pushed during this attempt */
        while (state.choiceStack.length > _cpDepth2) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize2);
        state.failed = false;
    }

    return false; /* No clause matched */
}
function member_2(state, arg1, arg2) {
    /* Check if resuming from a choice point (only when backtracking) */
    let startClause = 1;
    const _top = state.choiceStack.length > 0
        ? state.choiceStack[state.choiceStack.length - 1] : null;
    if (state.backtracking && _top && _top.predId === member_2) {
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

    /* Clause 1: member(A,[A|B]) */
    if (startClause <= 1) {
        const _cpDepth1 = state.choiceStack.length;
        const _savedBindingsSize1 = state.bindings.length;
        /* Push choice point for next clause before trying this one */
        pushChoicePoint(state, member_2, 2, [arg1, arg2]);
        const var__0 = createVar(state.nextVarId++);
        const var__1 = createVar(state.nextVarId++);
        if (unify(state, var__0, arg1) &&
            unify(state, createList(var__0, var__1), arg2)) {

            return true;
        }
        /* Clause failed: pop all CPs pushed during this attempt */
        while (state.choiceStack.length > _cpDepth1) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize1);
        state.failed = false;
    }
    /* Clause 2: member(A,[B|C]) :- member(A,C) */
    if (startClause <= 2) {
        const _cpDepth2 = state.choiceStack.length;
        const _savedBindingsSize2 = state.bindings.length;
        /* Push sentinel choice point before trying last clause */
        pushChoicePoint(state, member_2, 9999, [arg1, arg2]);
        const _bodyCp = state.choiceStack.length;
        const var__0 = createVar(state.nextVarId++);
        const var__1 = createVar(state.nextVarId++);
        const var__2 = createVar(state.nextVarId++);
        if (unify(state, var__0, arg1) &&
            unify(state, createList(var__1, var__2), arg2)) {

            do {
    /* retry loop: if goal fails, backtrack into an earlier choice point */
    while (!member_2(state, var__0, var__2)) {
        state.failed = false;
        if (!_retryBody(state, _bodyCp)) { state.failed = true; break; }
    }
    if (state.failed) break;
            } while (false);
            if (!state.failed) return true;
        }
        /* Clause failed: pop all CPs pushed during this attempt */
        while (state.choiceStack.length > _cpDepth2) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize2);
        state.failed = false;
    }

    return false; /* No clause matched */
}
function append_3(state, arg1, arg2, arg3) {
    /* Check if resuming from a choice point (only when backtracking) */
    let startClause = 1;
    const _top = state.choiceStack.length > 0
        ? state.choiceStack[state.choiceStack.length - 1] : null;
    if (state.backtracking && _top && _top.predId === append_3) {
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

    /* Clause 1: append([],A,A) */
    if (startClause <= 1) {
        const _cpDepth1 = state.choiceStack.length;
        const _savedBindingsSize1 = state.bindings.length;
        /* Push choice point for next clause before trying this one */
        pushChoicePoint(state, append_3, 2, [arg1, arg2, arg3]);
        const var__0 = createVar(state.nextVarId++);
        if (unify(state, createNil(), arg1) &&
            unify(state, var__0, arg2) &&
            unify(state, var__0, arg3)) {

            return true;
        }
        /* Clause failed: pop all CPs pushed during this attempt */
        while (state.choiceStack.length > _cpDepth1) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize1);
        state.failed = false;
    }
    /* Clause 2: append([A|B],C,[A|D]) :- append(B,C,D) */
    if (startClause <= 2) {
        const _cpDepth2 = state.choiceStack.length;
        const _savedBindingsSize2 = state.bindings.length;
        /* Push sentinel choice point before trying last clause */
        pushChoicePoint(state, append_3, 9999, [arg1, arg2, arg3]);
        const _bodyCp = state.choiceStack.length;
        const var__0 = createVar(state.nextVarId++);
        const var__1 = createVar(state.nextVarId++);
        const var__2 = createVar(state.nextVarId++);
        const var__3 = createVar(state.nextVarId++);
        if (unify(state, createList(var__0, var__1), arg1) &&
            unify(state, var__2, arg2) &&
            unify(state, createList(var__0, var__3), arg3)) {

            do {
    /* retry loop: if goal fails, backtrack into an earlier choice point */
    while (!append_3(state, var__1, var__2, var__3)) {
        state.failed = false;
        if (!_retryBody(state, _bodyCp)) { state.failed = true; break; }
    }
    if (state.failed) break;
            } while (false);
            if (!state.failed) return true;
        }
        /* Clause failed: pop all CPs pushed during this attempt */
        while (state.choiceStack.length > _cpDepth2) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize2);
        state.failed = false;
    }

    return false; /* No clause matched */
}
function max_3(state, arg1, arg2, arg3) {
    /* Check if resuming from a choice point (only when backtracking) */
    let startClause = 1;
    const _top = state.choiceStack.length > 0
        ? state.choiceStack[state.choiceStack.length - 1] : null;
    if (state.backtracking && _top && _top.predId === max_3) {
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

    /* Clause 1: max(A,B,A) :- A>=B,! */
    if (startClause <= 1) {
        const _cpDepth1 = state.choiceStack.length;
        const _savedBindingsSize1 = state.bindings.length;
        /* Push choice point for next clause before trying this one */
        pushChoicePoint(state, max_3, 2, [arg1, arg2, arg3]);
        const _bodyCp = state.choiceStack.length;
        const var__0 = createVar(state.nextVarId++);
        const var__1 = createVar(state.nextVarId++);
        if (unify(state, var__0, arg1) &&
            unify(state, var__1, arg2) &&
            unify(state, var__0, arg3)) {

            do {
    /* retry loop: if goal fails, backtrack into an earlier choice point */
    while (!gte_2(state, var__0, var__1)) {
        state.failed = false;
        if (!_retryBody(state, _bodyCp)) { state.failed = true; break; }
    }
    if (state.failed) break;
    performCut(state);
            } while (false);
            if (!state.failed) return true;
        }
        /* Clause failed: pop all CPs pushed during this attempt */
        while (state.choiceStack.length > _cpDepth1) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize1);
        state.failed = false;
    }
    /* Clause 2: max(A,B,B) */
    if (startClause <= 2) {
        const _cpDepth2 = state.choiceStack.length;
        const _savedBindingsSize2 = state.bindings.length;
        /* Push sentinel choice point before trying last clause */
        pushChoicePoint(state, max_3, 9999, [arg1, arg2, arg3]);
        const var__0 = createVar(state.nextVarId++);
        const var__1 = createVar(state.nextVarId++);
        if (unify(state, var__0, arg1) &&
            unify(state, var__1, arg2) &&
            unify(state, var__1, arg3)) {

            return true;
        }
        /* Clause failed: pop all CPs pushed during this attempt */
        while (state.choiceStack.length > _cpDepth2) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize2);
        state.failed = false;
    }

    return false; /* No clause matched */
}
function main_0(state) {
    /* Clause 1: main :- write(=== Family Relationships ===),nl,(grandparent(tom,ann)->write(grandparent(tom, ann) = true),nl;write(grandparent(tom, ann) = false),nl),(member(bob,[tom,bob,liz])->write(member(bob, [tom,bob,liz]) = true),nl;write(member(bob, [tom,bob,liz]) = false),nl),max(3,5,A),write(max(3,5) = ),write(A),nl,write(=== Done ===),nl */
    {
        const _cpDepth = state.choiceStack.length;
        const _savedBindingsSize = state.bindings.length;
        const _bodyCp = state.choiceStack.length;
        const var__0 = createVar(state.nextVarId++);
        {

            do {
    /* retry loop: if goal fails, backtrack into an earlier choice point */
    while (!write_1(state, createAtom("=== Family Relationships ==="))) {
        state.failed = false;
        if (!_retryBody(state, _bodyCp)) { state.failed = true; break; }
    }
    if (state.failed) break;
    /* retry loop: if goal fails, backtrack into an earlier choice point */
    while (!nl_0(state)) {
        state.failed = false;
        if (!_retryBody(state, _bodyCp)) { state.failed = true; break; }
    }
    if (state.failed) break;
    /* If-then-else */
    {
        const _ite_saved = state.bindings.length;
        const _ite_cp0 = state.choiceStack.length;
        (function() { do {
    /* retry loop: if goal fails, backtrack into an earlier choice point */
    while (!grandparent_2(state, createAtom("tom"), createAtom("ann"))) {
        state.failed = false;
        if (!_retryBody(state, _bodyCp)) { state.failed = true; break; }
    }
    if (state.failed) break;
        } while (false); })();
        if (!state.failed) {
            /* Condition succeeded: commit (cut alternatives), execute then-branch */
            while (state.choiceStack.length > _ite_cp0) state.choiceStack.pop();
            do {
    /* retry loop: if goal fails, backtrack into an earlier choice point */
    while (!write_1(state, createAtom("grandparent(tom, ann) = true"))) {
        state.failed = false;
        if (!_retryBody(state, _bodyCp)) { state.failed = true; break; }
    }
    if (state.failed) break;
    /* retry loop: if goal fails, backtrack into an earlier choice point */
    while (!nl_0(state)) {
        state.failed = false;
        if (!_retryBody(state, _bodyCp)) { state.failed = true; break; }
    }
    if (state.failed) break;
            } while (false);
        } else {
            /* Condition failed, execute else branch */
            state.bindings = state.bindings.slice(0, _ite_saved);
            while (state.choiceStack.length > _ite_cp0) state.choiceStack.pop();
            state.failed = false;
            do {
    /* retry loop: if goal fails, backtrack into an earlier choice point */
    while (!write_1(state, createAtom("grandparent(tom, ann) = false"))) {
        state.failed = false;
        if (!_retryBody(state, _bodyCp)) { state.failed = true; break; }
    }
    if (state.failed) break;
    /* retry loop: if goal fails, backtrack into an earlier choice point */
    while (!nl_0(state)) {
        state.failed = false;
        if (!_retryBody(state, _bodyCp)) { state.failed = true; break; }
    }
    if (state.failed) break;
            } while (false);
        }
        if (state.failed) break;
    }
    /* If-then-else */
    {
        const _ite_saved = state.bindings.length;
        const _ite_cp0 = state.choiceStack.length;
        (function() { do {
    /* retry loop: if goal fails, backtrack into an earlier choice point */
    while (!member_2(state, createAtom("bob"), createList(createAtom("tom"), createList(createAtom("bob"), createList(createAtom("liz"), createNil()))))) {
        state.failed = false;
        if (!_retryBody(state, _bodyCp)) { state.failed = true; break; }
    }
    if (state.failed) break;
        } while (false); })();
        if (!state.failed) {
            /* Condition succeeded: commit (cut alternatives), execute then-branch */
            while (state.choiceStack.length > _ite_cp0) state.choiceStack.pop();
            do {
    /* retry loop: if goal fails, backtrack into an earlier choice point */
    while (!write_1(state, createAtom("member(bob, [tom,bob,liz]) = true"))) {
        state.failed = false;
        if (!_retryBody(state, _bodyCp)) { state.failed = true; break; }
    }
    if (state.failed) break;
    /* retry loop: if goal fails, backtrack into an earlier choice point */
    while (!nl_0(state)) {
        state.failed = false;
        if (!_retryBody(state, _bodyCp)) { state.failed = true; break; }
    }
    if (state.failed) break;
            } while (false);
        } else {
            /* Condition failed, execute else branch */
            state.bindings = state.bindings.slice(0, _ite_saved);
            while (state.choiceStack.length > _ite_cp0) state.choiceStack.pop();
            state.failed = false;
            do {
    /* retry loop: if goal fails, backtrack into an earlier choice point */
    while (!write_1(state, createAtom("member(bob, [tom,bob,liz]) = false"))) {
        state.failed = false;
        if (!_retryBody(state, _bodyCp)) { state.failed = true; break; }
    }
    if (state.failed) break;
    /* retry loop: if goal fails, backtrack into an earlier choice point */
    while (!nl_0(state)) {
        state.failed = false;
        if (!_retryBody(state, _bodyCp)) { state.failed = true; break; }
    }
    if (state.failed) break;
            } while (false);
        }
        if (state.failed) break;
    }
    /* retry loop: if goal fails, backtrack into an earlier choice point */
    while (!max_3(state, createInt(3), createInt(5), var__0)) {
        state.failed = false;
        if (!_retryBody(state, _bodyCp)) { state.failed = true; break; }
    }
    if (state.failed) break;
    /* retry loop: if goal fails, backtrack into an earlier choice point */
    while (!write_1(state, createAtom("max(3,5) = "))) {
        state.failed = false;
        if (!_retryBody(state, _bodyCp)) { state.failed = true; break; }
    }
    if (state.failed) break;
    /* retry loop: if goal fails, backtrack into an earlier choice point */
    while (!write_1(state, var__0)) {
        state.failed = false;
        if (!_retryBody(state, _bodyCp)) { state.failed = true; break; }
    }
    if (state.failed) break;
    /* retry loop: if goal fails, backtrack into an earlier choice point */
    while (!nl_0(state)) {
        state.failed = false;
        if (!_retryBody(state, _bodyCp)) { state.failed = true; break; }
    }
    if (state.failed) break;
    /* retry loop: if goal fails, backtrack into an earlier choice point */
    while (!write_1(state, createAtom("=== Done ==="))) {
        state.failed = false;
        if (!_retryBody(state, _bodyCp)) { state.failed = true; break; }
    }
    if (state.failed) break;
    /* retry loop: if goal fails, backtrack into an earlier choice point */
    while (!nl_0(state)) {
        state.failed = false;
        if (!_retryBody(state, _bodyCp)) { state.failed = true; break; }
    }
    if (state.failed) break;
            } while (false);
            if (!state.failed) return true;
        }
        /* Restore bindings and clean up any orphaned CPs */
        while (state.choiceStack.length > _cpDepth) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize);
        state.failed = false;
    }

    return false; /* No clause matched */
}


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
