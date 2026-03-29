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

function pushChoicePoint(state, predId, clauseIdx) {
    state.choiceStack.push({
        predId: predId,
        clauseIdx: clauseIdx,
        savedBindingsSize: state.bindings.length
    });
}

function popChoicePoint(state) {
    if (state.choiceStack.length === 0) return false;
    const cp = state.choiceStack.pop();
    state.bindings = state.bindings.slice(0, cp.savedBindingsSize);
    return true;
}

function performCut(state) {
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

// ---- Structural equality ----
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
        const f = t.functor, a = t.arity;
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
            if (f === "min") return Math.min(l, r);
            if (f === "max") return Math.max(l, r);
        }
        if (a === 1) {
            const v = evalArithmetic(state, t.args[0]);
            if (f === "-")   return -v;
            if (f === "abs") return Math.abs(v);
        }
    }
    return 0;
}

// ---- Built-in predicates ----
function is_2(state, arg1, arg2) {
    return unify(state, arg1, createInt(evalArithmetic(state, arg2)));
}
function gt_2(state, arg1, arg2) {
    const t1 = deref(state, arg1), t2 = deref(state, arg2);
    if (t1.type === "int" && t2.type === "int") return t1.val > t2.val;
    state.failed = true; return false;
}
function lt_2(state, arg1, arg2) {
    const t1 = deref(state, arg1), t2 = deref(state, arg2);
    if (t1.type === "int" && t2.type === "int") return t1.val < t2.val;
    state.failed = true; return false;
}
function gte_2(state, arg1, arg2) {
    const t1 = deref(state, arg1), t2 = deref(state, arg2);
    if (t1.type === "int" && t2.type === "int") return t1.val >= t2.val;
    state.failed = true; return false;
}
function lte_2(state, arg1, arg2) {
    const t1 = deref(state, arg1), t2 = deref(state, arg2);
    if (t1.type === "int" && t2.type === "int") return t1.val <= t2.val;
    state.failed = true; return false;
}
function eq_2(state, arg1, arg2) { return unify(state, arg1, arg2); }
function neq_2(state, arg1, arg2) {
    const savedSize = state.bindings.length;
    const ok = unify(state, arg1, arg2);
    state.bindings = state.bindings.slice(0, savedSize);
    return !ok;
}
function eqeq_2(state, arg1, arg2) {
    return termsEqual(deref(state, arg1), deref(state, arg2));
}
function neqeq_2(state, arg1, arg2) { return !eqeq_2(state, arg1, arg2); }
function true_0(state) { return true; }
function fail_0(state) { state.failed = true; return false; }

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
        case "atom":    return term.name;
        case "int":     return String(term.val);
        case "nil":     return "[]";
        case "var":     return "_" + term.id;
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
function nl_0(state) { _prologWrite("\n"); return true; }

// ---- Term copy ----
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

// End of runtime library

// ---- Generated predicates from family.pl ----

function parent_2(state, arg1, arg2) {
    /* Check if resuming from a choice point (only when backtracking) */
    let startClause = 1;
    const _top = state.choiceStack.length > 0
        ? state.choiceStack[state.choiceStack.length - 1] : null;
    if (state.backtracking && _top && _top.predId === parent_2) {
        startClause = _top.clauseIdx;
        popChoicePoint(state);
        state.backtracking = false;
        if (startClause >= 9999) {
            state.failed = true;
            return false;
        }
    }

    /* Clause 1: parent(tom,bob) */
    if (startClause <= 1) {
        const _cpDepth1 = state.choiceStack.length;
        const _savedBindingsSize1 = state.bindings.length;
        pushChoicePoint(state, parent_2, 2);
        if (unify(state, createAtom("tom"), arg1) &&
            unify(state, createAtom("bob"), arg2)) {
            return true;
        }
        while (state.choiceStack.length > _cpDepth1) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize1);
        state.failed = false;
    }
    /* Clause 2: parent(tom,liz) */
    if (startClause <= 2) {
        const _cpDepth2 = state.choiceStack.length;
        const _savedBindingsSize2 = state.bindings.length;
        pushChoicePoint(state, parent_2, 3);
        if (unify(state, createAtom("tom"), arg1) &&
            unify(state, createAtom("liz"), arg2)) {
            return true;
        }
        while (state.choiceStack.length > _cpDepth2) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize2);
        state.failed = false;
    }
    /* Clause 3: parent(bob,ann) */
    if (startClause <= 3) {
        const _cpDepth3 = state.choiceStack.length;
        const _savedBindingsSize3 = state.bindings.length;
        pushChoicePoint(state, parent_2, 4);
        if (unify(state, createAtom("bob"), arg1) &&
            unify(state, createAtom("ann"), arg2)) {
            return true;
        }
        while (state.choiceStack.length > _cpDepth3) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize3);
        state.failed = false;
    }
    /* Clause 4: parent(bob,pat) */
    if (startClause <= 4) {
        const _cpDepth4 = state.choiceStack.length;
        const _savedBindingsSize4 = state.bindings.length;
        pushChoicePoint(state, parent_2, 5);
        if (unify(state, createAtom("bob"), arg1) &&
            unify(state, createAtom("pat"), arg2)) {
            return true;
        }
        while (state.choiceStack.length > _cpDepth4) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize4);
        state.failed = false;
    }
    /* Clause 5: parent(pat,jim) */
    if (startClause <= 5) {
        const _cpDepth5 = state.choiceStack.length;
        const _savedBindingsSize5 = state.bindings.length;
        pushChoicePoint(state, parent_2, 9999);
        if (unify(state, createAtom("pat"), arg1) &&
            unify(state, createAtom("jim"), arg2)) {
            return true;
        }
        while (state.choiceStack.length > _cpDepth5) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize5);
        state.failed = false;
    }
    return false; /* No clause matched */
}

function grandparent_2(state, arg1, arg2) {
    /* Clause 1: grandparent(A,C) :- parent(A,B), parent(B,C) */
    {
        const _cpDepth = state.choiceStack.length;
        const _savedBindingsSize = state.bindings.length;
        const var__0 = createVar(state.nextVarId++); /* X */
        const var__1 = createVar(state.nextVarId++); /* Y */
        const var__2 = createVar(state.nextVarId++); /* Z */
        if (unify(state, var__0, arg1) &&
            unify(state, var__2, arg2)) {
            do {
                if (!parent_2(state, var__0, var__1)) { state.failed = true; break; }
                if (!parent_2(state, var__1, var__2)) { state.failed = true; break; }
            } while (false);
            if (!state.failed) return true;
        }
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
        state.backtracking = false;
        if (startClause >= 9999) {
            state.failed = true;
            return false;
        }
    }

    /* Clause 1: ancestor(X,Y) :- parent(X,Y) */
    if (startClause <= 1) {
        const _cpDepth1 = state.choiceStack.length;
        const _savedBindingsSize1 = state.bindings.length;
        pushChoicePoint(state, ancestor_2, 2);
        const var__0 = createVar(state.nextVarId++); /* X */
        const var__1 = createVar(state.nextVarId++); /* Y */
        if (unify(state, var__0, arg1) &&
            unify(state, var__1, arg2)) {
            do {
                if (!parent_2(state, var__0, var__1)) { state.failed = true; break; }
            } while (false);
            if (!state.failed) return true;
        }
        while (state.choiceStack.length > _cpDepth1) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize1);
        state.failed = false;
    }
    /* Clause 2: ancestor(X,Y) :- parent(X,Z), ancestor(Z,Y) */
    if (startClause <= 2) {
        const _cpDepth2 = state.choiceStack.length;
        const _savedBindingsSize2 = state.bindings.length;
        pushChoicePoint(state, ancestor_2, 9999);
        const var__0 = createVar(state.nextVarId++); /* X */
        const var__1 = createVar(state.nextVarId++); /* Y */
        const var__2 = createVar(state.nextVarId++); /* Z */
        if (unify(state, var__0, arg1) &&
            unify(state, var__1, arg2)) {
            do {
                if (!parent_2(state, var__0, var__2)) { state.failed = true; break; }
                if (!ancestor_2(state, var__2, var__1)) { state.failed = true; break; }
            } while (false);
            if (!state.failed) return true;
        }
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
        state.backtracking = false;
        if (startClause >= 9999) {
            state.failed = true;
            return false;
        }
    }

    /* Clause 1: member(X,[X|_]) */
    if (startClause <= 1) {
        const _cpDepth1 = state.choiceStack.length;
        const _savedBindingsSize1 = state.bindings.length;
        pushChoicePoint(state, member_2, 2);
        const var__0 = createVar(state.nextVarId++); /* X */
        const var__1 = createVar(state.nextVarId++); /* _ */
        if (unify(state, var__0, arg1) &&
            unify(state, createList(var__0, var__1), arg2)) {
            return true;
        }
        while (state.choiceStack.length > _cpDepth1) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize1);
        state.failed = false;
    }
    /* Clause 2: member(X,[_|T]) :- member(X,T) */
    if (startClause <= 2) {
        const _cpDepth2 = state.choiceStack.length;
        const _savedBindingsSize2 = state.bindings.length;
        pushChoicePoint(state, member_2, 9999);
        const var__0 = createVar(state.nextVarId++); /* X */
        const var__1 = createVar(state.nextVarId++); /* _ */
        const var__2 = createVar(state.nextVarId++); /* T */
        if (unify(state, var__0, arg1) &&
            unify(state, createList(var__1, var__2), arg2)) {
            do {
                if (!member_2(state, var__0, var__2)) { state.failed = true; break; }
            } while (false);
            if (!state.failed) return true;
        }
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
        state.backtracking = false;
        if (startClause >= 9999) {
            state.failed = true;
            return false;
        }
    }

    /* Clause 1: append([],L,L) */
    if (startClause <= 1) {
        const _cpDepth1 = state.choiceStack.length;
        const _savedBindingsSize1 = state.bindings.length;
        pushChoicePoint(state, append_3, 2);
        const var__0 = createVar(state.nextVarId++); /* L */
        if (unify(state, createNil(), arg1) &&
            unify(state, var__0, arg2) &&
            unify(state, var__0, arg3)) {
            return true;
        }
        while (state.choiceStack.length > _cpDepth1) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize1);
        state.failed = false;
    }
    /* Clause 2: append([H|T1],L2,[H|T3]) :- append(T1,L2,T3) */
    if (startClause <= 2) {
        const _cpDepth2 = state.choiceStack.length;
        const _savedBindingsSize2 = state.bindings.length;
        pushChoicePoint(state, append_3, 9999);
        const var__0 = createVar(state.nextVarId++); /* H */
        const var__1 = createVar(state.nextVarId++); /* T1 */
        const var__2 = createVar(state.nextVarId++); /* L2 */
        const var__3 = createVar(state.nextVarId++); /* T3 */
        if (unify(state, createList(var__0, var__1), arg1) &&
            unify(state, var__2, arg2) &&
            unify(state, createList(var__0, var__3), arg3)) {
            do {
                if (!append_3(state, var__1, var__2, var__3)) { state.failed = true; break; }
            } while (false);
            if (!state.failed) return true;
        }
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
        state.backtracking = false;
        if (startClause >= 9999) {
            state.failed = true;
            return false;
        }
    }

    /* Clause 1: max(X,Y,X) :- X >= Y, ! */
    if (startClause <= 1) {
        const _cpDepth1 = state.choiceStack.length;
        const _savedBindingsSize1 = state.bindings.length;
        pushChoicePoint(state, max_3, 2);
        const var__0 = createVar(state.nextVarId++); /* X */
        const var__1 = createVar(state.nextVarId++); /* Y */
        if (unify(state, var__0, arg1) &&
            unify(state, var__1, arg2) &&
            unify(state, var__0, arg3)) {
            do {
                if (!gte_2(state, var__0, var__1)) { state.failed = true; break; }
                performCut(state);
            } while (false);
            if (!state.failed) return true;
        }
        while (state.choiceStack.length > _cpDepth1) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize1);
        state.failed = false;
    }
    /* Clause 2: max(_,Y,Y) */
    if (startClause <= 2) {
        const _cpDepth2 = state.choiceStack.length;
        const _savedBindingsSize2 = state.bindings.length;
        pushChoicePoint(state, max_3, 9999);
        const var__0 = createVar(state.nextVarId++); /* _ */
        const var__1 = createVar(state.nextVarId++); /* Y */
        if (unify(state, var__1, arg2) &&
            unify(state, var__1, arg3)) {
            return true;
        }
        while (state.choiceStack.length > _cpDepth2) state.choiceStack.pop();
        state.bindings = state.bindings.slice(0, _savedBindingsSize2);
        state.failed = false;
    }
    return false; /* No clause matched */
}

function main_0(state) {
    /* Clause 1: main :- ... */
    {
        const _cpDepth = state.choiceStack.length;
        const _savedBindingsSize = state.bindings.length;
        const var__0 = createVar(state.nextVarId++); /* M */
        {
            do {
                if (!write_1(state, createAtom("=== Family Relationships ==="))) { state.failed = true; break; }
                if (!nl_0(state)) { state.failed = true; break; }
                /* If-then-else */
                {
                    const _ite_saved = state.bindings.length;
                    if (!grandparent_2(state, createAtom("tom"), createAtom("ann"))) { state.failed = true; }
                    if (!state.failed) {
                        if (!write_1(state, createAtom("grandparent(tom, ann) = true"))) { state.failed = true; break; }
                        if (!nl_0(state)) { state.failed = true; break; }
                    } else {
                        state.bindings = state.bindings.slice(0, _ite_saved);
                        state.failed = false;
                        if (!write_1(state, createAtom("grandparent(tom, ann) = false"))) { state.failed = true; break; }
                        if (!nl_0(state)) { state.failed = true; break; }
                    }
                }
                /* If-then-else */
                {
                    const _ite_saved2 = state.bindings.length;
                    if (!member_2(state, createAtom("bob"),
                                  createList(createAtom("tom"),
                                  createList(createAtom("bob"),
                                  createList(createAtom("liz"), createNil()))))) { state.failed = true; }
                    if (!state.failed) {
                        if (!write_1(state, createAtom("member(bob, [tom,bob,liz]) = true"))) { state.failed = true; break; }
                        if (!nl_0(state)) { state.failed = true; break; }
                    } else {
                        state.bindings = state.bindings.slice(0, _ite_saved2);
                        state.failed = false;
                        if (!write_1(state, createAtom("member(bob, [tom,bob,liz]) = false"))) { state.failed = true; break; }
                        if (!nl_0(state)) { state.failed = true; break; }
                    }
                }
                if (!max_3(state, createInt(3), createInt(5), var__0)) { state.failed = true; break; }
                if (!write_1(state, createAtom("max(3,5) = "))) { state.failed = true; break; }
                if (!write_1(state, var__0)) { state.failed = true; break; }
                if (!nl_0(state)) { state.failed = true; break; }
                if (!write_1(state, createAtom("=== Done ==="))) { state.failed = true; break; }
                if (!nl_0(state)) { state.failed = true; break; }
            } while (false);
            if (!state.failed) return true;
        }
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
