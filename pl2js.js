// pl2js.js — Prolog-to-JavaScript browser translator/runtime
//
// Translates a practical subset of Prolog into JavaScript-executable clause
// structures and provides a minimal execution engine for those structures.
//
// Design: translator-based (NOT a full interpreter / WAM / bytecode VM).
//   - Parse Prolog source into term data structures.
//   - Group clauses into a database by predicate key (name/arity).
//   - Execute queries by iterating clause structures with explicit unification
//     and continuation-passing backtracking.
//
// Supported subset:
//   facts, rules, atoms, integers, variables, compound terms, lists [H|T] / [],
//   conjunction (,), disjunction (;), if-then-else (Cond -> Then ; Else),
//   cut (!), negation-as-failure (\+), unification (=), \=, ==, \==,
//   arithmetic (is/2, >, <, >=, =<, =:=, =\=),
//   built-ins: true/0, fail/0, nl/0, write/1, writeln/1, writeq/1, tab/1,
//              atom/1, integer/1, number/1, var/1, nonvar/1, compound/1,
//              atomic/1, is_list/1, atom_concat/3, atom_length/2,
//              atom_chars/2, atom_codes/2, atom_string/2, atom_number/2,
//              number_codes/2, number_chars/2, number_string/2,
//              char_code/2, term_to_atom/2, term_string/2,
//              string_to_atom/2, string_codes/2, string_chars/2,
//              atomic_list_concat/2-3,
//              length/2, findall/3, succ/2, plus/3, functor/3,
//              flatten/2, max_list/2, min_list/2, sum_list/2, numlist/3,
//              maplist/2-5, include/3, exclude/3, convlist/3, foldl/4-7.
//
// Not supported (by design): floats, assert/retract, modules, DCG, exceptions,
//   operator declarations, full ISO compliance.
//
// Auto-loaded at startup (invisible to user programs, cannot be redefined):
//   A small Prolog prelude (_PRELUDE_SOURCE) is parsed and merged into every
//   query database before user clauses.  Predicates whose name/arity appear in
//   _BUILTIN_KEYS (JS-native) are rejected when user code tries to define them.

(function (root) {
  'use strict';

  // =========================================================================
  // SECTION 1: Term constructors
  // =========================================================================

  let _varIdCounter = 0;

  function mkVar(name) {
    return { type: 'var', name: name, id: ++_varIdCounter };
  }
  function mkAtom(name) { return { type: 'atom', name: name }; }
  function mkInt(val)   { return { type: 'int',  val: val  }; }
  function mkNil()      { return { type: 'nil'             }; }
  function mkList(head, tail) { return { type: 'list', head: head, tail: tail }; }
  function mkCompound(functor, args) {
    return { type: 'compound', functor: functor, arity: args.length, args: args };
  }

  // Build a list term from a JavaScript array of terms.
  function arrayToList(arr) {
    let t = mkNil();
    for (let i = arr.length - 1; i >= 0; i--) t = mkList(arr[i], t);
    return t;
  }

  // =========================================================================
  // SECTION 2: Tokenizer
  // =========================================================================

  // Token: { t: <type>, v: <value> }
  // Types: 'var','atom','int','float','op','end','(',')',  '[',']',',','|'

  function tokenize(src) {
    const toks = [];
    let i = 0;
    const len = src.length;

    while (i < len) {
      const ch = src[i];

      // Whitespace
      if (ch === ' ' || ch === '\t' || ch === '\r' || ch === '\n') { i++; continue; }

      // Line comment
      if (ch === '%') { while (i < len && src[i] !== '\n') i++; continue; }

      // Block comment
      if (ch === '/' && src[i + 1] === '*') {
        i += 2;
        while (i + 1 < len && !(src[i] === '*' && src[i + 1] === '/')) i++;
        i += 2;
        continue;
      }

      // Single-quoted atom
      if (ch === "'") {
        i++;
        let s = '';
        while (i < len) {
          if (src[i] === "'" && src[i + 1] === "'") { s += "'"; i += 2; }
          else if (src[i] === "'") { i++; break; }
          else if (src[i] === '\\' && i + 1 < len) {
            const esc = src[i + 1];
            if (esc === 'n') s += '\n';
            else if (esc === 't') s += '\t';
            else s += esc;
            i += 2;
          }
          else { s += src[i++]; }
        }
        toks.push({ t: 'atom', v: s });
        continue;
      }

      // Double-quoted string — treat as atom for simplicity
      if (ch === '"') {
        i++;
        let s = '';
        while (i < len && src[i] !== '"') {
          if (src[i] === '\\' && i + 1 < len) { i++; s += src[i++]; }
          else s += src[i++];
        }
        i++; // closing "
        toks.push({ t: 'atom', v: s });
        continue;
      }

      // Numbers (digit-starting)
      if (ch >= '0' && ch <= '9') {
        // 0'<char> character code notation
        if (ch === '0' && src[i + 1] === "'") {
          i += 2;
          toks.push({ t: 'int', v: src.charCodeAt(i++) });
          continue;
        }
        let s = '';
        while (i < len && src[i] >= '0' && src[i] <= '9') s += src[i++];
        if (src[i] === '.' && i + 1 < len && src[i + 1] >= '0' && src[i + 1] <= '9') {
          s += '.'; i++;
          while (i < len && src[i] >= '0' && src[i] <= '9') s += src[i++];
          toks.push({ t: 'int', v: Math.trunc(parseFloat(s)) }); // treat floats as ints
        } else {
          toks.push({ t: 'int', v: parseInt(s, 10) });
        }
        continue;
      }

      // Variable (uppercase or _)
      if ((ch >= 'A' && ch <= 'Z') || ch === '_') {
        let s = '';
        while (i < len && /[A-Za-z0-9_]/.test(src[i])) s += src[i++];
        toks.push({ t: 'var', v: s });
        continue;
      }

      // Lowercase atom or keyword
      if (ch >= 'a' && ch <= 'z') {
        let s = '';
        while (i < len && /[A-Za-z0-9_]/.test(src[i])) s += src[i++];
        toks.push({ t: 'atom', v: s });
        continue;
      }

      // Clause-terminating dot: '.' followed by whitespace or EOF
      if (ch === '.' && (i + 1 >= len || /[\s]/.test(src[i + 1]))) {
        toks.push({ t: 'end', v: '.' });
        i++;
        continue;
      }

      // Multi-char operators — check longest first
      const rest = src.slice(i);
      const ops3 = ['=:=', '=\\=', '=..', '\\==', '@>=', '@=<', '-->'];
      const ops2 = [':-', '->', '\\+', '\\=', '\\/', '/\\', '>=', '=<', '==',
                    '@<', '@>', '**', '<<', '>>'];
      let matched = false;
      for (const op of ops3) {
        if (rest.startsWith(op)) { toks.push({ t: 'op', v: op }); i += op.length; matched = true; break; }
      }
      if (!matched) {
        for (const op of ops2) {
          if (rest.startsWith(op)) { toks.push({ t: 'op', v: op }); i += op.length; matched = true; break; }
        }
      }
      if (matched) continue;

      // Single-char tokens
      if (ch === '!') { toks.push({ t: 'atom', v: '!' }); i++; continue; }
      if (ch === '(') { toks.push({ t: '(' }); i++; continue; }
      if (ch === ')') { toks.push({ t: ')' }); i++; continue; }
      if (ch === '[') { toks.push({ t: '[' }); i++; continue; }
      if (ch === ']') { toks.push({ t: ']' }); i++; continue; }
      if (ch === ',') { toks.push({ t: ',' }); i++; continue; }
      if (ch === '|') { toks.push({ t: '|' }); i++; continue; }
      if (ch === ';') { toks.push({ t: 'op', v: ';' }); i++; continue; }

      // Single-char operator chars
      if ('+-*/\\<>=^@'.indexOf(ch) >= 0) { toks.push({ t: 'op', v: ch }); i++; continue; }

      // Skip anything unrecognised
      i++;
    }
    return toks;
  }

  // =========================================================================
  // SECTION 3: Parser
  // =========================================================================

  // Operator table: op -> { prec, type }
  // type: xfx, xfy, yfx, fx, fy
  const OP_TABLE = {
    ':-':  { prec: 1200, type: 'xfx' },
    '-->': { prec: 1200, type: 'xfx' },
    ';':   { prec: 1100, type: 'xfy' },
    '->':  { prec: 1050, type: 'xfy' },
    ',':   { prec: 1000, type: 'xfy' },
    '\\+': { prec:  900, type: 'fy'  },
    '=':   { prec:  700, type: 'xfx' },
    '\\=': { prec:  700, type: 'xfx' },
    '==':  { prec:  700, type: 'xfx' },
    '\\==':{ prec:  700, type: 'xfx' },
    'is':  { prec:  700, type: 'xfx' },
    '>':   { prec:  700, type: 'xfx' },
    '<':   { prec:  700, type: 'xfx' },
    '>=':  { prec:  700, type: 'xfx' },
    '=<':  { prec:  700, type: 'xfx' },
    '=:=': { prec:  700, type: 'xfx' },
    '=\\=':{ prec:  700, type: 'xfx' },
    '=..': { prec:  700, type: 'xfx' },
    '@<':  { prec:  700, type: 'xfx' },
    '@>':  { prec:  700, type: 'xfx' },
    '@=<': { prec:  700, type: 'xfx' },
    '@>=': { prec:  700, type: 'xfx' },
    '+':   { prec:  500, type: 'yfx' },
    '-':   { prec:  500, type: 'yfx' },
    '\\/': { prec:  500, type: 'yfx' },
    '/\\': { prec:  500, type: 'yfx' },
    '*':   { prec:  400, type: 'yfx' },
    '/':   { prec:  400, type: 'yfx' },
    '//':  { prec:  400, type: 'yfx' },
    'mod': { prec:  400, type: 'yfx' },
    'rem': { prec:  400, type: 'yfx' },
    'xor': { prec:  400, type: 'yfx' },
    '>>':  { prec:  400, type: 'yfx' },
    '<<':  { prec:  400, type: 'yfx' },
    '**':  { prec:  200, type: 'xfx' },
    '^':   { prec:  200, type: 'xfy' },
  };

  function Parser(toks) {
    this.toks = toks;
    this.pos  = 0;
  }

  Parser.prototype.peek = function () { return this.toks[this.pos]; };
  Parser.prototype.next = function () { return this.toks[this.pos++]; };

  Parser.prototype.expect = function (t) {
    const tok = this.next();
    if (!tok) throw new Error('Expected ' + t + ' but got end of input');
    if (tok.t !== t) throw new Error('Expected ' + t + ' but got ' + tok.t + '(' + tok.v + ')');
    return tok;
  };

  // Is the current token a binary operator with prec <= maxPrec?
  Parser.prototype.peekBinOp = function (maxPrec) {
    const tok = this.peek();
    if (!tok) return null;
    let opStr = null;
    if (tok.t === 'op') opStr = tok.v;
    else if (tok.t === 'atom' && OP_TABLE[tok.v]) opStr = tok.v;
    else if (tok.t === ',' ) opStr = ',';
    if (!opStr) return null;
    const entry = OP_TABLE[opStr];
    if (!entry) return null;
    if (entry.prec > maxPrec) return null;
    return { opStr: opStr, entry: entry };
  };

  // parseTerm: operator-precedence Pratt parser
  Parser.prototype.parseTerm = function (maxPrec) {
    let left = this.parsePrefix(maxPrec);

    while (true) {
      const info = this.peekBinOp(maxPrec);
      if (!info) break;
      this.next(); // consume operator token

      const { opStr, entry } = info;
      // right-hand side precedence
      let rPrec = entry.type === 'xfx' ? entry.prec - 1 :
                  entry.type === 'xfy' ? entry.prec :
                  entry.type === 'yfx' ? entry.prec - 1 :
                  entry.prec - 1;

      // Comma in arg list context: stop if maxPrec < 1000
      if (opStr === ',' && maxPrec < 1000) break;

      const right = this.parseTerm(rPrec);
      left = mkCompound(opStr, [left, right]);
    }

    return left;
  };

  // Parse prefix (unary prefix operators and primary terms)
  Parser.prototype.parsePrefix = function (maxPrec) {
    const tok = this.peek();
    if (!tok) throw new Error('Unexpected end of input');

    // Prefix :- (fx 1200, directive syntax)
    if (tok.t === 'op' && tok.v === ':-') {
      this.next();
      const arg = this.parseTerm(1199);
      return mkCompound(':-', [arg]);
    }

    // Prefix \+  (fy 900)
    if (tok.t === 'op' && tok.v === '\\+') {
      this.next();
      const arg = this.parseTerm(900);
      return mkCompound('\\+', [arg]);
    }

    // Prefix - (fy 200 as unary minus)
    if (tok.t === 'op' && tok.v === '-') {
      this.next();
      const peek2 = this.peek();
      if (peek2 && peek2.t === 'int') {
        this.next();
        return mkInt(-peek2.v);
      }
      const arg = this.parseTerm(200);
      return mkCompound('-', [arg]);
    }

    // Prefix + (ignore)
    if (tok.t === 'op' && tok.v === '+') {
      this.next();
      return this.parseTerm(200);
    }

    // Prefix not (fy 900)
    if (tok.t === 'atom' && tok.v === 'not') {
      this.next();
      const arg = this.parseTerm(900);
      return mkCompound('\\+', [arg]);
    }

    return this.parsePrimary();
  };

  Parser.prototype.parsePrimary = function () {
    const tok = this.next();
    if (!tok) throw new Error('Unexpected end of input');

    // Variable
    if (tok.t === 'var') {
      const name = tok.v;
      if (name === '_') return mkVar('_'); // anonymous — always a fresh unique var
      // Within a clause, the same variable name must map to the same Var object.
      if (this._clauseVars) {
        if (!this._clauseVars[name]) this._clauseVars[name] = mkVar(name);
        return this._clauseVars[name];
      }
      return mkVar(name);
    }

    // Integer
    if (tok.t === 'int') return mkInt(tok.v);

    // Atom (possibly functor of compound, or special atoms)
    if (tok.t === 'atom') {
      const name = tok.v;
      // Check for compound: name(...)
      const peek = this.peek();
      if (peek && peek.t === '(') {
        this.next(); // consume '('
        const args = this.parseArgList();
        this.expect(')');
        return mkCompound(name, args);
      }
      return mkAtom(name);
    }

    // Operator used as atom/functor
    if (tok.t === 'op') {
      const name = tok.v;
      const peek = this.peek();
      if (peek && peek.t === '(') {
        this.next();
        const args = this.parseArgList();
        this.expect(')');
        return mkCompound(name, args);
      }
      return mkAtom(name);
    }

    // List [...]
    if (tok.t === '[') {
      const peek = this.peek();
      if (peek && peek.t === ']') { this.next(); return mkNil(); }
      return this.parseListBody();
    }

    // Parenthesised term
    if (tok.t === '(') {
      const t = this.parseTerm(1200);
      this.expect(')');
      return t;
    }

    throw new Error('Unexpected token: ' + JSON.stringify(tok));
  };

  // Parse comma-separated argument list (commas at prec 999)
  Parser.prototype.parseArgList = function () {
    const peek = this.peek();
    if (!peek || peek.t === ')') return [];
    const args = [this.parseTerm(999)];
    while (this.peek() && this.peek().t === ',') {
      this.next(); // consume ','
      args.push(this.parseTerm(999));
    }
    return args;
  };

  // Parse inside [ ... ] after consuming the first '[' (and not ']')
  Parser.prototype.parseListBody = function () {
    const head = this.parseTerm(999);
    const peek = this.peek();
    if (!peek) throw new Error('Unterminated list');
    if (peek.t === '|') {
      this.next();
      const tail = this.parseTerm(999);
      this.expect(']');
      return mkList(head, tail);
    }
    if (peek.t === ',') {
      this.next();
      return mkList(head, this.parseListBody());
    }
    if (peek.t === ']') {
      this.next();
      return mkList(head, mkNil());
    }
    throw new Error('Expected , or | or ] in list');
  };

  // Parse one clause from the token stream.
  // Returns {head, body} where body may be null (for facts).
  Parser.prototype.parseClause = function () {
    if (this.pos >= this.toks.length) return null;
    // Per-clause variable registry: same name -> same Var object.
    this._clauseVars = Object.create(null);
    const term = this.parseTerm(1200);
    this._clauseVars = null;
    this.expect('end');

    // term is either a plain head, or ':-'(head, body)
    if (term.type === 'compound' && term.functor === ':-' && term.arity === 2) {
      return { head: term.args[0], body: term.args[1] };
    }
    // Directives like :- use_module(...) — return for special handling
    if (term.type === 'compound' && term.functor === ':-' && term.arity === 1) {
      return { _directive: term.args[0] };
    }
    return { head: term, body: null };
  };

  // Parse a full Prolog source string into an array of {head, body} clauses.
  // Directives (:- ...) are silently ignored.
  function parsePrologSource(src) {
    const toks = tokenize(src);
    const parser = new Parser(toks);
    const clauses = [];
    while (parser.pos < parser.toks.length) {
      try {
        const cl = parser.parseClause();
        if (!cl) continue;
        if (cl._directive) {
          // All directives are silently ignored in user programs.
          // Use consult/1 or assertz/1 to load Prolog source at runtime.
          continue;
        }
        clauses.push(cl);
      } catch (e) {
        // Skip to the next '.' and continue
        while (parser.pos < parser.toks.length && parser.toks[parser.pos].t !== 'end') {
          parser.pos++;
        }
        parser.pos++; // skip the '.'
        // eslint-disable-next-line no-console
        console.warn('[pl2js] parse error (skipping clause):', e.message);
      }
    }
    return clauses;
  }

  // =========================================================================
  // SECTION 4: Variable renaming
  // =========================================================================
  // Before trying a clause, give every variable in it a fresh id so that
  // separate clause attempts don't share variable bindings.

  function renameClause(clause) {
    const map = Object.create(null); // oldId -> new Var term
    return {
      head: renameTerm(clause.head, map),
      body: clause.body ? renameTerm(clause.body, map) : null
    };
  }

  function renameTerm(term, map) {
    switch (term.type) {
      case 'var': {
        if (!map[term.id]) map[term.id] = mkVar(term.name);
        return map[term.id];
      }
      case 'atom': case 'int': case 'nil':
        return term;
      case 'compound':
        return mkCompound(term.functor, term.args.map(a => renameTerm(a, map)));
      case 'list':
        return mkList(renameTerm(term.head, map), renameTerm(term.tail, map));
      default:
        return term;
    }
  }

  // =========================================================================
  // SECTION 5: Environment, dereference, unification
  // =========================================================================

  // Environment: plain object { varId: Term }.
  // Variables are looked up by their numeric id.

  function deref(env, term) {
    while (term.type === 'var' && env[term.id] !== undefined) {
      term = env[term.id];
    }
    return term;
  }

  // Unify t1 and t2 in env (modifies env in place). Returns true on success.
  function unify(env, t1, t2) {
    t1 = deref(env, t1);
    t2 = deref(env, t2);
    if (t1 === t2) return true;

    if (t1.type === 'var') {
      // Occurs check omitted (for performance, same as most Prolog systems by default)
      env[t1.id] = t2;
      return true;
    }
    if (t2.type === 'var') {
      env[t2.id] = t1;
      return true;
    }

    // nil == atom '[]'
    if (t1.type === 'nil' && t2.type === 'atom' && t2.name === '[]') return true;
    if (t2.type === 'nil' && t1.type === 'atom' && t1.name === '[]') return true;

    if (t1.type !== t2.type) return false;

    switch (t1.type) {
      case 'atom': return t1.name === t2.name;
      case 'int':  return t1.val  === t2.val;
      case 'nil':  return true;
      case 'compound':
        if (t1.functor !== t2.functor || t1.arity !== t2.arity) return false;
        for (let i = 0; i < t1.arity; i++) {
          if (!unify(env, t1.args[i], t2.args[i])) return false;
        }
        return true;
      case 'list':
        return unify(env, t1.head, t2.head) && unify(env, t1.tail, t2.tail);
      default:
        return false;
    }
  }

  // Shallow copy of env for backtracking (snapshot before a clause attempt).
  function copyEnv(env) { return Object.assign(Object.create(null), env); }

  // Walk env to produce a fully-instantiated copy of term (for display / findall templates).
  function applyEnv(env, term) {
    term = deref(env, term);
    switch (term.type) {
      case 'var':  return term; // unbound
      case 'atom': case 'int': case 'nil': return term;
      case 'compound':
        return mkCompound(term.functor, term.args.map(a => applyEnv(env, a)));
      case 'list':
        return mkList(applyEnv(env, term.head), applyEnv(env, term.tail));
      default: return term;
    }
  }

  // =========================================================================
  // SECTION 6: Clause database
  // =========================================================================

  function predicateKey(head) {
    if (head.type === 'atom')     return head.name + '/0';
    if (head.type === 'compound') return head.functor + '/' + head.arity;
    return '?/0';
  }

  // buildDatabase(clauses, opts)
  //   opts.rejectBuiltins (default true) — throw on clauses that redefine a
  //   JS-native built-in listed in _BUILTIN_KEYS.
  //   opts.system (default false) — mark all clauses as system predicates
  //   (loaded from the prelude; they can be overridden by user code but are
  //   not "visible" in the user's source).
  function buildDatabase(clauses, opts) {
    const rejectBuiltins = !opts || opts.rejectBuiltins !== false;
    const system         = opts && opts.system === true;
    const db = Object.create(null); // 'name/arity' -> [{head, body, system?}]
    for (const cl of clauses) {
      const key = predicateKey(cl.head);
      if (rejectBuiltins && _BUILTIN_KEYS.has(key)) {
        throw new Error('Permission error: cannot redefine built-in predicate ' + key);
      }
      if (!db[key]) db[key] = [];
      db[key].push(system ? Object.assign({}, cl, { system: true }) : cl);
    }
    return db;
  }

  // =========================================================================
  // SECTION 7: Term display
  // =========================================================================

  function termToString(env, term) {
    return _termStr(env, deref(env, term));
  }

  function _termStr(env, term) {
    switch (term.type) {
      case 'var':  return '_';
      case 'atom': return term.name;
      case 'int':  return String(term.val);
      case 'nil':  return '[]';
      case 'list': {
        const parts = [];
        let cur = term;
        while (cur.type === 'list') {
          parts.push(_termStr(env, deref(env, cur.head)));
          cur = deref(env, cur.tail);
        }
        if (cur.type !== 'nil') return '[' + parts.join(',') + '|' + _termStr(env, cur) + ']';
        return '[' + parts.join(',') + ']';
      }
      case 'compound': {
        const f = term.functor;
        const a = term.arity;
        // Infix operators — pretty-print
        const INFIX = {',':1,';':1,'->':1,'+':1,'-':1,'*':1,'/':1,'//':1,
                       'mod':1,'is':1,'=':1,'\\=':1,'==':1,'\\==':1,
                       '>':1,'<':1,'>=':1,'=<':1,'=:=':1,'=\\=':1,'=..':1};
        if (a === 2 && INFIX[f]) {
          const l = _termStr(env, deref(env, term.args[0]));
          const r = _termStr(env, deref(env, term.args[1]));
          return '(' + l + f + r + ')';
        }
        if (a === 1 && (f === '\\+' || f === '-')) {
          return f + _termStr(env, deref(env, term.args[0]));
        }
        const args = term.args.map(a2 => _termStr(env, deref(env, a2)));
        return f + '(' + args.join(',') + ')';
      }
      default: return '?';
    }
  }

  // =========================================================================
  // SECTION 8: Arithmetic evaluator
  // =========================================================================

  function evalArith(env, term) {
    term = deref(env, term);
    if (term.type === 'int') return term.val;
    if (term.type === 'atom') {
      if (term.name === 'pi')       return Math.round(Math.PI * 1e9) / 1e9; // approx int-friendly
      if (term.name === 'max_tagged_integer') return 2147483647;
      return null;
    }
    if (term.type === 'compound') {
      const f = term.functor;
      if (term.arity === 2) {
        const l = evalArith(env, term.args[0]);
        const r = evalArith(env, term.args[1]);
        if (l === null || r === null) return null;
        if (f === '+')    return l + r;
        if (f === '-')    return l - r;
        if (f === '*')    return l * r;
        if (f === '/')    return r !== 0 ? Math.trunc(l / r) : null;
        if (f === '//')   return r !== 0 ? Math.trunc(l / r) : null;
        if (f === 'mod')  return ((l % r) + r) % r;
        if (f === 'rem')  return l % r;
        if (f === '**')   return Math.pow(l, r) | 0;
        if (f === '^')    return Math.pow(l, r) | 0;
        if (f === '>>')   return l >> r;
        if (f === '<<')   return l << r;
        if (f === '/\\')  return l & r;
        if (f === '\\/')  return l | r;
        if (f === 'xor')  return l ^ r;
        if (f === 'min')  return Math.min(l, r);
        if (f === 'max')  return Math.max(l, r);
        if (f === 'gcd')  { let a = Math.abs(l), b = Math.abs(r); while (b) { const t = b; b = a % b; a = t; } return a; }
      }
      if (term.arity === 1) {
        const v = evalArith(env, term.args[0]);
        if (v === null) return null;
        if (f === '-')        return -v;
        if (f === '+')        return v;
        if (f === 'abs')      return Math.abs(v);
        if (f === 'sign')     return Math.sign(v);
        if (f === 'sqrt')     return Math.trunc(Math.sqrt(v));
        if (f === 'floor')    return Math.floor(v);
        if (f === 'ceiling')  return Math.ceil(v);
        if (f === 'round')    return Math.round(v);
        if (f === 'truncate') return Math.trunc(v);
        if (f === '\\')       return ~v;
        if (f === 'float_integer_part') return Math.trunc(v);
        if (f === 'integer')  return Math.trunc(v);
        if (f === 'msb')      return 31 - Math.clz32(v);
      }
    }
    return null;
  }

  // =========================================================================
  // SECTION 9: Built-in registry, prelude, and goal execution
  // =========================================================================

  // Fallback file system used by save_file/2 and save_folder/2 in environments
  // where neither Node.js fs nor the browser Blob/download APIs are available
  // (e.g. Node.js environments without __dirname, or test harnesses).
  // Keys are file paths; values are source strings.
  const _vfs = Object.create(null);

  // Browser file store — populated by pl2js.loadFile(name, content).
  // read_file/2 and read_folder/2 in browser environments look here for files
  // that the user has loaded via the dialogue-box (Load File / Load Folder)
  // before running a query.  Use the Load File and Load Folder buttons in
  // index.html (or call pl2js.loadFile() programmatically) to register files.
  const _browserFiles = Object.create(null);

  // Set of 'name/arity' keys for every predicate implemented natively in JS.
  // buildDatabase rejects user clauses whose key appears here.
  const _BUILTIN_KEYS = new Set([
    // Control flow
    'true/0', 'fail/0', 'false/0', 'nl/0', '!/0',
    ',/2', ';/2', '->/2', '\\+/1', 'not/1',
    // Unification / comparison
    '=/2', '\\=/2', '==/2', '\\==/2',
    '@</2', '@>/2', '@=</2', '@>=/2', 'compare/3',
    // Arithmetic
    'is/2', '>/2', '</2', '>=/2', '=</2', '=:=/2', '=\\=/2',
    // I/O
    'write/1', 'writeln/1', 'writeq/1', 'write_term/2', 'print/1',
    'tab/1', 'format/1', 'format/2',
    // Type checks
    'atom/1', 'integer/1', 'number/1', 'float/1',
    'var/1', 'nonvar/1', 'compound/1', 'atomic/1', 'callable/1',
    'is_list/1', 'ground/1', 'string/1',
    // Term manipulation
    'functor/3', 'arg/3', '=../2', 'copy_term/2',
    // Atom / string / char conversions (all directions)
    'atom_length/2', 'atom_concat/3',
    'atom_chars/2', 'atom_codes/2', 'atom_number/2', 'atom_string/2',
    'number_codes/2', 'number_chars/2', 'number_string/2',
    'char_code/2',
    'term_to_atom/2', 'term_string/2',
    'upcase_atom/2', 'downcase_atom/2',
    'string_concat/3', 'string_to_atom/2', 'string_length/2',
    'string_codes/2', 'string_chars/2',
    'atomic_list_concat/2', 'atomic_list_concat/3',
    'char_type/2',
    // List predicates
    'length/2', 'last/2', 'nth0/3', 'nth1/3', 'reverse/2',
    'sort/2', 'msort/2',
    'flatten/2', 'max_list/2', 'min_list/2', 'sum_list/2', 'numlist/3',
    'list_to_set/2', 'permutation/2', 'select/3',
    'subtract/3', 'intersection/3', 'union/3', 'delete/3',
    // Findall family
    'findall/3', 'aggregate_all/3', 'bagof/3', 'setof/3', 'forall/2',
    // Control
    'once/1', 'ignore/1',
    'call/1', 'call/2', 'call/3', 'call/4',
    'call/5', 'call/6', 'call/7', 'call/8',
    // Arithmetic helpers
    'succ/2', 'plus/3', 'between/3', 'succ_or_zero/2',
    // Higher-order
    'maplist/2', 'maplist/3', 'maplist/4', 'maplist/5',
    'include/3', 'exclude/3', 'convlist/3',
    'foldl/4', 'foldl/5', 'foldl/6', 'foldl/7',
    // Side-effect / meta
    'assert/1', 'asserta/1', 'assertz/1', 'retract/1', 'abolish/1',
    'nb_getval/2', 'nb_setval/2', 'b_setval/2', 'b_getval/2',
    'read_term/2', 'with_output_to/2', 'predsort/3',
    // Form / CGI
    'read_string/1', 'read_string/2', 'form_argument/2', 'hidden_field/2',
    // File / folder I/O
    'read_file/2', 'save_file/2', 'read_folder/2', 'save_folder/2',
    // Dynamic loading
    'consult/1',
  ]);

  // Prolog source loaded into every query database before user clauses.
  // The prelude predicates are defined inline here (previously they were loaded
  // via :- include(File). directives from the extras/ directory, but that
  // mechanism has been replaced with this inline approach so the prelude works
  // reliably in both Node.js and browser environments without requiring file
  // access).  Only the JS-native predicates in _BUILTIN_KEYS are permanently
  // protected; prelude predicates can be overridden by user code.
  const _PRELUDE_SOURCE = [
    '% extras/strings.pl — string convenience predicates',
    'string_lower(X, Y) :- downcase_atom(X, Y).',
    'string_upper(X, Y) :- upcase_atom(X, Y).',
    '% extras/lists.pl — extra list predicates',
    'not_member(_, []).',
    'not_member(X, [H|T]) :- X \\= H, not_member(X, T).',
    'max_member(Max, [Max]).',
    'max_member(Max, [H|T]) :- max_member(TMax, T), (H @>= TMax -> Max = H ; Max = TMax).',
    'min_member(Min, [Min]).',
    'min_member(Min, [H|T]) :- min_member(TMin, T), (H @=< TMin -> Min = H ; Min = TMin).',
    '% extras/pairs.pl — Key-Value pair predicates',
    'pairs_keys_values([], [], []).',
    'pairs_keys_values([K-V|Ps], [K|Ks], [V|Vs]) :- pairs_keys_values(Ps, Ks, Vs).',
    'pairs_keys([], []).',
    'pairs_keys([K-_|Ps], [K|Ks]) :- pairs_keys(Ps, Ks).',
    'pairs_values([], []).',
    'pairs_values([_-V|Ps], [V|Vs]) :- pairs_values(Ps, Vs).',
  ].join('\n');

  // solve(goal, env, db, depth, k)
  //   Calls k(env_solution) for each solution.
  //   Throws {cut:true} when cut fires (caught at clause-iteration level).
  //   Throws {stop:true} when the answer limit is reached (caught at top level).

  // Builds a ZIP blob (store, no compression) from an array of {name, content} pairs.
  // Used by save_folder/2 in browser environments.
  function _buildZipBlob(folderName, pairs) {
    function strToBytes(s) {
      var buf = [];
      for (var i = 0; i < s.length; i++) {
        var c = s.charCodeAt(i);
        if (c < 128) {
          buf.push(c);
        } else if (c < 2048) {
          buf.push((c >> 6) | 192, (c & 63) | 128);
        } else {
          buf.push((c >> 12) | 224, ((c >> 6) & 63) | 128, (c & 63) | 128);
        }
      }
      return new Uint8Array(buf);
    }
    function uint16LE(n) { return [n & 0xff, (n >> 8) & 0xff]; }
    function uint32LE(n) { return [n & 0xff, (n >> 8) & 0xff, (n >> 16) & 0xff, (n >> 24) & 0xff]; }
    function crc32(bytes) {
      var table = [];
      for (var i = 0; i < 256; i++) {
        var c = i;
        for (var j = 0; j < 8; j++) c = (c & 1) ? (0xEDB88320 ^ (c >>> 1)) : (c >>> 1);
        table[i] = c;
      }
      var crc = 0xFFFFFFFF;
      for (var k = 0; k < bytes.length; k++) crc = table[(crc ^ bytes[k]) & 0xff] ^ (crc >>> 8);
      return (crc ^ 0xFFFFFFFF) >>> 0;
    }
    var locals = [];
    var central = [];
    var offset = 0;
    var prefix = folderName.endsWith('/') ? folderName : folderName + '/';
    for (var i = 0; i < pairs.length; i++) {
      var entryName = prefix + pairs[i].name;
      var nameBytes = strToBytes(entryName);
      var dataBytes = strToBytes(pairs[i].content);
      var crc       = crc32(dataBytes);
      var local = [].concat(
        [0x50, 0x4B, 0x03, 0x04],  // signature
        uint16LE(20),               // version needed
        uint16LE(0),                // flags
        uint16LE(0),                // compression: store
        uint16LE(0), uint16LE(0),   // mod time, mod date
        uint32LE(crc),
        uint32LE(dataBytes.length),
        uint32LE(dataBytes.length),
        uint16LE(nameBytes.length),
        uint16LE(0)                 // extra length
      );
      for (var j = 0; j < nameBytes.length; j++) local.push(nameBytes[j]);
      for (var j = 0; j < dataBytes.length; j++) local.push(dataBytes[j]);
      var cent = [].concat(
        [0x50, 0x4B, 0x01, 0x02],  // central dir signature
        uint16LE(20), uint16LE(20),
        uint16LE(0), uint16LE(0),
        uint16LE(0), uint16LE(0),
        uint32LE(crc),
        uint32LE(dataBytes.length),
        uint32LE(dataBytes.length),
        uint16LE(nameBytes.length),
        uint16LE(0), uint16LE(0),
        uint16LE(0), uint16LE(0),
        uint32LE(0),
        uint32LE(offset)
      );
      for (var j = 0; j < nameBytes.length; j++) cent.push(nameBytes[j]);
      locals.push(local);
      central.push(cent);
      offset += local.length;
    }
    var centralBytes = [].concat.apply([], central);
    var eocd = [].concat(
      [0x50, 0x4B, 0x05, 0x06],
      uint16LE(0), uint16LE(0),
      uint16LE(pairs.length), uint16LE(pairs.length),
      uint32LE(centralBytes.length),
      uint32LE(offset),
      uint16LE(0)
    );
    var all = [].concat.apply([], locals).concat(centralBytes).concat(eocd);
    return new Blob([new Uint8Array(all)], { type: 'application/zip' });
  }



  const MAX_DEPTH   = 500;  // guard against infinite recursion
  let   _output     = '';   // captured write/nl output
  let   _formArgs   = {};   // form arguments passed in (URL params / POST data)
  let   _formInputs = [];   // form inputs collected by read_string / hidden_field
  let   _readStringCounter = 0;  // sequential counter for read_string field names

  function solve(goal, env, db, depth, k) {
    if (depth > MAX_DEPTH) throw new Error('Maximum depth exceeded (possible infinite loop)');

    goal = deref(env, goal);

    // ---- Atom goals ----
    if (goal.type === 'atom') {
      const n = goal.name;
      if (n === 'true')  { k(env); return; }
      if (n === 'fail' || n === 'false') { return; }
      if (n === 'nl')    { _output += '\n'; k(env); return; }
      if (n === '!')     { k(env); throw { cut: true }; }
      // 0-arity user predicate
      solveUserPred(goal.name, 0, [], env, db, depth, k);
      return;
    }

    if (goal.type !== 'compound') { k(env); return; } // numbers, nil => treat as true

    const f = goal.functor;
    const a = goal.arity;

    // ---- Conjunction ----
    if (f === ',' && a === 2) {
      solve(goal.args[0], env, db, depth + 1, function (env2) {
        solve(goal.args[1], env2, db, depth + 1, k);
      });
      return;
    }

    // ---- Disjunction (also handles if-then-else) ----
    if (f === ';' && a === 2) {
      const left = deref(env, goal.args[0]);
      // if-then-else: (Cond -> Then ; Else)
      if (left.type === 'compound' && left.functor === '->' && left.arity === 2) {
        let condSucceeded = false;
        try {
          solve(left.args[0], env, db, depth + 1, function (env2) {
            if (!condSucceeded) {
              condSucceeded = true;
              solve(left.args[1], env2, db, depth + 1, k);
            }
          });
        } catch (e) { if (!e.cut) throw e; }
        if (!condSucceeded) {
          solve(goal.args[1], env, db, depth + 1, k);
        }
        return;
      }
      // Plain disjunction
      let cutLeft = false;
      try {
        solve(goal.args[0], env, db, depth + 1, k);
      } catch (e) {
        if (e.cut) cutLeft = true; else throw e;
      }
      if (!cutLeft) solve(goal.args[1], env, db, depth + 1, k);
      return;
    }

    // ---- If-then (no else) ----
    if (f === '->' && a === 2) {
      let done = false;
      try {
        solve(goal.args[0], env, db, depth + 1, function (env2) {
          if (!done) { done = true; solve(goal.args[1], env2, db, depth + 1, k); }
        });
      } catch (e) { if (!e.cut) throw e; }
      return;
    }

    // ---- Cut ----
    if (f === '!' && a === 0) { k(env); throw { cut: true }; }

    // ---- Negation as failure ----
    if (f === '\\+' && a === 1) {
      let found = false;
      try { solve(goal.args[0], env, db, depth + 1, function () { found = true; }); }
      catch (e) { if (!e.cut) throw e; }
      if (!found) k(env);
      return;
    }

    // ---- Unification ----
    if (f === '=' && a === 2) {
      const e2 = copyEnv(env);
      if (unify(e2, goal.args[0], goal.args[1])) k(e2);
      return;
    }
    if (f === '\\=' && a === 2) {
      const e2 = copyEnv(env);
      if (!unify(e2, goal.args[0], goal.args[1])) k(env);
      return;
    }
    if (f === '==' && a === 2) {
      if (termsEqual(applyEnv(env, goal.args[0]), applyEnv(env, goal.args[1]))) k(env);
      return;
    }
    if (f === '\\==' && a === 2) {
      if (!termsEqual(applyEnv(env, goal.args[0]), applyEnv(env, goal.args[1]))) k(env);
      return;
    }

    // ---- Arithmetic ----
    if (f === 'is' && a === 2) {
      const val = evalArith(env, goal.args[1]);
      if (val !== null) {
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[0], mkInt(val))) k(e2);
      }
      return;
    }
    if (a === 2 && (f === '>' || f === '<' || f === '>=' || f === '=<' || f === '=:=' || f === '=\\=')) {
      const l = evalArith(env, goal.args[0]);
      const r = evalArith(env, goal.args[1]);
      if (l !== null && r !== null) {
        const ok = f === '>'   ? l > r  :
                   f === '<'   ? l < r  :
                   f === '>='  ? l >= r :
                   f === '=<'  ? l <= r :
                   f === '=:=' ? l === r : l !== r;
        if (ok) k(env);
      }
      return;
    }

    // ---- I/O ----
    if (f === 'write' && a === 1) {
      _output += termToString(env, goal.args[0]);
      k(env);
      return;
    }
    if (f === 'writeln' && a === 1) {
      _output += termToString(env, goal.args[0]) + '\n';
      k(env);
      return;
    }
    if (f === 'write_term' && a === 2) {
      // simplified: ignore options
      _output += termToString(env, goal.args[0]);
      k(env);
      return;
    }
    if (f === 'nl' && a === 0) { _output += '\n'; k(env); return; }
    if (f === 'tab' && a === 1) {
      const t = deref(env, goal.args[0]);
      if (t.type === 'int' && t.val > 0) _output += ' '.repeat(t.val);
      k(env);
      return;
    }
    if (f === 'print' && a === 1) {
      _output += termToString(env, goal.args[0]);
      k(env);
      return;
    }
    if (f === 'format' && a === 2) {
      const fmt = deref(env, goal.args[0]);
      if (fmt.type === 'atom') {
        let s = fmt.name;
        let argList = deref(env, goal.args[1]);
        let out = '';
        for (let i = 0; i < s.length; i++) {
          if (s[i] === '~' && i + 1 < s.length) {
            const spec = s[++i];
            if (spec === 'n') { out += '\n'; }
            else if (spec === 'w' || spec === 'a' || spec === 'p') {
              if (argList.type === 'list') {
                out += termToString(env, argList.head);
                argList = deref(env, argList.tail);
              }
            }
            else if (spec === 'd' || spec === 'D') {
              if (argList.type === 'list') {
                out += termToString(env, argList.head);
                argList = deref(env, argList.tail);
              }
            }
            else out += spec;
          } else {
            out += s[i];
          }
        }
        _output += out;
      }
      k(env);
      return;
    }
    if (f === 'format' && a === 1) {
      const fmt = deref(env, goal.args[0]);
      if (fmt.type === 'atom') {
        _output += fmt.name.replace(/~n/g, '\n');
      }
      k(env);
      return;
    }

    // ---- File / folder I/O ----
    if (f === 'read_file' && a === 2) {
      const pathT = deref(env, goal.args[0]);
      if (pathT.type !== 'atom') throw new Error('read_file/2: Path must be an atom');
      const p = pathT.name;
      let content;
      if (typeof require !== 'undefined' && typeof __dirname !== 'undefined') {
        // Node.js: try real filesystem first, then fall back to browser file store
        // (the browser file store is populated by pl2js.loadFile() and is useful
        // for testing or for programs that use loadFile() rather than disk paths).
        try {
          const _fs = require('fs');
          content = _fs.readFileSync(p, 'utf8');
        } catch (e) {
          if (_browserFiles[p] !== undefined) {
            content = _browserFiles[p];
          } else {
            throw new Error('read_file/2: cannot read file \'' + p + '\': ' + e.message);
          }
        }
      } else if (_browserFiles[p] !== undefined) {
        // Browser: read from the browser file store (populated via pl2js.loadFile()
        // or the Load File / Load Folder buttons in the UI).
        content = _browserFiles[p];
      } else {
        throw new Error('read_file/2: file not found: \'' + p + '\'. ' +
          'In a browser, use the Load File button (or pl2js.loadFile()) to ' +
          'make files available before calling read_file/2.');
      }
      const e2 = copyEnv(env);
      if (unify(e2, goal.args[1], mkAtom(content))) k(e2);
      return;
    }

    if (f === 'save_file' && a === 2) {
      const pathT    = deref(env, goal.args[0]);
      const contentT = deref(env, goal.args[1]);
      if (pathT.type !== 'atom')    throw new Error('save_file/2: Path must be an atom');
      if (contentT.type !== 'atom') throw new Error('save_file/2: Content must be an atom');
      const p = pathT.name;
      const c = contentT.name;
      if (typeof require !== 'undefined' && typeof __dirname !== 'undefined') {
        // Node.js: write to real filesystem
        try {
          const _fs = require('fs');
          _fs.writeFileSync(p, c, 'utf8');
        } catch (e) {
          throw new Error('save_file/2: cannot write file \'' + p + '\': ' + e.message);
        }
      } else if (typeof Blob !== 'undefined' && typeof document !== 'undefined') {
        // Browser: trigger a download
        const blob = new Blob([c], { type: 'text/plain' });
        const url  = URL.createObjectURL(blob);
        const a2   = document.createElement('a');
        a2.href     = url;
        a2.download = p.split('/').pop() || p;
        document.body.appendChild(a2);
        a2.click();
        document.body.removeChild(a2);
        URL.revokeObjectURL(url);
      } else {
        // Fallback: store in VFS so the content is retrievable in tests
        _vfs[p] = c;
      }
      k(env);
      return;
    }

    if (f === 'read_folder' && a === 2) {
      const pathT = deref(env, goal.args[0]);
      if (pathT.type !== 'atom') throw new Error('read_folder/2: Path must be an atom');
      const p = pathT.name;
      let names;
      if (typeof require !== 'undefined' && typeof __dirname !== 'undefined') {
        // Node.js: recursively list real directory, returning relative paths
        try {
          const _fs   = require('fs');
          const _path = require('path');
          function _readDirRec(dir, base) {
            const entries = _fs.readdirSync(dir, { withFileTypes: true });
            const results = [];
            for (let ei = 0; ei < entries.length; ei++) {
              const entry   = entries[ei];
              const relPath = base ? base + '/' + entry.name : entry.name;
              if (entry.isDirectory()) {
                const sub = _readDirRec(_path.join(dir, entry.name), relPath);
                for (let si = 0; si < sub.length; si++) results.push(sub[si]);
              } else {
                results.push(relPath);
              }
            }
            return results;
          }
          names = _readDirRec(p, '');
        } catch (e) {
          throw new Error('read_folder/2: cannot read folder \'' + p + '\': ' + e.message);
        }
      } else {
        // Browser: list all files in the browser file store whose path starts
        // with p + '/', returning relative paths (including nested paths such
        // as 'subdir/file.txt').  Files are loaded via pl2js.loadFile() or
        // the Load File / Load Folder buttons in the UI.
        const prefix = p.endsWith('/') ? p : p + '/';
        names = Object.keys(_browserFiles)
          .filter(function (k2) { return k2.indexOf(prefix) === 0; })
          .map(function (k2) { return k2.slice(prefix.length); });
      }
      const fileList = arrayToList(names.map(mkAtom));
      const e2 = copyEnv(env);
      if (unify(e2, goal.args[1], fileList)) k(e2);
      return;
    }

    if (f === 'save_folder' && a === 2) {
      // save_folder(+Path, +FileList)
      // FileList is a list of file(Name, Content) compound terms.
      const pathT    = deref(env, goal.args[0]);
      const filesArg = deref(env, goal.args[1]);
      if (pathT.type !== 'atom') throw new Error('save_folder/2: Path must be an atom');
      const dir   = pathT.name;
      const files = listToArray(filesArg, env);
      if (!files) throw new Error('save_folder/2: FileList must be a proper list');
      // Build an array of {name, content} pairs
      const pairs = [];
      for (let i = 0; i < files.length; i++) {
        const ft = deref(env, files[i]);
        if (ft.type !== 'compound' || ft.functor !== 'file' || ft.arity !== 2)
          throw new Error('save_folder/2: each element must be file(Name, Content)');
        const nameT    = deref(env, ft.args[0]);
        const contentT = deref(env, ft.args[1]);
        if (nameT.type !== 'atom')    throw new Error('save_folder/2: file Name must be an atom');
        if (contentT.type !== 'atom') throw new Error('save_folder/2: file Content must be an atom');
        pairs.push({ name: nameT.name, content: contentT.name });
      }
      if (typeof require !== 'undefined' && typeof __dirname !== 'undefined') {
        // Node.js: create directory and write each file, creating subdirectories as needed
        try {
          const _fs   = require('fs');
          const _path = require('path');
          _fs.mkdirSync(dir, { recursive: true });
          for (let i = 0; i < pairs.length; i++) {
            const filePath = _path.join(dir, pairs[i].name);
            _fs.mkdirSync(_path.dirname(filePath), { recursive: true });
            _fs.writeFileSync(filePath, pairs[i].content, 'utf8');
          }
        } catch (e) {
          throw new Error('save_folder/2: cannot save folder \'' + dir + '\': ' + e.message);
        }
      } else if (typeof Blob !== 'undefined' && typeof document !== 'undefined') {
        // Browser: build a ZIP archive (store, no compression) and download it
        const zipBlob = _buildZipBlob(dir, pairs);
        const url  = URL.createObjectURL(zipBlob);
        const a2   = document.createElement('a');
        a2.href     = url;
        a2.download = (dir.split('/').pop() || dir) + '.zip';
        document.body.appendChild(a2);
        a2.click();
        document.body.removeChild(a2);
        URL.revokeObjectURL(url);
      } else {
        // Fallback: store each file in VFS
        const prefix = dir.endsWith('/') ? dir : dir + '/';
        for (let i = 0; i < pairs.length; i++) {
          _vfs[prefix + pairs[i].name] = pairs[i].content;
        }
      }
      k(env);
      return;
    }


    if (f === 'atom' && a === 1) {
      const t = deref(env, goal.args[0]);
      if (t.type === 'atom' || t.type === 'nil') k(env);
      return;
    }
    if (f === 'integer' && a === 1) {
      if (deref(env, goal.args[0]).type === 'int') k(env);
      return;
    }
    if (f === 'number' && a === 1) {
      if (deref(env, goal.args[0]).type === 'int') k(env);
      return;
    }
    if (f === 'var' && a === 1) {
      if (deref(env, goal.args[0]).type === 'var') k(env);
      return;
    }
    if (f === 'nonvar' && a === 1) {
      if (deref(env, goal.args[0]).type !== 'var') k(env);
      return;
    }
    if (f === 'compound' && a === 1) {
      const t = deref(env, goal.args[0]);
      if (t.type === 'compound' || t.type === 'list') k(env);
      return;
    }
    if (f === 'atomic' && a === 1) {
      const t = deref(env, goal.args[0]);
      if (t.type === 'atom' || t.type === 'int' || t.type === 'nil') k(env);
      return;
    }
    if (f === 'callable' && a === 1) {
      const t = deref(env, goal.args[0]);
      if (t.type === 'atom' || t.type === 'compound') k(env);
      return;
    }
    if (f === 'is_list' && a === 1) {
      if (isList(deref(env, goal.args[0]), env)) k(env);
      return;
    }
    if (f === 'ground' && a === 1) {
      if (isGround(applyEnv(env, goal.args[0]))) k(env);
      return;
    }

    // ---- Atom operations ----
    if (f === 'atom_concat' && a === 3) {
      const t1 = deref(env, goal.args[0]);
      const t2 = deref(env, goal.args[1]);
      if ((t1.type === 'atom' || t1.type === 'int' || t1.type === 'nil') &&
          (t2.type === 'atom' || t2.type === 'int' || t2.type === 'nil')) {
        const s1 = t1.type === 'atom' ? t1.name : t1.type === 'nil' ? '[]' : String(t1.val);
        const s2 = t2.type === 'atom' ? t2.name : t2.type === 'nil' ? '[]' : String(t2.val);
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[2], mkAtom(s1 + s2))) k(e2);
      }
      return;
    }
    if (f === 'atom_length' && a === 2) {
      const t = deref(env, goal.args[0]);
      if (t.type === 'atom') {
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[1], mkInt(t.name.length))) k(e2);
      }
      return;
    }
    if (f === 'atom_chars' && a === 2) {
      const t = deref(env, goal.args[0]);
      const t2 = deref(env, goal.args[1]);
      if (t.type === 'atom') {
        const chars = arrayToList(t.name.split('').map(c => mkAtom(c)));
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[1], chars)) k(e2);
      } else if (t.type === 'var' && t2.type !== 'var') {
        // Reverse: build atom from char list
        let cur = t2; let s = '';
        while (cur.type === 'list') {
          const h = deref(env, cur.head);
          if (h.type !== 'atom') { cur = null; break; }
          s += h.name;
          cur = deref(env, cur.tail);
        }
        if (cur && cur.type === 'nil') {
          const e2 = copyEnv(env);
          if (unify(e2, goal.args[0], mkAtom(s))) k(e2);
        }
      }
      return;
    }
    if (f === 'atom_codes' && a === 2) {
      const t  = deref(env, goal.args[0]);
      const t2 = deref(env, goal.args[1]);
      if (t.type === 'atom' || t.type === 'int') {
        // Forward: atom/number → code list
        const s = t.type === 'atom' ? t.name : String(t.val);
        const codes = arrayToList(s.split('').map(c => mkInt(c.charCodeAt(0))));
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[1], codes)) k(e2);
      } else if (t.type === 'var') {
        // Reverse: code list → atom
        const arr = listToArray(t2, env);
        if (arr) {
          let s = ''; let ok = true;
          for (const el of arr) {
            const d = deref(env, el);
            if (d.type !== 'int') { ok = false; break; }
            s += String.fromCharCode(d.val);
          }
          if (ok) { const e2 = copyEnv(env); if (unify(e2, goal.args[0], mkAtom(s))) k(e2); }
        }
      }
      return;
    }
    if (f === 'char_code' && a === 2) {
      const t1 = deref(env, goal.args[0]);
      const t2 = deref(env, goal.args[1]);
      if (t1.type === 'atom' && t1.name.length === 1) {
        // Forward: char → code
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[1], mkInt(t1.name.charCodeAt(0)))) k(e2);
      } else if (t1.type === 'var' && t2.type === 'int') {
        // Reverse: code → char
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[0], mkAtom(String.fromCharCode(t2.val)))) k(e2);
      }
      return;
    }
    if (f === 'number_codes' && a === 2) {
      const t  = deref(env, goal.args[0]);
      const t2 = deref(env, goal.args[1]);
      if (t.type === 'int') {
        // Forward: number → code list
        const codes = arrayToList(String(t.val).split('').map(c => mkInt(c.charCodeAt(0))));
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[1], codes)) k(e2);
      } else if (t.type === 'var') {
        // Reverse: code list → number
        const arr = listToArray(t2, env);
        if (arr) {
          let s = ''; let ok = true;
          for (const el of arr) {
            const d = deref(env, el);
            if (d.type !== 'int') { ok = false; break; }
            s += String.fromCharCode(d.val);
          }
          if (ok) {
            const n = parseInt(s, 10);
            if (!isNaN(n)) { const e2 = copyEnv(env); if (unify(e2, goal.args[0], mkInt(n))) k(e2); }
          }
        }
      }
      return;
    }
    if (f === 'number_chars' && a === 2) {
      const t  = deref(env, goal.args[0]);
      const t2 = deref(env, goal.args[1]);
      if (t.type === 'int') {
        // Forward: number → char list
        const chars = arrayToList(String(t.val).split('').map(c => mkAtom(c)));
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[1], chars)) k(e2);
      } else if (t.type === 'var') {
        // Reverse: char list → number
        const arr = listToArray(t2, env);
        if (arr) {
          let s = ''; let ok = true;
          for (const el of arr) {
            const d = deref(env, el);
            if (d.type !== 'atom') { ok = false; break; }
            s += d.name;
          }
          if (ok) {
            const n = parseInt(s, 10);
            if (!isNaN(n)) { const e2 = copyEnv(env); if (unify(e2, goal.args[0], mkInt(n))) k(e2); }
          }
        }
      }
      return;
    }
    if (f === 'atom_number' && a === 2) {
      const t  = deref(env, goal.args[0]);
      const t2 = deref(env, goal.args[1]);
      if (t.type === 'atom') {
        // Forward: atom → number
        const n = parseInt(t.name, 10);
        if (!isNaN(n)) { const e2 = copyEnv(env); if (unify(e2, goal.args[1], mkInt(n))) k(e2); }
      } else if (t.type === 'var' && t2.type === 'int') {
        // Reverse: number → atom
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[0], mkAtom(String(t2.val)))) k(e2);
      }
      return;
    }
    if (f === 'term_to_atom' && a === 2) {
      const t  = deref(env, goal.args[0]);
      const t2 = deref(env, goal.args[1]);
      if (t.type !== 'var') {
        // Forward: term → atom
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[1], mkAtom(termToString(env, t)))) k(e2);
      } else if (t2.type === 'atom') {
        // Reverse: parse atom text as a term
        try {
          const toks = tokenize(t2.name + '.');
          const parser = new Parser(toks);
          const cl = parser.parseClause();
          if (cl) { const e2 = copyEnv(env); if (unify(e2, goal.args[0], cl.head)) k(e2); }
        } catch (_) { /* parse failure → predicate fails */ }
      }
      return;
    }
    if (f === 'upcase_atom' && a === 2) {
      const t = deref(env, goal.args[0]);
      if (t.type === 'atom') {
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[1], mkAtom(t.name.toUpperCase()))) k(e2);
      }
      return;
    }
    if (f === 'downcase_atom' && a === 2) {
      const t = deref(env, goal.args[0]);
      if (t.type === 'atom') {
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[1], mkAtom(t.name.toLowerCase()))) k(e2);
      }
      return;
    }

    // ---- List operations ----
    if (f === 'length' && a === 2) {
      const lst = deref(env, goal.args[0]);
      const len = listLen(lst, env);
      if (len >= 0) {
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[1], mkInt(len))) k(e2);
      }
      return;
    }
    if (f === 'last' && a === 2) {
      const lst = listToArray(deref(env, goal.args[0]), env);
      if (lst && lst.length > 0) {
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[1], lst[lst.length - 1])) k(e2);
      }
      return;
    }
    if (f === 'nth0' && a === 3) {
      const idx = deref(env, goal.args[0]);
      const lst = listToArray(deref(env, goal.args[1]), env);
      if (lst && idx.type === 'int' && idx.val >= 0 && idx.val < lst.length) {
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[2], lst[idx.val])) k(e2);
      }
      return;
    }
    if (f === 'nth1' && a === 3) {
      const idx = deref(env, goal.args[0]);
      const lst = listToArray(deref(env, goal.args[1]), env);
      if (lst && idx.type === 'int' && idx.val >= 1 && idx.val <= lst.length) {
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[2], lst[idx.val - 1])) k(e2);
      }
      return;
    }
    if (f === 'sort' && a === 2) {
      const lst = listToArray(deref(env, goal.args[0]), env);
      if (lst) {
        const applied = lst.map(t => applyEnv(env, t));
        const sorted = applied.slice().sort(termCompare).filter((t, i, arr) =>
          i === 0 || termCompare(t, arr[i - 1]) !== 0);
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[1], arrayToList(sorted))) k(e2);
      }
      return;
    }
    if (f === 'msort' && a === 2) {
      const lst = listToArray(deref(env, goal.args[0]), env);
      if (lst) {
        const applied = lst.map(t => applyEnv(env, t));
        const sorted = applied.slice().sort(termCompare);
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[1], arrayToList(sorted))) k(e2);
      }
      return;
    }
    if (f === 'flatten' && a === 2) {
      const lst = listToArray(deref(env, goal.args[0]), env);
      if (lst) {
        const flat = [];
        function flatList(t) {
          if (t.type === 'nil') return;
          if (t.type === 'list') { flatList(deref(env, t.head)); flatList(deref(env, t.tail)); return; }
          flat.push(t);
        }
        flatList(deref(env, goal.args[0]));
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[1], arrayToList(flat))) k(e2);
      }
      return;
    }
    if (f === 'max_list' && a === 2) {
      const lst = listToArray(deref(env, goal.args[0]), env);
      if (lst && lst.length > 0) {
        const vals = lst.map(t => deref(env, t)).filter(t => t.type === 'int').map(t => t.val);
        if (vals.length === lst.length) {
          const e2 = copyEnv(env);
          if (unify(e2, goal.args[1], mkInt(Math.max(...vals)))) k(e2);
        }
      }
      return;
    }
    if (f === 'min_list' && a === 2) {
      const lst = listToArray(deref(env, goal.args[0]), env);
      if (lst && lst.length > 0) {
        const vals = lst.map(t => deref(env, t)).filter(t => t.type === 'int').map(t => t.val);
        if (vals.length === lst.length) {
          const e2 = copyEnv(env);
          if (unify(e2, goal.args[1], mkInt(Math.min(...vals)))) k(e2);
        }
      }
      return;
    }
    if (f === 'sum_list' && a === 2) {
      const lst = listToArray(deref(env, goal.args[0]), env);
      if (lst) {
        const vals = lst.map(t => deref(env, t)).filter(t => t.type === 'int');
        if (vals.length === lst.length) {
          const e2 = copyEnv(env);
          if (unify(e2, goal.args[1], mkInt(vals.reduce((s, t) => s + t.val, 0)))) k(e2);
        }
      }
      return;
    }
    if (f === 'numlist' && a === 3) {
      const lo = deref(env, goal.args[0]);
      const hi = deref(env, goal.args[1]);
      if (lo.type === 'int' && hi.type === 'int') {
        const arr = [];
        for (let j = lo.val; j <= hi.val; j++) arr.push(mkInt(j));
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[2], arrayToList(arr))) k(e2);
      }
      return;
    }
    if (f === 'list_to_set' && a === 2) {
      const lst = listToArray(deref(env, goal.args[0]), env);
      if (lst) {
        const seen = [];
        const set = lst.filter(t => {
          const tv = applyEnv(env, t);
          const dup = seen.some(s => termCompare(s, tv) === 0);
          if (!dup) seen.push(tv);
          return !dup;
        });
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[1], arrayToList(set))) k(e2);
      }
      return;
    }
    if (f === 'permutation' && a === 2) {
      const lst = listToArray(deref(env, goal.args[0]), env);
      if (lst) {
        function perms(arr) {
          if (arr.length === 0) return [[]];
          const res = [];
          for (let j = 0; j < arr.length; j++) {
            const rest = arr.filter((_, idx) => idx !== j);
            for (const p of perms(rest)) res.push([arr[j]].concat(p));
          }
          return res;
        }
        for (const p of perms(lst)) {
          const e2 = copyEnv(env);
          if (unify(e2, goal.args[1], arrayToList(p))) k(e2);
        }
      }
      return;
    }
    if (f === 'select' && a === 3) {
      const lst = listToArray(deref(env, goal.args[1]), env);
      if (lst) {
        for (let j = 0; j < lst.length; j++) {
          const rest = lst.filter((_, idx) => idx !== j);
          const e2 = copyEnv(env);
          if (unify(e2, goal.args[0], lst[j]) && unify(e2, goal.args[2], arrayToList(rest))) {
            k(e2);
          }
        }
      }
      return;
    }
    if (f === 'subtract' && a === 3) {
      const lst1 = listToArray(deref(env, goal.args[0]), env);
      const lst2 = listToArray(deref(env, goal.args[1]), env);
      if (lst1 && lst2) {
        const lst2a = lst2.map(t => applyEnv(env, t));
        const diff = lst1.filter(t => {
          const tv = applyEnv(env, t);
          return !lst2a.some(s => termCompare(s, tv) === 0);
        });
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[2], arrayToList(diff))) k(e2);
      }
      return;
    }
    if (f === 'intersection' && a === 3) {
      const lst1 = listToArray(deref(env, goal.args[0]), env);
      const lst2 = listToArray(deref(env, goal.args[1]), env);
      if (lst1 && lst2) {
        const lst2a = lst2.map(t => applyEnv(env, t));
        const inter = lst1.filter(t => {
          const tv = applyEnv(env, t);
          return lst2a.some(s => termCompare(s, tv) === 0);
        });
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[2], arrayToList(inter))) k(e2);
      }
      return;
    }
    if (f === 'union' && a === 3) {
      const lst1 = listToArray(deref(env, goal.args[0]), env);
      const lst2 = listToArray(deref(env, goal.args[1]), env);
      if (lst1 && lst2) {
        const lst1a = lst1.map(t => applyEnv(env, t));
        const add = lst2.filter(t => {
          const tv = applyEnv(env, t);
          return !lst1a.some(s => termCompare(s, tv) === 0);
        });
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[2], arrayToList(lst1.concat(add)))) k(e2);
      }
      return;
    }
    if (f === 'delete' && a === 3) {
      const lst = listToArray(deref(env, goal.args[0]), env);
      const elem = applyEnv(env, goal.args[1]);
      if (lst) {
        const filtered = lst.filter(t => termCompare(applyEnv(env, t), elem) !== 0);
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[2], arrayToList(filtered))) k(e2);
      }
      return;
    }

    // ---- Meta-predicates ----
    if (f === 'findall' && a === 3) {
      const template = goal.args[0];
      const goalArg  = goal.args[1];
      const listArg  = goal.args[2];
      const results  = [];
      try {
        solve(goalArg, env, db, depth + 1, function (solEnv) {
          results.push(applyEnv(solEnv, template));
        });
      } catch (e) { if (!e.cut) throw e; }
      const e2 = copyEnv(env);
      if (unify(e2, listArg, arrayToList(results))) k(e2);
      return;
    }
    if (f === 'aggregate_all' && a === 3) {
      // simplified: only count
      const agg = deref(env, goal.args[0]);
      const goalArg = goal.args[1];
      const resultArg = goal.args[2];
      if (agg.type === 'atom' && agg.name === 'count') {
        let cnt = 0;
        try { solve(goalArg, env, db, depth + 1, function() { cnt++; }); }
        catch(e) { if (!e.cut) throw e; }
        const e2 = copyEnv(env);
        if (unify(e2, resultArg, mkInt(cnt))) k(e2);
      }
      return;
    }
    if (f === 'bagof' && a === 3) {
      // simplified behaves like findall (no grouping)
      const template = goal.args[0];
      const goalArg  = goal.args[1];
      const listArg  = goal.args[2];
      const results  = [];
      try {
        solve(goalArg, env, db, depth + 1, function (solEnv) {
          results.push(applyEnv(solEnv, template));
        });
      } catch (e) { if (!e.cut) throw e; }
      if (results.length > 0) {
        const e2 = copyEnv(env);
        if (unify(e2, listArg, arrayToList(results))) k(e2);
      }
      return;
    }
    if (f === 'setof' && a === 3) {
      const template = goal.args[0];
      const goalArg  = goal.args[1];
      const listArg  = goal.args[2];
      const results  = [];
      try {
        solve(goalArg, env, db, depth + 1, function (solEnv) {
          results.push(applyEnv(solEnv, template));
        });
      } catch (e) { if (!e.cut) throw e; }
      if (results.length > 0) {
        const sorted = results.sort(termCompare).filter((t, i, arr) =>
          i === 0 || termCompare(t, arr[i-1]) !== 0);
        const e2 = copyEnv(env);
        if (unify(e2, listArg, arrayToList(sorted))) k(e2);
      }
      return;
    }
    if (f === 'forall' && a === 2) {
      // forall(Cond, Action) — true if for all Cond solutions, Action succeeds
      let ok = true;
      try {
        solve(goal.args[0], env, db, depth + 1, function (env2) {
          let actionOk = false;
          try { solve(goal.args[1], env2, db, depth + 1, function() { actionOk = true; }); }
          catch(e) { if (!e.cut) throw e; }
          if (!actionOk) ok = false;
        });
      } catch(e) { if (!e.cut) throw e; }
      if (ok) k(env);
      return;
    }
    if (f === 'once' && a === 1) {
      let done = false;
      try {
        solve(goal.args[0], env, db, depth + 1, function (env2) {
          if (!done) { done = true; k(env2); }
        });
      } catch (e) { if (!e.cut) throw e; }
      return;
    }
    if (f === 'ignore' && a === 1) {
      let done = false;
      try {
        solve(goal.args[0], env, db, depth + 1, function (env2) {
          if (!done) { done = true; k(env2); }
        });
      } catch (e) { if (!e.cut) throw e; }
      if (!done) k(env);
      return;
    }
    if (f === 'call' && a === 1) {
      solve(goal.args[0], env, db, depth + 1, k);
      return;
    }
    if (f === 'call' && a >= 2) {
      // call(Goal, Arg1, ..., ArgN) — add extra args to Goal
      const baseGoal = deref(env, goal.args[0]);
      const extraArgs = goal.args.slice(1);
      let callGoal;
      if (baseGoal.type === 'atom') {
        callGoal = mkCompound(baseGoal.name, extraArgs);
      } else if (baseGoal.type === 'compound') {
        callGoal = mkCompound(baseGoal.functor, baseGoal.args.concat(extraArgs));
      } else {
        return; // fail
      }
      solve(callGoal, env, db, depth + 1, k);
      return;
    }
    if (f === 'not' && a === 1) {
      // not/1 as negation-as-failure
      let found = false;
      try { solve(goal.args[0], env, db, depth + 1, function () { found = true; }); }
      catch (e) { if (!e.cut) throw e; }
      if (!found) k(env);
      return;
    }

    // ---- Functor / univ ----
    if (f === 'functor' && a === 3) {
      const t = deref(env, goal.args[0]);
      if (t.type !== 'var') {
        const e2 = copyEnv(env);
        const fname = t.type === 'atom' ? t.name : t.type === 'int' ? String(t.val) : t.type === 'nil' ? '[]' : t.functor;
        const farity = t.type === 'compound' ? t.arity : t.type === 'list' ? 2 : 0;
        if (unify(e2, goal.args[1], mkAtom(fname)) && unify(e2, goal.args[2], mkInt(farity))) k(e2);
      } else {
        // Build term from functor + arity
        const nameT  = deref(env, goal.args[1]);
        const arityT = deref(env, goal.args[2]);
        if ((nameT.type === 'atom' || nameT.type === 'int') && arityT.type === 'int') {
          const e2 = copyEnv(env);
          if (arityT.val === 0) {
            const term2 = nameT.type === 'int' ? nameT : mkAtom(nameT.name);
            if (unify(e2, goal.args[0], term2)) k(e2);
          } else {
            const newArgs = Array.from({length: arityT.val}, () => mkVar('_'));
            if (unify(e2, goal.args[0], mkCompound(nameT.name, newArgs))) k(e2);
          }
        }
      }
      return;
    }
    if (f === 'arg' && a === 3) {
      const n = deref(env, goal.args[0]);
      const t = deref(env, goal.args[1]);
      if (n.type === 'int' && t.type === 'compound' && n.val >= 1 && n.val <= t.arity) {
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[2], t.args[n.val - 1])) k(e2);
      }
      return;
    }
    if (f === '=..' && a === 2) {
      const t = deref(env, goal.args[0]);
      if (t.type !== 'var') {
        const lst = t.type === 'compound'
          ? arrayToList([mkAtom(t.functor)].concat(t.args))
          : t.type === 'atom' ? arrayToList([t])
          : t.type === 'int'  ? arrayToList([t])
          : t.type === 'nil'  ? arrayToList([mkAtom('[]')])
          : null;
        if (lst) {
          const e2 = copyEnv(env);
          if (unify(e2, goal.args[1], lst)) k(e2);
        }
      } else {
        // Build term from list
        const lst = listToArray(deref(env, goal.args[1]), env);
        if (lst && lst.length > 0) {
          const fn = deref(env, lst[0]);
          const e2 = copyEnv(env);
          let term2;
          if (lst.length === 1) term2 = fn.type === 'atom' ? fn : fn;
          else term2 = mkCompound(fn.name, lst.slice(1));
          if (unify(e2, goal.args[0], term2)) k(e2);
        }
      }
      return;
    }
    if (f === 'copy_term' && a === 2) {
      const t = applyEnv(env, goal.args[0]);
      const fresh = renameTerm(t, Object.create(null));
      const e2 = copyEnv(env);
      if (unify(e2, goal.args[1], fresh)) k(e2);
      return;
    }

    // ---- Numeric shortcuts ----
    if (f === 'succ' && a === 2) {
      const t = deref(env, goal.args[0]);
      const t2 = deref(env, goal.args[1]);
      if (t.type === 'int') {
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[1], mkInt(t.val + 1))) k(e2);
      } else if (t2.type === 'int' && t2.val > 0) {
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[0], mkInt(t2.val - 1))) k(e2);
      }
      return;
    }
    if (f === 'plus' && a === 3) {
      const t1 = deref(env, goal.args[0]);
      const t2 = deref(env, goal.args[1]);
      const t3 = deref(env, goal.args[2]);
      if (t1.type === 'int' && t2.type === 'int') {
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[2], mkInt(t1.val + t2.val))) k(e2);
      } else if (t1.type === 'int' && t3.type === 'int') {
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[1], mkInt(t3.val - t1.val))) k(e2);
      } else if (t2.type === 'int' && t3.type === 'int') {
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[0], mkInt(t3.val - t2.val))) k(e2);
      }
      return;
    }
    if (f === 'between' && a === 3) {
      const lo = deref(env, goal.args[0]);
      const hi = deref(env, goal.args[1]);
      if (lo.type === 'int' && hi.type === 'int') {
        for (let j = lo.val; j <= hi.val; j++) {
          const e2 = copyEnv(env);
          if (unify(e2, goal.args[2], mkInt(j))) k(e2);
        }
      }
      return;
    }
    if (f === 'succ_or_zero' && a === 2) {
      const t = deref(env, goal.args[0]);
      if (t.type === 'int') {
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[1], mkInt(Math.max(0, t.val - 1)))) k(e2);
      }
      return;
    }
    if (f === 'char_type' && a === 2) {
      // simplified: just succeed
      k(env);
      return;
    }

    // ---- assert / retract / abolish ----
    if (f === 'assertz' || f === 'asserta' || f === 'assert') {
      if (a !== 1) { k(env); return; }
      const ct = applyEnv(env, deref(env, goal.args[0]));
      let head, body;
      if (ct.type === 'compound' && ct.functor === ':-' && ct.arity === 2) {
        head = ct.args[0];
        body = ct.args[1];
      } else {
        head = ct;
        body = null;
      }
      const assertKey = predicateKey(head);
      if (_BUILTIN_KEYS.has(assertKey)) {
        throw new Error(f + '/1: cannot assert over built-in predicate ' + assertKey);
      }
      if (!db[assertKey]) db[assertKey] = [];
      if (f === 'asserta') {
        db[assertKey].unshift({ head: head, body: body });
      } else {
        db[assertKey].push({ head: head, body: body });
      }
      k(env);
      return;
    }

    if (f === 'retract' && a === 1) {
      const ct = deref(env, goal.args[0]);
      let headP, bodyP;
      if (ct.type === 'compound' && ct.functor === ':-' && ct.arity === 2) {
        headP = ct.args[0];
        bodyP = ct.args[1];
      } else {
        headP = ct;
        bodyP = null;
      }
      const headD = deref(env, headP);
      const retractKey = (headD.type === 'atom'     ? headD.name + '/0' :
                          headD.type === 'compound' ? headD.functor + '/' + headD.arity : null);
      if (!retractKey) return; // fail
      const retractClauses = db[retractKey];
      if (!retractClauses) return; // fail
      // Non-deterministic: try each clause; permanently remove it before yielding.
      let ri = 0;
      while (ri < retractClauses.length) {
        const fresh = renameClause(retractClauses[ri]);
        const e2 = copyEnv(env);
        let matches = unify(e2, headP, fresh.head);
        if (matches && bodyP !== null) {
          const freshBody = fresh.body || mkAtom('true');
          matches = unify(e2, bodyP, freshBody);
        }
        if (matches) {
          retractClauses.splice(ri, 1); // permanently remove (not undone on backtrack)
          try {
            k(e2);
          } catch (e) {
            if (e.cut) return;
            throw e;
          }
          // ri stays the same — the former ri+1 is now at ri
        } else {
          ri++;
        }
      }
      return;
    }

    if (f === 'abolish' && a === 1) {
      const ct = deref(env, goal.args[0]);
      // Standard: abolish(Name/Arity)
      if (ct.type === 'compound' && ct.functor === '/' && ct.arity === 2) {
        const nameT  = deref(env, ct.args[0]);
        const arityT = deref(env, ct.args[1]);
        if (nameT.type === 'atom' && arityT.type === 'int') {
          const abolishKey = nameT.name + '/' + arityT.val;
          if (_BUILTIN_KEYS.has(abolishKey)) {
            throw new Error('abolish/1: cannot abolish built-in predicate ' + abolishKey);
          }
          delete db[abolishKey];
        }
      }
      k(env);
      return;
    }

    // ---- consult/1 — parse a Prolog source atom and add its clauses to db ----
    if (f === 'consult' && a === 1) {
      const srcT = deref(env, goal.args[0]);
      if (srcT.type !== 'atom') {
        throw new Error('consult/1: argument must be an atom containing Prolog source text');
      }
      const consultClauses = parsePrologSource(srcT.name);
      for (let ci = 0; ci < consultClauses.length; ci++) {
        const cl = consultClauses[ci];
        const consultKey = predicateKey(cl.head);
        if (_BUILTIN_KEYS.has(consultKey)) {
          throw new Error('consult/1: cannot redefine built-in predicate ' + consultKey);
        }
        if (!db[consultKey]) db[consultKey] = [];
        db[consultKey].push(cl);
      }
      k(env);
      return;
    }

    // ---- Comparison (standard order) ----
    if (f === 'compare' && a === 3) {
      const t1 = applyEnv(env, goal.args[1]);
      const t2 = applyEnv(env, goal.args[2]);
      const c = termCompare(t1, t2);
      const sym = c < 0 ? '<' : c > 0 ? '>' : '=';
      const e2 = copyEnv(env);
      if (unify(e2, goal.args[0], mkAtom(sym))) k(e2);
      return;
    }
    if (f === '@<' && a === 2) {
      if (termCompare(applyEnv(env, goal.args[0]), applyEnv(env, goal.args[1])) < 0) k(env);
      return;
    }
    if (f === '@>' && a === 2) {
      if (termCompare(applyEnv(env, goal.args[0]), applyEnv(env, goal.args[1])) > 0) k(env);
      return;
    }
    if (f === '@=<' && a === 2) {
      if (termCompare(applyEnv(env, goal.args[0]), applyEnv(env, goal.args[1])) <= 0) k(env);
      return;
    }
    if (f === '@>=' && a === 2) {
      if (termCompare(applyEnv(env, goal.args[0]), applyEnv(env, goal.args[1])) >= 0) k(env);
      return;
    }

    // ---- String (treat as atom) ----
    if (f === 'string' && a === 1) {
      const t = deref(env, goal.args[0]);
      if (t.type === 'atom') k(env);
      return;
    }
    if (f === 'string_concat' && a === 3) {
      const t1 = deref(env, goal.args[0]);
      const t2 = deref(env, goal.args[1]);
      if (t1.type === 'atom' && t2.type === 'atom') {
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[2], mkAtom(t1.name + t2.name))) k(e2);
      }
      return;
    }
    if (f === 'string_to_atom' && a === 2) {
      // Both directions: string_to_atom(?String, ?Atom)
      // In this implementation strings and atoms are the same type.
      const t  = deref(env, goal.args[0]);
      const t2 = deref(env, goal.args[1]);
      if (t.type === 'atom' || t.type === 'int') {
        const s = t.type === 'atom' ? t.name : String(t.val);
        const e2 = copyEnv(env); if (unify(e2, goal.args[1], mkAtom(s))) k(e2);
      } else if (t.type === 'var' && (t2.type === 'atom' || t2.type === 'int')) {
        const s = t2.type === 'atom' ? t2.name : String(t2.val);
        const e2 = copyEnv(env); if (unify(e2, goal.args[0], mkAtom(s))) k(e2);
      }
      return;
    }
    if (f === 'string_length' && a === 2) {
      const t = deref(env, goal.args[0]);
      if (t.type === 'atom') {
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[1], mkInt(t.name.length))) k(e2);
      }
      return;
    }

    // ---- New type converters ----
    if (f === 'atom_string' && a === 2) {
      // atom_string(?Atom, ?String) — bidirectional; numbers convert too
      const t  = deref(env, goal.args[0]);
      const t2 = deref(env, goal.args[1]);
      if (t.type === 'atom' || t.type === 'int') {
        const s = t.type === 'atom' ? t.name : String(t.val);
        const e2 = copyEnv(env); if (unify(e2, goal.args[1], mkAtom(s))) k(e2);
      } else if (t.type === 'var' && (t2.type === 'atom' || t2.type === 'int')) {
        const s = t2.type === 'atom' ? t2.name : String(t2.val);
        const e2 = copyEnv(env); if (unify(e2, goal.args[0], mkAtom(s))) k(e2);
      }
      return;
    }
    if (f === 'number_string' && a === 2) {
      // number_string(?Number, ?String) — bidirectional
      const t  = deref(env, goal.args[0]);
      const t2 = deref(env, goal.args[1]);
      if (t.type === 'int') {
        const e2 = copyEnv(env); if (unify(e2, goal.args[1], mkAtom(String(t.val)))) k(e2);
      } else if (t.type === 'var' && t2.type === 'atom') {
        const n = parseInt(t2.name, 10);
        if (!isNaN(n)) { const e2 = copyEnv(env); if (unify(e2, goal.args[0], mkInt(n))) k(e2); }
      }
      return;
    }
    if (f === 'term_string' && a === 2) {
      // term_string(?Term, ?String) — like term_to_atom but for strings
      const t  = deref(env, goal.args[0]);
      const t2 = deref(env, goal.args[1]);
      if (t.type !== 'var') {
        const e2 = copyEnv(env); if (unify(e2, goal.args[1], mkAtom(termToString(env, t)))) k(e2);
      } else if (t2.type === 'atom') {
        try {
          const toks = tokenize(t2.name + '.');
          const parser = new Parser(toks);
          const cl = parser.parseClause();
          if (cl) { const e2 = copyEnv(env); if (unify(e2, goal.args[0], cl.head)) k(e2); }
        } catch (_) { /* parse failure → predicate fails */ }
      }
      return;
    }
    if (f === 'string_codes' && a === 2) {
      // string_codes(?String, ?Codes) — bidirectional
      const t  = deref(env, goal.args[0]);
      const t2 = deref(env, goal.args[1]);
      if (t.type === 'atom') {
        const codes = arrayToList(t.name.split('').map(c => mkInt(c.charCodeAt(0))));
        const e2 = copyEnv(env); if (unify(e2, goal.args[1], codes)) k(e2);
      } else if (t.type === 'var') {
        const arr = listToArray(t2, env);
        if (arr) {
          let s = ''; let ok = true;
          for (const el of arr) {
            const d = deref(env, el);
            if (d.type !== 'int') { ok = false; break; }
            s += String.fromCharCode(d.val);
          }
          if (ok) { const e2 = copyEnv(env); if (unify(e2, goal.args[0], mkAtom(s))) k(e2); }
        }
      }
      return;
    }
    if (f === 'string_chars' && a === 2) {
      // string_chars(?String, ?Chars) — bidirectional
      const t  = deref(env, goal.args[0]);
      const t2 = deref(env, goal.args[1]);
      if (t.type === 'atom') {
        const chars = arrayToList(t.name.split('').map(c => mkAtom(c)));
        const e2 = copyEnv(env); if (unify(e2, goal.args[1], chars)) k(e2);
      } else if (t.type === 'var') {
        const arr = listToArray(t2, env);
        if (arr) {
          let s = ''; let ok = true;
          for (const el of arr) {
            const d = deref(env, el);
            if (d.type !== 'atom') { ok = false; break; }
            s += d.name;
          }
          if (ok) { const e2 = copyEnv(env); if (unify(e2, goal.args[0], mkAtom(s))) k(e2); }
        }
      }
      return;
    }
    if (f === 'atomic_list_concat' && a === 2) {
      // atomic_list_concat(+List, ?Atom) — concat list of atomics
      const lst = listToArray(deref(env, goal.args[0]), env);
      if (lst) {
        let s = ''; let ok = true;
        for (const el of lst) {
          const d = deref(env, el);
          if (d.type === 'atom')     s += d.name;
          else if (d.type === 'int') s += String(d.val);
          else { ok = false; break; }
        }
        if (ok) { const e2 = copyEnv(env); if (unify(e2, goal.args[1], mkAtom(s))) k(e2); }
      }
      return;
    }
    if (f === 'atomic_list_concat' && a === 3) {
      // atomic_list_concat(+List, +Sep, ?Atom) — join with separator
      // Also reverse: atomic_list_concat(-List, +Sep, +Atom) — split by separator
      const sepTerm  = deref(env, goal.args[1]);
      const atomTerm = deref(env, goal.args[2]);
      const lstTerm  = deref(env, goal.args[0]);
      if (lstTerm.type !== 'var') {
        // Forward: join
        const lst = listToArray(lstTerm, env);
        if (lst && (sepTerm.type === 'atom' || sepTerm.type === 'int')) {
          const sep = sepTerm.type === 'atom' ? sepTerm.name : String(sepTerm.val);
          let ok = true;
          const parts = [];
          for (const el of lst) {
            const d = deref(env, el);
            if (d.type === 'atom')     parts.push(d.name);
            else if (d.type === 'int') parts.push(String(d.val));
            else { ok = false; break; }
          }
          if (ok) { const e2 = copyEnv(env); if (unify(e2, goal.args[2], mkAtom(parts.join(sep)))) k(e2); }
        }
      } else if (atomTerm.type === 'atom' && (sepTerm.type === 'atom' || sepTerm.type === 'int')) {
        // Reverse: split
        const sep = sepTerm.type === 'atom' ? sepTerm.name : String(sepTerm.val);
        const parts = sep === '' ? atomTerm.name.split('') : atomTerm.name.split(sep);
        const lst = arrayToList(parts.map(p => mkAtom(p)));
        const e2 = copyEnv(env); if (unify(e2, goal.args[0], lst)) k(e2);
      }
      return;
    }
    if (f === 'writeq' && a === 1) {
      _output += termToString(env, goal.args[0]);
      k(env);
      return;
    }

    // ---- Form / CGI predicates ----
    // read_string(?Value) or read_string(+Prompt, ?Value)
    // On first call (no matching form arg): binds Value to '' and records a
    // text input in _formInputs so the HTML generator can render a form.
    // On subsequent calls (form arg present): binds Value to the submitted string.
    if (f === 'read_string' && (a === 1 || a === 2)) {
      const hasPrompt = (a === 2);
      const promptTerm = hasPrompt ? deref(env, goal.args[0]) : null;
      const valueArg   = hasPrompt ? goal.args[1] : goal.args[0];
      const prompt     = promptTerm
        ? (promptTerm.type === 'atom' ? promptTerm.name : termToString(env, promptTerm))
        : '';
      // Field names follow the pattern 'rs_N' (read_string field index N).
      const fieldName = 'rs_' + _readStringCounter++;
      const e2 = copyEnv(env);
      if (_formArgs[fieldName] !== undefined) {
        if (unify(e2, valueArg, mkAtom(String(_formArgs[fieldName])))) k(e2);
      } else {
        _formInputs.push({ type: 'text', name: fieldName, prompt: prompt });
        if (unify(e2, valueArg, mkAtom(''))) k(e2);
      }
      return;
    }
    // form_argument(+Name, ?Value)
    // Reads a named form argument (URL query param). Fails if not present.
    if (f === 'form_argument' && a === 2) {
      const nameTerm = deref(env, goal.args[0]);
      if (nameTerm.type !== 'atom') return;
      const argVal = _formArgs[nameTerm.name];
      if (argVal !== undefined) {
        const e2 = copyEnv(env);
        if (unify(e2, goal.args[1], mkAtom(String(argVal)))) k(e2);
      }
      return;
    }
    // hidden_field(+Name, +Value)
    // Records a hidden form field that will be included in the generated form.
    if (f === 'hidden_field' && a === 2) {
      const nameTerm  = deref(env, goal.args[0]);
      const valueTerm = deref(env, goal.args[1]);
      _formInputs.push({
        type:  'hidden',
        name:  termToString(env, nameTerm),
        value: termToString(env, valueTerm)
      });
      k(env);
      return;
    }

    // ---- Misc ----
    if (f === 'nb_getval' && a === 2) { return; } // not supported
    if (f === 'nb_setval' && a === 2) { k(env); return; } // no-op
    if (f === 'b_setval' && a === 2)  { k(env); return; }
    if (f === 'b_getval' && a === 2)  { return; }
    if (f === 'read_term' && a === 2) { return; }
    if (f === 'with_output_to' && a === 2) {
      // simplified: run goal, capture into string, unify with first arg
      const dest = deref(env, goal.args[0]);
      if (dest.type === 'compound' && dest.functor === 'string' && dest.arity === 1) {
        const savedOutput = _output;
        _output = '';
        try { solve(goal.args[1], env, db, depth + 1, k); }
        finally {
          const captured = _output;
          _output = savedOutput + captured;
        }
      } else {
        solve(goal.args[1], env, db, depth + 1, k);
      }
      return;
    }
    if (f === 'predsort' && a === 3) { return; }
    if (f === 'maplist' && a >= 2) {
      // maplist(Goal, List) or maplist(Goal, List, List2)
      if (a === 2) {
        const lst = listToArray(deref(env, goal.args[1]), env);
        if (!lst) return;
        function maplistSolve(idx, envCur) {
          if (idx === lst.length) { k(envCur); return; }
          solve(mkCompound('call', [goal.args[0], lst[idx]]), envCur, db, depth + 1, function(e2) {
            maplistSolve(idx + 1, e2);
          });
        }
        maplistSolve(0, env);
      } else if (a === 3) {
        const lst = listToArray(deref(env, goal.args[1]), env);
        if (!lst) return;
        const outVars = lst.map(() => mkVar('_M'));
        function maplist2Solve(idx, envCur) {
          if (idx === lst.length) {
            const e2 = copyEnv(envCur);
            if (unify(e2, goal.args[2], arrayToList(outVars.map(v => applyEnv(envCur, v))))) k(e2);
            return;
          }
          solve(mkCompound('call', [goal.args[0], lst[idx], outVars[idx]]), envCur, db, depth + 1, function(e2) {
            maplist2Solve(idx + 1, e2);
          });
        }
        maplist2Solve(0, env);
      } else if (a === 4) {
        const raw1 = listToArray(deref(env, goal.args[1]), env);
        const raw2 = listToArray(deref(env, goal.args[2]), env);
        const raw3 = listToArray(deref(env, goal.args[3]), env);
        const mLen = raw1 ? raw1.length : (raw2 ? raw2.length : (raw3 ? raw3.length : -1));
        if (mLen < 0) return;
        if ((raw1 && raw1.length !== mLen) || (raw2 && raw2.length !== mLen) || (raw3 && raw3.length !== mLen)) return;
        const vars1_4 = raw1 ? null : Array.from({length: mLen}, () => mkVar('_M'));
        const vars2_4 = raw2 ? null : Array.from({length: mLen}, () => mkVar('_M'));
        const vars3_4 = raw3 ? null : Array.from({length: mLen}, () => mkVar('_M'));
        function maplist3Solve(idx, envCur) {
          if (idx === mLen) {
            const e2 = copyEnv(envCur);
            if ((!vars1_4 || unify(e2, goal.args[1], arrayToList(vars1_4.map(v => applyEnv(envCur, v))))) &&
                (!vars2_4 || unify(e2, goal.args[2], arrayToList(vars2_4.map(v => applyEnv(envCur, v))))) &&
                (!vars3_4 || unify(e2, goal.args[3], arrayToList(vars3_4.map(v => applyEnv(envCur, v)))))) k(e2);
            return;
          }
          const el1 = raw1 ? raw1[idx] : vars1_4[idx];
          const el2 = raw2 ? raw2[idx] : vars2_4[idx];
          const el3 = raw3 ? raw3[idx] : vars3_4[idx];
          solve(mkCompound('call', [goal.args[0], el1, el2, el3]), envCur, db, depth + 1, function(e2) {
            maplist3Solve(idx + 1, e2);
          });
        }
        maplist3Solve(0, env);
      } else if (a === 5) {
        const raw1_5 = listToArray(deref(env, goal.args[1]), env);
        const raw2_5 = listToArray(deref(env, goal.args[2]), env);
        const raw3_5 = listToArray(deref(env, goal.args[3]), env);
        const raw4_5 = listToArray(deref(env, goal.args[4]), env);
        const mLen5 = raw1_5 ? raw1_5.length : (raw2_5 ? raw2_5.length : (raw3_5 ? raw3_5.length : (raw4_5 ? raw4_5.length : -1)));
        if (mLen5 < 0) return;
        if ((raw1_5 && raw1_5.length !== mLen5) || (raw2_5 && raw2_5.length !== mLen5) ||
            (raw3_5 && raw3_5.length !== mLen5) || (raw4_5 && raw4_5.length !== mLen5)) return;
        const vars1_5 = raw1_5 ? null : Array.from({length: mLen5}, () => mkVar('_M'));
        const vars2_5 = raw2_5 ? null : Array.from({length: mLen5}, () => mkVar('_M'));
        const vars3_5 = raw3_5 ? null : Array.from({length: mLen5}, () => mkVar('_M'));
        const vars4_5 = raw4_5 ? null : Array.from({length: mLen5}, () => mkVar('_M'));
        function maplist4Solve(idx, envCur) {
          if (idx === mLen5) {
            const e2 = copyEnv(envCur);
            if ((!vars1_5 || unify(e2, goal.args[1], arrayToList(vars1_5.map(v => applyEnv(envCur, v))))) &&
                (!vars2_5 || unify(e2, goal.args[2], arrayToList(vars2_5.map(v => applyEnv(envCur, v))))) &&
                (!vars3_5 || unify(e2, goal.args[3], arrayToList(vars3_5.map(v => applyEnv(envCur, v))))) &&
                (!vars4_5 || unify(e2, goal.args[4], arrayToList(vars4_5.map(v => applyEnv(envCur, v)))))) k(e2);
            return;
          }
          const el1 = raw1_5 ? raw1_5[idx] : vars1_5[idx];
          const el2 = raw2_5 ? raw2_5[idx] : vars2_5[idx];
          const el3 = raw3_5 ? raw3_5[idx] : vars3_5[idx];
          const el4 = raw4_5 ? raw4_5[idx] : vars4_5[idx];
          solve(mkCompound('call', [goal.args[0], el1, el2, el3, el4]), envCur, db, depth + 1, function(e2) {
            maplist4Solve(idx + 1, e2);
          });
        }
        maplist4Solve(0, env);
      }
      return;
    }
    if (f === 'include' && a === 3) {
      const lst = listToArray(deref(env, goal.args[1]), env);
      if (!lst) return;
      const kept = [];
      function includeSolve(idx, envCur) {
        if (idx === lst.length) {
          const e2 = copyEnv(envCur);
          if (unify(e2, goal.args[2], arrayToList(kept))) k(e2);
          return;
        }
        let found = false;
        try {
          solve(mkCompound('call', [goal.args[0], lst[idx]]), envCur, db, depth + 1, function(e2) {
            if (!found) { found = true; kept.push(lst[idx]); includeSolve(idx + 1, e2); }
          });
        } catch(e) { if (!e.cut) throw e; }
        if (!found) includeSolve(idx + 1, envCur);
      }
      includeSolve(0, env);
      return;
    }
    if (f === 'exclude' && a === 3) {
      const lst = listToArray(deref(env, goal.args[1]), env);
      if (!lst) return;
      const kept = [];
      function excludeSolve(idx, envCur) {
        if (idx === lst.length) {
          const e2 = copyEnv(envCur);
          if (unify(e2, goal.args[2], arrayToList(kept))) k(e2);
          return;
        }
        let found = false;
        try {
          solve(mkCompound('call', [goal.args[0], lst[idx]]), envCur, db, depth + 1, function() { found = true; });
        } catch(e) { if (!e.cut) throw e; }
        if (!found) kept.push(lst[idx]);
        excludeSolve(idx + 1, envCur);
      }
      excludeSolve(0, env);
      return;
    }
    if (f === 'convlist' && a === 3) {
      const lst = listToArray(deref(env, goal.args[1]), env);
      if (!lst) return;
      const acc = [];
      function convlistSolve(idx, envCur) {
        if (idx === lst.length) {
          const e2 = copyEnv(envCur);
          if (unify(e2, goal.args[2], arrayToList(acc))) k(e2);
          return;
        }
        const outVar = mkVar('_C');
        let found = false;
        try {
          solve(mkCompound('call', [goal.args[0], lst[idx], outVar]), envCur, db, depth + 1, function(e2) {
            if (!found) {
              found = true;
              acc.push(applyEnv(e2, outVar));
              convlistSolve(idx + 1, e2);
            }
          });
        } catch(e) { if (!e.cut) throw e; }
        if (!found) convlistSolve(idx + 1, envCur);
      }
      convlistSolve(0, env);
      return;
    }
    if (f === 'foldl' && a >= 4) {
      // foldl(Goal, List, V0, V) or foldl(Goal, L1, L2, V0, V) etc.
      if (a === 4) {
        const lst = listToArray(deref(env, goal.args[1]), env);
        if (!lst) return;
        function foldlSolve(idx, envCur, vi) {
          if (idx === lst.length) {
            const e2 = copyEnv(envCur);
            if (unify(e2, goal.args[3], vi)) k(e2);
            return;
          }
          const nextVar = mkVar('_F');
          solve(mkCompound('call', [goal.args[0], lst[idx], vi, nextVar]), envCur, db, depth + 1, function(e2) {
            foldlSolve(idx + 1, e2, applyEnv(e2, nextVar));
          });
        }
        foldlSolve(0, env, applyEnv(env, goal.args[2]));
      } else if (a === 5) {
        const lst1 = listToArray(deref(env, goal.args[1]), env);
        const lst2 = listToArray(deref(env, goal.args[2]), env);
        if (!lst1 || !lst2 || lst1.length !== lst2.length) return;
        function foldl2Solve(idx, envCur, vi) {
          if (idx === lst1.length) {
            const e2 = copyEnv(envCur);
            if (unify(e2, goal.args[4], vi)) k(e2);
            return;
          }
          const nextVar = mkVar('_F');
          solve(mkCompound('call', [goal.args[0], lst1[idx], lst2[idx], vi, nextVar]), envCur, db, depth + 1, function(e2) {
            foldl2Solve(idx + 1, e2, applyEnv(e2, nextVar));
          });
        }
        foldl2Solve(0, env, applyEnv(env, goal.args[3]));
      } else if (a === 6) {
        const lst1 = listToArray(deref(env, goal.args[1]), env);
        const lst2 = listToArray(deref(env, goal.args[2]), env);
        const lst3 = listToArray(deref(env, goal.args[3]), env);
        if (!lst1 || !lst2 || !lst3 || lst1.length !== lst2.length || lst1.length !== lst3.length) return;
        function foldl3Solve(idx, envCur, vi) {
          if (idx === lst1.length) {
            const e2 = copyEnv(envCur);
            if (unify(e2, goal.args[5], vi)) k(e2);
            return;
          }
          const nextVar = mkVar('_F');
          solve(mkCompound('call', [goal.args[0], lst1[idx], lst2[idx], lst3[idx], vi, nextVar]), envCur, db, depth + 1, function(e2) {
            foldl3Solve(idx + 1, e2, applyEnv(e2, nextVar));
          });
        }
        foldl3Solve(0, env, applyEnv(env, goal.args[4]));
      } else if (a === 7) {
        const lst1 = listToArray(deref(env, goal.args[1]), env);
        const lst2 = listToArray(deref(env, goal.args[2]), env);
        const lst3 = listToArray(deref(env, goal.args[3]), env);
        const lst4 = listToArray(deref(env, goal.args[4]), env);
        if (!lst1 || !lst2 || !lst3 || !lst4 ||
            lst1.length !== lst2.length || lst1.length !== lst3.length || lst1.length !== lst4.length) return;
        function foldl4Solve(idx, envCur, vi) {
          if (idx === lst1.length) {
            const e2 = copyEnv(envCur);
            if (unify(e2, goal.args[6], vi)) k(e2);
            return;
          }
          const nextVar = mkVar('_F');
          solve(mkCompound('call', [goal.args[0], lst1[idx], lst2[idx], lst3[idx], lst4[idx], vi, nextVar]), envCur, db, depth + 1, function(e2) {
            foldl4Solve(idx + 1, e2, applyEnv(e2, nextVar));
          });
        }
        foldl4Solve(0, env, applyEnv(env, goal.args[5]));
      }
      return;
    }

    // ---- Fallthrough: user-defined predicate ----
    solveUserPred(f, a, goal.args, env, db, depth, k);
  }

  // Iterate clauses of a user-defined predicate.
  function solveUserPred(name, arity, args, env, db, depth, k) {
    const key = name + '/' + arity;
    const clauses = db[key];
    if (!clauses || clauses.length === 0) {
      // Unknown predicate — fail silently
      return;
    }
    for (const clause of clauses) {
      const fresh = renameClause(clause);
      const e2 = copyEnv(env);
      // Unify call args with head args
      const headArgs = fresh.head.type === 'atom' ? [] : fresh.head.args;
      let ok = true;
      for (let i = 0; i < arity; i++) {
        if (!unify(e2, args[i], headArgs[i])) { ok = false; break; }
      }
      if (!ok) continue;
      // Execute body
      try {
        if (!fresh.body) {
          k(e2); // fact
        } else {
          solve(fresh.body, e2, db, depth + 1, k);
        }
      } catch (e) {
        if (e.cut) return; // cut stops this predicate's clause loop
        throw e;
      }
    }
  }

  // =========================================================================
  // SECTION 10: Helper utilities
  // =========================================================================

  function isList(t, env) {
    let cur = t;
    for (let i = 0; i < 10000; i++) {
      cur = deref(env, cur);
      if (cur.type === 'nil')  return true;
      if (cur.type === 'list') { cur = cur.tail; continue; }
      return false;
    }
    return false;
  }

  function listLen(t, env) {
    let n = 0;
    for (let i = 0; i < 100000; i++) {
      t = deref(env, t);
      if (t.type === 'nil')  return n;
      if (t.type !== 'list') return -1;
      n++; t = t.tail;
    }
    return -1;
  }

  function listToArray(t, env) {
    const arr = [];
    for (let i = 0; i < 100000; i++) {
      t = env ? deref(env, t) : t;
      if (t.type === 'nil')  return arr;
      if (t.type !== 'list') return null; // not a proper list
      arr.push(env ? deref(env, t.head) : t.head);
      t = t.tail;
    }
    return null;
  }

  function isGround(t) {
    if (t.type === 'var') return false;
    if (t.type === 'compound') return t.args.every(isGround);
    if (t.type === 'list')     return isGround(t.head) && isGround(t.tail);
    return true;
  }

  function termsEqual(t1, t2) {
    if (t1 === t2) return true;
    if (t1.type !== t2.type) {
      if (t1.type === 'nil' && t2.type === 'atom' && t2.name === '[]') return true;
      if (t2.type === 'nil' && t1.type === 'atom' && t1.name === '[]') return true;
      return false;
    }
    switch (t1.type) {
      case 'var':  return t1.id === t2.id;
      case 'atom': return t1.name === t2.name;
      case 'int':  return t1.val  === t2.val;
      case 'nil':  return true;
      case 'compound':
        if (t1.functor !== t2.functor || t1.arity !== t2.arity) return false;
        for (let i = 0; i < t1.arity; i++) if (!termsEqual(t1.args[i], t2.args[i])) return false;
        return true;
      case 'list': return termsEqual(t1.head, t2.head) && termsEqual(t1.tail, t2.tail);
      default: return false;
    }
  }

  function termCompare(t1, t2) {
    const order = { var: 0, int: 1, atom: 2, nil: 2, compound: 3, list: 3 };
    const o1 = order[t1.type] !== undefined ? order[t1.type] : 99;
    const o2 = order[t2.type] !== undefined ? order[t2.type] : 99;
    if (o1 !== o2) return o1 - o2;
    switch (t1.type) {
      case 'var':  return t1.id - t2.id;
      case 'int':  return t1.val - t2.val;
      case 'atom': return t1.name < t2.name ? -1 : t1.name > t2.name ? 1 : 0;
      case 'nil':  return 0;
      case 'compound': {
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
      case 'list': {
        const hc = termCompare(t1.head, t2.head);
        return hc !== 0 ? hc : termCompare(t1.tail, t2.tail);
      }
      default: return 0;
    }
  }

  // Collect variable names (display names) from a parsed term.
  function collectVarNames(term) {
    const names = new Set();
    _collectVarNames(term, names);
    return [...names];
  }
  function _collectVarNames(term, names) {
    if (!term) return;
    switch (term.type) {
      case 'var': if (term.name && !term.name.startsWith('_')) names.add(term.name); break;
      case 'compound': term.args.forEach(a => _collectVarNames(a, names)); break;
      case 'list': _collectVarNames(term.head, names); _collectVarNames(term.tail, names); break;
    }
  }

  // =========================================================================
  // SECTION 11: Public query API
  // =========================================================================

  /**
   * runQuery(programSource, queryString, maxAnswers, formArgs)
   *
   * Parse `programSource` as a set of Prolog clauses, then execute `queryString`
   * as a query.  Returns:
   *   {
   *     ok:      boolean,          // true if at least one answer found (or no error)
   *     answers: [{varName: val}], // variable bindings for each answer
   *     output:  string,           // text written by write/nl/writeln
   *     error:   string|null       // error message if something went wrong
   *   }
   *
   * The Prolog prelude (_PRELUDE_SOURCE) is always merged into the database
   * before user clauses, making its predicates available in every query.
   * Attempting to define a clause whose name/arity appears in _BUILTIN_KEYS
   * (JS-native predicates) causes an immediate error.
   */
  function runQuery(programSource, queryString, maxAnswers, formArgs) {
    maxAnswers = maxAnswers || 10;
    _output     = '';
    _formArgs   = (formArgs && typeof formArgs === 'object') ? formArgs : {};
    _formInputs = [];
    _readStringCounter = 0;

    let db;
    try {
      // 1. Parse user source — reject any redefinition of JS built-ins.
      const userClauses = parsePrologSource(programSource);
      for (const cl of userClauses) {
        const key = predicateKey(cl.head);
        if (_BUILTIN_KEYS.has(key)) {
          return { ok: false, answers: [], output: '',
                   error: 'Permission error: cannot redefine built-in predicate ' + key };
        }
      }

      // 2. Parse the prelude (silent, system predicates).
      const preludeClauses = parsePrologSource(_PRELUDE_SOURCE);

      // 3. Collect the set of predicate keys defined by user code.
      const userKeys = new Set(userClauses.map(cl => predicateKey(cl.head)));

      // 4. Merge into one database: prelude clauses are loaded first as system
      //    predicates, but any predicate key that the user also defines is
      //    completely replaced by the user's clauses (user code wins).
      db = buildDatabase([], { rejectBuiltins: false });
      for (const cl of preludeClauses) {
        const key = predicateKey(cl.head);
        if (userKeys.has(key)) continue; // user overrides this prelude predicate
        if (!db[key]) db[key] = [];
        db[key].push(Object.assign({}, cl, { system: true }));
      }
      for (const cl of userClauses) {
        const key = predicateKey(cl.head);
        if (!db[key]) db[key] = [];
        db[key].push(cl);
      }
    } catch (e) {
      return { ok: false, answers: [], output: '', error: 'Parse error in program: ' + e.message };
    }

    // Parse query (add trailing '.' if missing)
    let queryTerm;
    try {
      const qs = queryString.trim();
      const withDot = qs.endsWith('.') ? qs : qs + '.';
      const toks = tokenize(withDot);
      const parser = new Parser(toks);
      const cl = parser.parseClause();
      if (!cl) return { ok: false, answers: [], output: '', error: 'Empty query' };
      queryTerm = cl.head;
    } catch (e) {
      return { ok: false, answers: [], output: '', error: 'Parse error in query: ' + e.message };
    }

    // Collect variable names from the query for result display
    const varNames = collectVarNames(queryTerm);

    const answers = [];
    let errorMsg = null;

    try {
      // Rename query vars to get fresh ids (the parsed vars already have unique ids
      // from mkVar, but we want a mapping from display name -> id)
      const varMap = Object.create(null); // display name -> Var term (from queryTerm)
      _buildVarMap(queryTerm, varMap);

      const env = Object.create(null);
      solve(queryTerm, env, db, 0, function (solEnv) {
        if (answers.length >= maxAnswers) throw { stop: true };
        const bindings = Object.create(null);
        for (const name of varNames) {
          if (varMap[name]) {
            bindings[name] = termToString(solEnv, varMap[name]);
          }
        }
        answers.push(bindings);
      });
    } catch (e) {
      if (e.stop) { /* normal stop */ }
      else if (e.cut) { /* cut at top level — ok */ }
      else errorMsg = e.message || String(e);
    }

    return {
      ok:         answers.length > 0 || (errorMsg === null && varNames.length === 0),
      answers:    answers,
      output:     _output,
      formInputs: _formInputs.slice(),
      error:      errorMsg
    };
  }

  // Walk the query term and collect a display-name -> Var mapping
  // (uses the actual Var objects so we can look them up in the solution env).
  function _buildVarMap(term, map) {
    if (!term) return;
    switch (term.type) {
      case 'var':
        if (term.name && !term.name.startsWith('_') && !map[term.name]) map[term.name] = term;
        break;
      case 'compound':
        term.args.forEach(a => _buildVarMap(a, map));
        break;
      case 'list':
        _buildVarMap(term.head, map);
        _buildVarMap(term.tail, map);
        break;
    }
  }

  // =========================================================================
  // SECTION 12: Standalone HTML generator
  // =========================================================================

  /**
   * generateHtml(runtimeSource, programSource)
   *
   * Produces a fully self-contained HTML page that embeds the pl2js runtime
   * inline and auto-runs `main/0` from the supplied Prolog program when the
   * page is opened in a browser.
   *
   * - `runtimeSource` : the raw text of pl2js.js (fetched by the caller).
   * - `programSource` : the Prolog program text to embed.
   *
   * The generated page:
   *   1. Shows a reminder banner if `main/0` is not defined in the program.
   *   2. Displays the output produced by `write`/`nl`/`writeln` etc.
   *   3. Wraps all execution in error handling and displays errors clearly.
   *   4. Does not include execution traces.
   *   5. Supports interactive forms via read_string/1-2, hidden_field/2, and
   *      form_argument/2.  URL query parameters are passed to the Prolog
   *      program as form arguments so the page can act as a simple CGI-style
   *      application without a server.
   */
  // Returns true when the Prolog source defines at least one main/0 clause
  // (either a fact `main.` or a rule `main :- ...`).
  // The negative lookahead (?!\w) prevents false positives on predicates like
  // `mainLoop` or `main2`.
  function hasMainPredicate(source) {
    return /(?:^|[\r\n])\s*main(?!\w)\s*(?::-|\.)/.test(source);
  }

  function generateHtml(runtimeSource, programSource) {
    // Detect whether a main/0 clause exists (fact or rule).
    var hasMain = hasMainPredicate(programSource);

    // Safely embed the program source as a JS string literal.
    var escapedProg = JSON.stringify(programSource);

    // Escape any literal </script> sequences inside the runtime source so the
    // HTML parser does not close the <script> block prematurely.
    // <\/script> is equivalent in JavaScript but invisible to the HTML tokeniser.
    var safeRuntime = runtimeSource.replace(/<\/script/gi, '<\\/script');

    return '<!DOCTYPE html>\n' +
'<html lang="en">\n' +
'<head>\n' +
'  <meta charset="UTF-8">\n' +
'  <meta name="viewport" content="width=device-width, initial-scale=1.0">\n' +
'  <title>Prolog Program</title>\n' +
'  <style>\n' +
'    *, *::before, *::after { box-sizing: border-box; margin: 0; padding: 0; }\n' +
'    body { font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;\n' +
'           background: #f0f2f5; color: #1a1a2e; padding: 24px 16px 40px; }\n' +
'    .page { max-width: 700px; margin: 0 auto; }\n' +
'    h1 { font-size: 1.4rem; font-weight: 700; margin-bottom: 16px; }\n' +
'    h1 span { color: #5271ff; }\n' +
'    .notice { background: #fef3c7; border-left: 4px solid #f59e0b;\n' +
'              border-radius: 0 8px 8px 0; padding: 10px 14px;\n' +
'              margin-bottom: 16px; font-size: 0.88rem; line-height: 1.5; }\n' +
'    .notice code { background: #fde68a; border-radius: 3px;\n' +
'                   padding: 1px 4px; font-family: monospace; font-size: 0.83rem; }\n' +
'    .label { font-size: 0.76rem; font-weight: 600; text-transform: uppercase;\n' +
'             letter-spacing: 0.6px; color: #888; margin-bottom: 8px; }\n' +
'    #output { background: #111827; color: #d1fae5; border-radius: 8px;\n' +
'              padding: 14px 16px; font-family: "SF Mono","Fira Code",Menlo,monospace;\n' +
'              font-size: 0.87rem; line-height: 1.6; white-space: pre-wrap;\n' +
'              word-break: break-word; min-height: 60px; }\n' +
'    #output.has-error { color: #fca5a5; }\n' +
'    #output:empty { display: none; }\n' +
'    #pl-form { display: none; margin-top: 16px; }\n' +
'    .field { margin-bottom: 14px; }\n' +
'    .field label { display: block; font-size: 0.88rem; font-weight: 600;\n' +
'                   margin-bottom: 4px; color: #444; }\n' +
'    .text-input { width: 100%; padding: 8px 10px; border: 1px solid #d1d5db;\n' +
'                  border-radius: 6px; font-size: 0.9rem; font-family: inherit;\n' +
'                  background: #fff; color: #1a1a2e; outline: none; }\n' +
'    .text-input:focus { border-color: #5271ff;\n' +
'                        box-shadow: 0 0 0 2px rgba(82,113,255,0.15); }\n' +
'    .submit-btn { background: #5271ff; color: #fff; border: none; border-radius: 6px;\n' +
'                  padding: 8px 20px; font-size: 0.9rem; font-weight: 600;\n' +
'                  cursor: pointer; margin-top: 4px; }\n' +
'    .submit-btn:hover { background: #3a54d4; }\n' +
'    footer { text-align: center; font-size: 0.75rem; color: #bbb; margin-top: 24px; }\n' +
'    footer a { color: #5271ff; text-decoration: none; }\n' +
'  </style>\n' +
'</head>\n' +
'<body>\n' +
'<div class="page">\n' +
'  <h1>Prolog <span>Program</span></h1>\n' +
  (hasMain ? '' :
'  <div class="notice" id="notice">\n' +
'    <strong>Reminder:</strong> No <code>main/0</code> predicate was found in this program.\n' +
'    Add a clause such as <code>main :- write(hello), nl.</code> so the page\n' +
'    produces output when opened.\n' +
'  </div>\n') +
'  <p class="label">Output</p>\n' +
'  <pre id="output">Running main/0\u2026</pre>\n' +
'  <form id="pl-form" method="get"></form>\n' +
'  <footer>Generated by <a href="https://github.com/luciangreen/pl2js" target="_blank">pl2js</a></footer>\n' +
'</div>\n' +
'<script>\n' +
safeRuntime + '\n' +
'</script>\n' +
'<script>\n' +
'(function () {\n' +
'  \'use strict\';\n' +
'  var prog = ' + escapedProg + ';\n' +
'  var outputEl = document.getElementById(\'output\');\n' +
'  var formEl   = document.getElementById(\'pl-form\');\n' +
'\n' +
'  function showError(msg) {\n' +
'    outputEl.textContent = \'Error: \' + msg;\n' +
'    outputEl.className = \'has-error\';\n' +
'  }\n' +
'\n' +
'  function buildForm(formInputs) {\n' +
'    formEl.innerHTML = \'\';\n' +
'    formInputs.forEach(function (fi) {\n' +
'      if (fi.type === \'hidden\') {\n' +
'        var inp = document.createElement(\'input\');\n' +
'        inp.type  = \'hidden\';\n' +
'        inp.name  = fi.name;\n' +
'        inp.value = fi.value || \'\';\n' +
'        formEl.appendChild(inp);\n' +
'      } else {\n' +
'        var div = document.createElement(\'div\');\n' +
'        div.className = \'field\';\n' +
'        if (fi.prompt) {\n' +
'          var lbl = document.createElement(\'label\');\n' +
'          lbl.setAttribute(\'for\', fi.name);\n' +
'          lbl.textContent = fi.prompt;\n' +
'          div.appendChild(lbl);\n' +
'        }\n' +
'        var inp = document.createElement(\'input\');\n' +
'        inp.type      = \'text\';\n' +
'        inp.id        = fi.name;\n' +
'        inp.name      = fi.name;\n' +
'        inp.className = \'text-input\';\n' +
'        div.appendChild(inp);\n' +
'        formEl.appendChild(div);\n' +
'      }\n' +
'    });\n' +
'    var btn = document.createElement(\'button\');\n' +
'    btn.type      = \'submit\';\n' +
'    btn.className = \'submit-btn\';\n' +
'    btn.textContent = \'Submit\';\n' +
'    formEl.appendChild(btn);\n' +
'    formEl.style.display = \'block\';\n' +
'  }\n' +
'\n' +
'  try {\n' +
'    if (!window.pl2js) { showError(\'pl2js runtime not available.\'); return; }\n' +
'\n' +
'    var formArgs = {};\n' +
'    new URLSearchParams(window.location.search).forEach(function (v, k) {\n' +
'      formArgs[k] = v;\n' +
'    });\n' +
'\n' +
'    var result = pl2js.runQuery(prog, \'main.\', 10, formArgs);\n' +
'\n' +
'    if (result.error) {\n' +
'      showError(result.error);\n' +
'    } else if (result.formInputs && result.formInputs.length > 0) {\n' +
'      outputEl.textContent = result.output || \'\';\n' +
'      outputEl.className = \'\';\n' +
'      buildForm(result.formInputs);\n' +
'    } else if (!result.ok && !result.output) {\n' +
'      outputEl.textContent = \'false. (main/0 has no solutions)\';\n' +
'      outputEl.className = \'\';\n' +
'    } else {\n' +
'      outputEl.textContent = result.output ||\n' +
'        \'true. (main/0 succeeded with no output)\';\n' +
'      outputEl.className = \'\';\n' +
'    }\n' +
'  } catch (e) {\n' +
'    showError(e.message || String(e));\n' +
'  }\n' +
'})();\n' +
'</script>\n' +
'</body>\n' +
'</html>\n';
  }

  // =========================================================================
  // SECTION 13: Export
  // =========================================================================

  const pl2js = {
    tokenize,
    parsePrologSource,
    buildDatabase,
    runQuery,
    hasMainPredicate,
    generateHtml,
    /** Render a term to a display string (no environment). */
    termToString: function (term) { return _termStr({}, term); },
    /**
     * Load a file into the browser file store so that read_file/2 and
     * read_folder/2 can access it during query execution.
     *
     * Call this (or use the Load File / Load Folder buttons in index.html)
     * before runQuery() whenever your Prolog program calls read_file/2 or
     * read_folder/2 in a browser environment.
     *
     * @param {string} path    — file path as it will appear in read_file/2
     *                           (e.g. 'mydata/input.txt' or just 'input.txt')
     * @param {string} content — text content of the file
     */
    loadFile: function (path, content) {
      if (content === undefined || content === null) {
        delete _browserFiles[path];
      } else {
        _browserFiles[path] = content;
      }
    },

    /**
     * @deprecated Use pl2js.loadFile() instead.
     * Kept for backwards compatibility — now populates the browser file store
     * (same as loadFile) rather than the old internal virtual file system.
     *
     * @param {string} path    — file path (e.g. 'input.txt')
     * @param {string} content — text content of the file
     */
    registerFile: function (path, content) { _browserFiles[path] = content; }
  };

  if (typeof module !== 'undefined' && module.exports) {
    module.exports = pl2js;
  } else {
    root.pl2js = pl2js;
  }

})(typeof window !== 'undefined' ? window : this);
