// A Formality term is an ADT represented by a JSON
const Var = (index)            => ["Var", {index}];
const Typ = ()                 => ["Typ", {}];
const All = (name, bind, body) => ["All", {name, bind, body}];
const Lam = (name, bind, body) => ["Lam", {name, bind, body}];
const App = (func, argm)       => ["App", {func, argm}];
const Let = (name, copy, body) => ["Let", {name, copy, body}];
const Ref = (name)             => ["Ref", {name}];

// A context is an array of (name, type, term) triples
const Ctx = () => null;

const extend = (ctx, bind) => {
  return {head: bind, tail: ctx};
}

const get_bind = (ctx, i, j = 0) => {
  if (!ctx) {
    return null;
  } else if (j < i) {
    return get_bind(ctx.tail, i, j + 1);
  } else {
    var name = ctx.head[0];
    var term = ctx.head[1] ? shift(ctx.head[1], i, 0) : null;
    var type = ctx.head[2] ? shift(ctx.head[2], i, 0) : null;
    return [name, term, type];
  }
}

const get_name = (ctx, i) => {
  const count = (ctx, name, i) => {
    return i === 0 ? 0 : (ctx.head[0] === name ? 1 : 0) + count(ctx.tail, name, i - 1);
  }
  const repeat = (str, i) => {
    return i === 0 ? "" : str + repeat(str, i - 1);
  }
  var name = get_bind(ctx, i)[0];
  return repeat("'", count(ctx, name, i)) + name;
}

const get_type = (ctx, i) => {
  return get_bind(ctx, i) ? get_bind(ctx, i)[1] : null;
}

const get_term = (ctx, i) => {
  return get_bind(ctx, i) ? get_bind(ctx, i)[2] : null;
}

const index_of = (ctx, name, skip, i = 0) => {
  if (!ctx) {
    return null;
  } else if (ctx.head[0] === name && skip > 0) {
    return index_of(ctx.tail, name, skip - 1, i + 1);
  } else if (ctx.head[0] !== name) {
    return index_of(ctx.tail, name, skip, i + 1);
  } else {
    return i;
  }
}

// Pretty prints a context
const show_context = (ctx, i = 0) => {
  var bind = get_bind(ctx, i);
  if (bind) {
    var type = ": " + (bind[1] ? show(norm(bind[1], {}, true), ctx) : "?");
    var term = "= " + (bind[2] ? show(norm(bind[2], {}, true), ctx) : "?");
    return show_context(ctx, i + 1) + bind[0] + "\n" + type + "\n" + term + "\n\n";
  } else {
    return "";
  }
}

// Converts a term to a string
const show = ([ctor, args], ctx = Ctx()) => {
  switch (ctor) {
    case "Var":
      return get_name(ctx, args.index) || "#" + args.index;
    case "Typ":
      return "Type";
    case "All":
      var name = args.name;
      var bind = show(args.bind, extend(ctx, [args.name, null, null]));
      var body = show(args.body, extend(ctx, [args.name, null, null]));
      return "{" + name + " : " + bind + "} " + body;
    case "Lam":
      var name = args.name;
      var bind = args.bind && show(args.bind, extend(ctx, [name, null, null]));
      var body = show(args.body, extend(ctx, [name, null, null]));
      return bind ? "[" + name + " : " + bind + "] " + body : "[" + name + "] " + body;
    case "App":
      var text = ")";
      var term = [ctor, args];
      while (term[0] === "App") {
        text = " " + show(term[1].argm, ctx) + text;
        term = term[1].func;
      }
      return "(" + show(term, ctx) + text;
    case "Let":
      var name = args.name;
      var copy = show(args.copy, ctx);
      var body = show(args.body, extend(ctx, [args.name, null, null]));
      return "let " + name + " " + copy + " " + body;
    case "Ref":
      return args.name;
  }
}

// Converts a string to a term
const parse = (code) => {
  function is_space(char) {
    return char === " " || char === "\t" || char === "\n";
  }

  function is_name_char(char) {
    return "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_.~-".indexOf(char) !== -1;
  }

  function skip_spaces() {
    while (index < code.length && is_space(code[index])) {
      index += 1;
    }
    return index;
  }

  function match(string) {
    skip_spaces();
    var sliced = code.slice(index, index + string.length);
    if (sliced === string) {
      index += string.length;
      return true;
    }
    return false;
  }

  function error(text) {
    text += "This is the relevant code:\n\n<<<";
    text += code.slice(index - 64, index) + "<<<HERE>>>";
    text += code.slice(index, index + 64) + ">>>";
    throw text;
  }

  function parse_exact(string) {
    if (!match(string)) {
      error("Parse error, expected '" + string + "'.\n");
    }
  }

  function parse_name() {
    skip_spaces();
    var name = "";
    while (index < code.length && is_name_char(code[index])) {
      name = name + code[index];
      index += 1;
    }
    return name;
  }

  function parse_term(ctx) {
    // Comment
    if (match("--")) {
      while (index < code.length && code[index] !== "\n") {
        index += 1;
      }
      return parse_term(ctx);
    }

    // Application
    else if (match("(")) {
      var func = parse_term(ctx);
      while (index < code.length && !match(")")) {
        var argm = parse_term(ctx);
        var func = App(func, argm);
        skip_spaces();
      }
      return func;
    }

    // Type
    else if (match("Type")) {
      return Typ();
    }

    // Forall
    else if (match("{")) {
      var name = parse_name();
      var skip = parse_exact(":");
      var bind = parse_term(extend(ctx, [name, null, Var(0)]));
      var skip = parse_exact("}");
      var body = parse_term(extend(ctx, [name, null, Var(0)]));
      return All(name, bind, body);
    }

    // Lambda
    else if (match("[")) {
      var name = parse_name();
      var bind = match(":") ? parse_term(extend(ctx, [name, null, Var(0)])) : null;
      var skip = parse_exact("]");
      var body = parse_term(extend(ctx, [name, null, Var(0)]));
      return Lam(name, bind, body);
    }

    // Let
    else if (match("let")) {
      var name = parse_name();
      var copy = parse_term(ctx);
      var body = parse_term(extend(ctx, [name, null, Var(0)]));
      return Let(name, copy, body);
    }

    // Variable / Reference
    else {
      var name = parse_name();
      var skip = 0;
      while (match("'")) {
        skip += 1;
      }
      var var_index = index_of(ctx, name, skip);
      if (var_index === null) {
        return Ref(name, false);
      } else {
        return get_bind(ctx, var_index)[2];
      }
    }
  }

  var index = 0;
  var defs = {};
  while (index < code.length) {
    if (match("--")) {
      while (index < code.length && code[index] !== "\n") {
        index += 1;
      }
    } else {
      var name = parse_name();
      var type = match(":") ? parse_term(Ctx()) : null;
      var skip = parse_exact("=");
      var term = parse_term(Ctx());
      defs[name] = {term: term, type: type, done: false};
      skip_spaces();
    }
  }

  return defs;
}

// Shifts a term
const shift = ([ctor, term], inc, depth) => {
  switch (ctor) {
    case "Var":
      return Var(term.index < depth ? term.index : term.index + inc);
    case "Typ":
      return Typ();
    case "All":
      var name = term.name;
      var bind = shift(term.bind, inc, depth + 1);
      var body = shift(term.body, inc, depth + 1);
      return All(name, bind, body);
    case "Lam":
      var name = term.name;
      var bind = term.bind && shift(term.bind, inc, depth + 1);
      var body =              shift(term.body, inc, depth + 1);
      return Lam(name, bind, body);
    case "App":
      var func = shift(term.func, inc, depth);
      var argm = shift(term.argm, inc, depth);
      return App(func, argm);
    case "Let":
      var name = term.name;
      var copy = shift(term.copy, inc, depth);
      var body = shift(term.body, inc, depth + 1);
      return Let(name, copy, body);
    case "Ref":
      return Ref(term.name);
  }
}

// Substitution
const subst = ([ctor, term], val, depth) => {
  switch (ctor) {
    case "Var":
      return depth === term.index ? val : Var(term.index - (term.index > depth ? 1 : 0));
    case "Typ":
      return Typ();
    case "All":
      var name = term.name;
      var bind = subst(term.bind, val && shift(val, 1, 0), depth + 1);
      var body = subst(term.body, val && shift(val, 1, 0), depth + 1);
      return All(name, bind, body);
    case "Lam":
      var name = term.name;
      var bind = term.bind && subst(term.bind, val && shift(val, 1, 0), depth + 1);
      var body =              subst(term.body, val && shift(val, 1, 0), depth + 1);
      return Lam(name, bind, body);
    case "App":
      var func = subst(term.func, val, depth);
      var argm = subst(term.argm, val, depth);
      return App(func, argm);
    case "Let":
      var name = term.name;
      var copy = subst(term.copy, val, depth);
      var body = subst(term.body, val && shift(val, 1, 0), depth + 1);
      return Let(name, copy, body);
    case "Ref":
      var name = term.name;
      return Ref(name);
  }
}

// Equality
const equals = (a, b, defs) => {
  // Checks if whnfs are equal without dereferencing
  var a = norm(a, {}, false);
  var b = norm(b, {}, false);
  if ( a[0] === "Ref" && b[0] === "Ref" && a[1].name === b[1].name
    || a[0] === "App" && b[0] === "App" && equals(a[1].func, b[1].func, defs) && equals(a[1].argm, b[1].argm, defs)
    || a[0] === "Cpy" && b[0] === "Cpy" && equals(a[1].copy, b[1].copy, defs) && equals(a[1].body, b[1].body, defs)) {
    return true;
  }
  // Otherwise, checks if whnfs are equal with dereferencing
  var a = norm(a, defs, false);
  var b = norm(b, defs, false);
  if (a[0] === "Typ" && b[0] === "Typ") {
    return true;
  } else if (a[0] === "All" && b[0] === "All") {
    var bind = equals(a[1].bind, b[1].bind, defs);
    var body = equals(a[1].body, b[1].body, defs);
    return bind && body;
  } else if (a[0] === "Lam" && b[0] === "Lam") {
    var body = equals(a[1].body, b[1].body, defs);
    return body;
  } else if (a[0] === "App" && b[0] === "App") {
    var func = equals(a[1].func, b[1].func, defs);
    var argm = equals(a[1].argm, b[1].argm, defs);
    return func && argm;
  } else if (a[0] === "Var" && b[0] === "Var") {
    return a[1].index === b[1].index;
  }
  // Otherwise, terms are different
  return false;
}

// Norm
const norm = ([ctor, term], defs, full) => {
  const cont = full ? norm : (x => x);
  const apply = (func, argm) => {
    var func = norm(func, defs, false);
    if (func[0] === "Lam") {
      return norm(subst(func[1].body, argm, 0), defs, full);
    } else {
      return App(func, cont(argm, defs, full));
    }
  }
  const dereference = (name) => {
    if (defs[name] && !defs[name].seen) {
      var term = norm(defs[name].term, defs, full);
      var term = term;
      return term;
    } else {
      return Ref(name);
    }
  }
  switch (ctor) {
    case "Var": return Var(term.index);
    case "Typ": return Typ();
    case "All": return All(term.name, cont(term.bind, defs, false), cont(term.body, defs, full));
    case "Lam": return Lam(term.name, term.bind && cont(term.bind, defs, false), cont(term.body, defs, full)); 
    case "App": return apply(term.func, term.argm);
    case "Let": return norm(subst(term.body, term.copy, 0), defs, full);
    case "Ref": return dereference(term.name);
  }
}

// Check
const infer = (term, defs, ctx = Ctx()) => {
  try {
    norm(term, defs, false);
  } catch (e) {
    throw "[ERROR]\nCouldn't determine head of: `" + show(term, ctx) + "`. Possibly non-terminating expression?";
  }
  switch (term[0]) {
    case "Typ":
      return Typ();
    case "All":
      var ex_ctx = extend(ctx, [term[1].name, term[1].bind, Var(0)]);
      var bind_t = infer(term[1].bind, defs, ex_ctx);
      var body_t = infer(term[1].body, defs, ex_ctx);
      if (!equals(bind_t, Typ(), defs) || !equals(body_t, Typ(), defs)) {
        throw "[ERROR]\nForall not a type: `" + show(term, ctx) + "`. Context:\n\n" + show_context(ctx);
      }
      return Typ();
    case "Lam":
      if (term[1].bind === null) {
        throw "[ERROR]\nCan't infer non-annotated lambda. Context:\n\n" + show_context(ctx);
      } else {
        var ex_ctx = extend(ctx, [term[1].name, term[1].bind, Var(0)]);
        var body_t = infer(term[1].body, defs, ex_ctx);
        var term_t = All(term[1].name, term[1].bind, body_t);
        infer(term_t, defs, ctx);
        return term_t;
      }
    case "App":
      var func_t = norm(infer(term[1].func, defs, ctx), defs, false);
      if (func_t[0] !== "All") {
        throw "[ERROR]\nNon-function application on `" + show(term, ctx) + "`. Context:\n\n" + show_context(ctx);
      }
      var bind_t = subst(func_t[1].bind, term[1].argm, 0);
      check(term[1].argm, bind_t, defs, ctx);
      return subst(func_t[1].body, term[1].argm, 0);
    case "Let":
      var copy_t = infer(term[1].copy, defs, ctx);
      var ex_ctx = extend(ctx, [term[1].name, shift(copy_t, 1, 0), shift(term[1].copy, 1, 0)]);
      return subst(infer(term[1].body, defs, ex_ctx), term[1].copy, 0);
    case "Ref":
      if (defs[term[1].name]) {
        var def = defs[term[1].name];
        if (def.done) {
          return def.type;
        } else {
          def.done = true;
          if (def.type) {
            check(def.term, def.type, defs, ctx);
          } else {
            def.type = infer(def.term, defs, ctx);
          }
          return def.type;
        }
      } else {
        throw "[ERROR]\nUndefined reference: `" + term[1].name + "`.";
      }
    case "Var":
      return get_type(ctx, term[1].index);
  }
}

// Checks if a term has given type
const check = (term, type, defs, ctx = Ctx()) => {
  var type = norm(type, defs, false);
  if (type[0] === "All" && term[0] === "Lam" && !term[1].bind) {
    check(term[1].body, type[1].body, defs, extend(ctx, [type[1].name, type[1].bind, Var(0)]));
    infer(type, defs, ctx);
  } else {
    var term_t = infer(term, defs, ctx);
    try {
      var checks = equals(type, term_t, defs);
    } catch (e) {
      var checks = false;
      console.log("Couldn't decide if terms are equal.");
      console.log(e);
    }
    if (!checks) {
      throw show_mismatch(ctx, type, norm(term_t, defs, false), () => "`" + show(term, ctx) + "`");
    }
  }
}

// Formats a type-mismatch error message
const show_mismatch = (ctx, expect, actual, value) => {
  var text = "";
  text += "[ERROR]\nType mismatch on " + value() + ".\n";
  text += "- Expect = " + show(norm(expect, {}, true), ctx) + "\n";
  text += "- Actual = " + show(norm(actual, {}, true), ctx) + "\n"
  text += "\n[CONTEXT]\n" 
  text += show_context(ctx);
  return text;
}

module.exports = {
  Ctx,
  extend,
  get_bind,
  get_name,
  get_type,
  get_term,
  index_of,
  show_context,
  show_mismatch,
  Var,
  Typ,
  All,
  Lam,
  App,
  Let,
  Ref,
  show,
  parse,
  norm,
  infer,
  check
};
