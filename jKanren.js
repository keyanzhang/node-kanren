// µKanren: https://github.com/jasonhemann/microKanren
// Copyright (C) 2013 Jason Hemann and Daniel P. Friedman

'use strict';

var _ = require('lodash');

// Utils
// ConsCell data structure
function ConsCell(x) {
  this._car = x; // a value, undefined, or another ConsCell
  this._cdr = null;
};

ConsCell.prototype.setCar = function(n) {
  this._car = n;
};

ConsCell.prototype.setCdr = function(n) {
  this._cdr = n;
};

ConsCell.prototype.getCar = function() {
  return this._car;
};

ConsCell.prototype.getCdr = function() {
  return this._cdr;
};

function writer(inp) {
  var n = inp;
  var result = "";
  
  if (!(n instanceof ConsCell)) {
    if (isNull(n)) {
      result += "()";
    }
    else {
      if (n === true) {
        result += "#t";
      }
      else if (n === false) {
        result += "#f";
      }
      else if (_.isArray(n)) {
        result += '#(' + n.join(' ') + ')';
      }
      else {
        result += n;        
      }
    }

    return result;
  }

  result += "(";

  while (n) {
    result += writer(n._car);

    if (isNull(n._cdr)) {
      break;
    }
    else if (!(n._cdr instanceof ConsCell)) {
      result += " . " + writer(n._cdr);
      break;
    }
    else {
      result += " ";
      n = n._cdr;
    }
  }

  result += ")";

  return result;
}

// singleton
var Null = {
  toString: function() {
    return '()';
  }
};

function isNull(x) {
  return x === Null;
}

function cons(a, d) {
  var result = new ConsCell(a);
  result.setCdr(d);
  return result;
}

function car(pair) {
  if (!(pair instanceof ConsCell)) {
    throw new TypeError('car: ' + pair + ' is not a pair');
  }

  return pair.getCar();
}

function cdr(pair) {
  if (!(pair instanceof ConsCell)) {
    throw new TypeError('cdr: ' + pair + ' is not a pair');
  }

  return pair.getCdr();
}

function list() {
  return _.foldr(arguments, function(ls, x) {
    return cons(x, ls);
  }, Null);
}

function isPair(x) {
  return x instanceof ConsCell;
}

function length(x) {
  if (_.isArray(x)) {
    return x.length;
  }
  else if (isNull(x)) {
    return 0;
  }
  else if (x instanceof ConsCell) {
    var result = 0;
    while (!isNull(x)) {
      result++;
      x = x.getCdr();
    }
    return result;
  }
  else {
    throw new TypeError('length: ' + x + ' has no length');
  }
}

function map(ls, f) {
  if (_.isArray(ls)) {
    return _.map(ls, f);
  }

  function mapConsCell(x, f) {
    if (isNull(x)) {
      return Null;
    }

    return cons(f(car(x)), mapConsCell(cdr(x), f));
  }

  return mapConsCell(ls, f);
}

function reverse(x) {
  var result;
  if (_.isArray(x)) {
    result = [];
    for (var i = x.length - 1; i >= 0; i--) {
      result.push(x[i]);
    }
    return result;
  }
  else if (isNull(x)) {
    return Null;
  }
  else if (isPair(x)) {
    result = Null;
    while (!isNull(x)) {
      result = cons(car(x), result);
      x = cdr(x);
    }
    return result;
  }
  else {
    throw new TypeError('reverse: ' + x + ' can\'t be reversed');
  }
}

function apply(ctx, f, ls) {
  if (_.isArray(ls)) {
    return f.apply(ctx, ls);
  }
  else {
    var args = [];
    while (!isNull(ls)) {
      args.push(car(ls));
      ls = cdr(ls);
    }
    return f.apply(ctx, args);
  }
}

function and() {
  if (arguments.length === 0) {
    return true;
  }

  if (_.some(arguments, function(x) {
    return x === false;
  })) {
    return false;
  }
  
  return _.last(arguments);
}

function or() {
  if (arguments.length === 0) {
    return false;
  }

  for (var i = 0; i < arguments.length; i++) {
    if (arguments[i] !== false) {
      return arguments[i];
    }
  }

  return false;
}

function kVar(c) {
  return [c];
}

function isVar(x) {
  return _.isArray(x);
}

function equalVar(x1, x2) {
  return x1[0] === x2[0]; // should be 2 numbers here
}

function assp(lss, p) { // the predicate is the 2nd parameter here
  if (isNull(lss)) {
    return false;
  }
  else if (p(car(car(lss)))) {
    return car(lss);
  }
  else {
    return assp(cdr(lss), p);
  }
}

function walk(u, s) {
  var pr = and(isVar(u), assp(s, function(v) {
    return equalVar(u, v);
  }));
  
  if (pr !== false) { // simulate Scheme's behavior
    return walk(cdr(pr), s);
  }
  else {
    return u;
  }
}

function extS(x, v, s) {
  return cons(cons(x, v), s);
}

function equiv(u, v) { // ==
  return function(s_c) {
    var s = unify(u, v, car(s_c));

    if (s !== false) { // @? !== false
      return unit(cons(s, cdr(s_c)));
    }
    else {
      return mzero;
    }
  };
}

function unit(s_c) {
  return cons(s_c, mzero);
}

var mzero = Null;

function unify(u, v, s) {
  var _u = walk(u, s);
  var _v = walk(v, s);
  var u = _u;
  var v = _v;

  if (and(isVar(u), isVar(v), equalVar(u, v))) {
    return s;
  }
  else if (isVar(u)) {
    return extS(u, v, s);
  }
  else if (isVar(v)) {
    return extS(v, u, s);
  }
  else if (and(isPair(u), isPair(v))) {
    var s = unify(car(u), car(v), s);
    return and(s, unify(cdr(u), cdr(v), s));
  }
  else {
    return and(u === v, s); // @? eqv?
  }
}

function call_fresh(f) {
  return function(s_c) {
    var c = cdr(s_c);
    var rator = f(kVar(c));
    return rator(cons(car(s_c), c + 1));
  };
}

function mplus($1, $2) {
  if (isNull($1)) {
    return $2;
  }
  else if (_.isFunction($1)) {
    return function() {
      return mplus($2, $1());
    };
  }
  else {
    return cons(car($1), mplus(cdr($1), $2));
  }
}

function bind($, g) {
  if (isNull($)) {
    return mzero;
  }
  else if (_.isFunction($)) {
    return function() {
      return bind($(), g);
    };
  }
  else {
    return mplus(g(car($)), bind(cdr($), g));
  }
}

function disj(g1, g2) {
  return function(s_c) {
    return mplus(g1(s_c), g2(s_c));
  };
}

function conj(g1, g2) {
  return function(s_c) {
    return bind(g1(s_c), g2);
  };
}

var emptyState = cons(Null, 0);

var a_and_b = conj(call_fresh(function(a) {
  return equiv(a, 7);
}), call_fresh(function(b) {
  return disj(equiv(b, 5), equiv(b, 6));
}));

// console.log(writer(a_and_b(emptyState)));

// console.log((call_fresh(function(q) {
//   return equiv(q, 5);
// }))(emptyState));

// wrappers

function call_goal(g) {
  return g(emptyState);
}

function pull($) {
  if (_.isFunction($)) {
    return pull($());
  }
  else {
    return $;
  }
}

function takeAll($) {
  var $ = pull($);

  if (isNull($)) {
    return Null;
  }
  else {
    return cons(car($), takeAll(cdr($)));
  }
}

function take(n, $) {
  if (n === 0) {
    return Null;
  }
  else {
    var $ = pull($);
    if (isNull($)) {
      return Null;
    }
    else {
      return cons(car($), take(n - 1, cdr($)));
    }
  }
}

function walk$(v, s) {
  var v = walk(v, s);

  if (isVar(v)) {
    return v;
  }
  else if (isPair(v)) {
    return cons(walk$(car(v), s), walk$(cdr(v), s));
  }
  else {
    return v;
  }
}

function reify1st(s_c) {
  var v = walk$(kVar(0), car(s_c));

  return walk$(v, reifyS(v, Null));
}

function reifyS(v, s) {
  var v = walk(v, s);

  if (isVar(v)) {
    var n = reifyName(length(s));
    return cons(cons(v, n), s);
  }
  else if (isPair(v)) {
    return reifyS(cdr(v), reifyS(car(v), s));
  }
  else {
    return s;
  }
}

function reifyName(n) {
  // return n; // @TODO: string->symbol
  return '_.' + n;
}

function fresh_nf(n, f) {
  function app_f_v$(n, v$) {
    if (n === 0) {
      return apply(this, f, reverse(v$));
    }
    else {
      return call_fresh(function(x) {
        return app_f_v$(n - 1, cons(x, v$));
      });
    }
  }

  return app_f_v$(n, Null);
}


// console.log('end of jKanren.js');
