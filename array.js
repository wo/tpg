//
// This file defines some Array methods, of which a few are for
// general use...
//
//    Array.prototype.remove = function(element)
//    Array.prototype.insert = function(element, index)
//    Array.prototype.copy = function()
//    Array.prototype.copyDeep = function()
//
// ...and the rest for use with arrays that represent formulas.
//
// Internally, formulas are arrays (for performance reasons):
//
//    |~A|      => [tc.NOT, |A|]
//    |A&B|     => [tc.AND, |A|, |B|]
//    |ExA|     => [tc.SOME, |x|, |A|]
//    |Rab|     => [|R|, [|a|, |b|]]
//
// where predicates, variables and constants (including function
// symbols) are represented by integers, function terms by arrays
// whose first element is the function symbol, the other the
// arguments:
//
//    predicates: 1, 4, 7, ...   (n % 3 == 1)  
//    constants:  2, 5, 8, ...   (n % 3 == 2)
//    variables:  3, 6, 9, ...   (n % 3 == 0)
//    functions terms:  [2,5], [5,3,8], [8,6,[8,2]], ...
//
// The following formula methods are defined below:
//
//    Array.prototype.negate = function()
//    Array.prototype.substitute = function(origTerm, newTerm)
//    Array.prototype.unify = function(formula)
//    Array.prototype.normalize = function()
//    Array.prototype.getFreeVariables = function()
//    Array.prototype.getBoundVariables = function()
//    Array.prototype.getConstants = function(withArity) 
//    Array.prototype.getPredicates = function(withArity)
//    Array.prototype.equals = function(formula)
//
// We also define a namespace object for global constants about whose
// value we don't care. (Except perhaps that they are all negative
// numbers.) E.g. tc.NOT is used as a global constant that stands
// for the internal negation symbol. (Simply using a string like
// "negation" or "~" instead slows down the script a lot.)
//
// First, though, some code for debugging (lines begin with 'debug' to
// help automatic removal):

debug = function(str) { if (!self.debugWin) debugPopup(); debugWin.document.write("<pre>"+str+"</pre>"); }
debugPopup = function() { debugWin = self.open("about:blank","debugWin"); if (!self.debugWin) alert("unblock popups!"); }
debug("hello, this is the debugging window");

// The namespace object (mostly used in translator.js):
tc = {
    counter : 0,
    register : function(constName) {
        this[constName] = --this.counter;
    },
    getName : function(num) {
        for (var n in this) {
            if (this[n] == num && n != "counter") return n;
        }
    }
}

// General Array methods:

Array.prototype.isArray = true;

Array.prototype.toString = function() {
    return "["+this.join(",")+"]";
}

if (!Array.prototype.includes) { // IE
    Array.prototype.includes = function(element) {
        for (var i=0; i<this.length; i++) {
            if (this[i] == element) return true;
        }
        return false;
    }
}

Array.prototype.remove = function(element) {
    // removes the first element that weakly equals (==) <element>
    for (var i=0; i<this.length; i++) {
        if (this[i] == element) {
            this.splice(i, 1);
            break;
        }
    }
    return element;
}

Array.prototype.insert = function(element, index) {
    // inserts <element> at the given position, shifting the existing
    // ones further back
    return this.splice(index, 0, element);
}

Array.prototype.copy = function() {
    // returns a shallow copy of this array.
    var result = [];
    for (var i=0; i<this.length; i++) result[i] = this[i];
    return result;
}

Array.prototype.copyDeep = function() {
    // returns a deep copy of this array (deep only with respect to arrays,
    // not objects, so objects will be copied by reference).
    var result = [];
    for (var i=0; i<this.length; i++) {
        if (this[i].isArray) result[i] = this[i].copyDeep();
        else result[i] = this[i];
    }
    return result;
}


// The remaining Array methods are used to manipulate formulas. 

Array.prototype.negate = function() {
    return [tc.NOT, this];
}

// xxx maybe more efficient: prototype.type() => tc.GAMMA etc.; for we
// often go through all of is_alpha, is_gamma, etc.

Array.prototype.is_alpha = function() {
    return ((this[0] == tc.AND) ||
            (this[0] == tc.NOT && (this[1][0] == tc.OR || this[1][0] == tc.THEN)));
}

Array.prototype.alpha1 = function() {
    // return first formula for alpha expansion
    if (this[0] == tc.AND) return this[1].copyDeep();
    // this[0] == tc.NOT
    if (this[1][0] == tc.OR) return this[1][1].copyDeep().negate();
    if (this[1][0] == tc.THEN) return this[1][1].copyDeep();
}

Array.prototype.alpha2 = function() {
    // return second formula for alpha expansion
    if (this[0] == tc.AND) return this[2].copyDeep();
    // this[0] == tc.NOT
    if (this[1][0] == tc.OR) return this[1][2].copyDeep().negate();
    if (this[1][0] == tc.THEN) return this[1][2].copyDeep().negate();
}

Array.prototype.is_beta = function() {
    return ((this[0] == tc.OR) ||
            (this[0] == tc.THEN) ||
            (this[0] == tc.IFF) ||
            (this[0] == tc.NOT && (this[1][0] == tc.AND || this[1][0] == tc.IFF)));
}

Array.prototype.beta1 = function() {
    // return first formula for beta expansion
    if (this[0] == tc.OR) return this[1].copyDeep();
    if (this[0] == tc.THEN) return this[1].copyDeep().negate();
    // We treat A <-> B as expanding to (A&B) | (~A&~B), and ~(A<->B)
    // to (A&~B) | (~A&B); these intermediate notes will be removed
    // before displaying trees.
    if (this[0] == tc.IFF) return [tc.AND, this[1].copyDeep(), this[2].copyDeep()];
    // this[0] == tc.NOT
    if (this[1][0] == tc.AND) return this[1][1].copyDeep().negate();
    // We treat A <-> B as expanding to (A&B) | (~A&~B), and ~(A<->B)
    // to (A&~B) | (~A&B); these intermediate notes will be removed
    // before displaying trees.
    if (this[1][0] == tc.IFF) return [tc.AND, this[1][1].copyDeep(), this[1][2].copyDeep().negate()];
}

Array.prototype.beta2 = function() {
    // return second formula for beta expansion
    if (this[0] == tc.OR || this[0] == tc.THEN) return this[2].copyDeep();
    if (this[0] == tc.IFF) return [tc.AND, this[1].copyDeep().negate(), this[2].copyDeep().negate()];
    // this[0] == tc.NOT
    if (this[1][0] == tc.AND) return this[1][2].copyDeep().negate();
    if (this[1][0] == tc.IFF) return [tc.AND, this[1][1].copyDeep().negate(), this[1][2].copyDeep()];
}

Array.prototype.is_gamma = function() {
    return ((this[0] == tc.ALL) ||
            (this[0] == tc.NOT && this[1][0] == tc.SOME));
}

Array.prototype.is_delta = function() {
    return ((this[0] == tc.SOME) ||
            (this[0] == tc.NOT && this[1][0] == tc.ALL));
}

Array.prototype.matrix = function() {
    // return matrix formula [Fx for (Ax)Fx]
    if (this[0] != tc.NOT) return this[2].copyDeep();
    // ~(Ex)A
    else return this[1][2].copyDeep().negate();
}

Array.prototype.boundVar = function() {
    // return variable bound by gamma of delta formula
    if (this[0] == tc.ALL || this[0] == tc.SOME) return this[1];
    else return this[1][1];
}

Array.prototype.is_doublenegation = function() {
    return (this[0] == tc.NOT && this[1][0] == tc.NOT); 
}
 
Array.prototype.substitute = function(origTerm, newTerm, shallow) {
    // replaces all (free) occurrences of <origTerm> by <newTerm>.
    // If <shallow>, don't replace terms in function arguments
    if (this[0] < 0) { // fla is not atomic
        if (this.length == 2) { // negated
            this[1].substitute(origTerm, newTerm, shallow);
            return this;
        }
        if (!this[1].isArray) { // quantified 
            if (this[1] != origTerm) { // otherwise origTerm is bound var
                this[2].substitute(origTerm, newTerm, shallow);
            }
            return this;
        }
        this[1].substitute(origTerm, newTerm, shallow);
        this[2].substitute(origTerm, newTerm, shallow);
        return this;
    }
    if (this[0] % 3 == 1) { // fla is atomic
        this[1].substitute(origTerm, newTerm, shallow);
    }
    // fla is term list (predicate arguments or function application)
    for (var i=0; i<this.length; i++) {
        if (this[i].isArray) {
            if (this[i].equals(origTerm)) this[i] = newTerm;
            else if (!shallow) this[i].substitute(origTerm, newTerm, shallow);
        }
        else if (this[i] == origTerm) this[i] = newTerm;
    }
    return this;
}

Array.prototype.unify = function(formula) {
    // Checks whether this formula can be unified with the argument formula.
    // Returns a (minimally) unifying substitution if yes, otherwise false.
    // A substitution is simply an array of terms which is interpreted as
    // arr[1] -> arr[2], arr[3] -> arr[4], ... 
    // Warning: Don't confuse an empty unifier [] with false!
    //
    // The following algorithm is losely based on the one described in S.
    // Hölldobler, Logik und Logikprogrammierung, Synchron Verlag,
    // Heidelberg 2001, §4.5, which is there proven to be complete and
    // sound.
    //
    // Note that this only works for literals.  For quantified
    // formulas one would have to care about capturing by quantified
    // variables, which would complicate things a little.
    if (this.length != 2) return false;
    if (this[0] != formula[0]) return false;
    if (this[0] == tc.NOT) return this[1].unify(formula[1]);
    if (this[1].length != formula[1].length) return false;
    // So we have two atomic formulas of the same arity.
    // Now we walk through all the pairs of terms. Remember:
    //    predicates: 1, 4, 7, ...   (n % 3 == 1)  
    //    constants:  2, 5, 8, ...   (n % 3 == 2)
    //    variables:  3, 6, 9, ...   (n % 3 == 0)
    //    functions:  [2,5], [5,3,8], [8,6,[8,2]], ...
    var unifier = [];
    var terms1 = this[1].copyDeep();
    var terms2 = formula[1].copyDeep();
    var t1, t2;
    while (t1 = terms1.shift(), t2 = terms2.shift()) {
        if (t1 == t2) {
            // terms are (constants or variables and) equal: nothing to do.
            continue; 
        }
        if (t1.isArray && t2.isArray) {
            // both terms are functions: unification fails if function
            // constants differ; otherwise add all the argument pairs
            // to the terms that must be unified.
            if (t1[0] != t2[0]) return false;
            for (var i=1; i<t1.length; i++) {
                terms1.push(t1[i]);
                terms2.push(t2[i]);
            }
            continue;
        }
        if (t1 % 3 != 0 && t2 % 3 != 0) {
            // none of the terms is a variable: unification failed.
            // (Note that t % 3 == NaN if t is an array, and NaN != 0
            // is true.)
            return false;
        }
        if (t1 % 3 != 0) {
            // only second term is a variable: exchange it with first
            // term, so that in what follows the first term is always
            // a variable.
            var temp = t1; t1 = t2; t2 = temp; 
        }
        if (t2.isArray) {
            // t2 is a function: unification fails if it contains t2 among
            // its arguments (or arguments of its ...  arguments).  
            var terms, termss = [t2];
            while (terms = termss.shift()) {
                for (var i=0; i<terms.length; i++) {
                    if (terms[i].isArray) termss.push(terms[i]);
                    else if (terms[i] == t1) return false;
                }
            }
        }
        // now we unify the variable t1 with the term t2: substitute t2
        // for t1 everywhere in the unifier array and in the remaining
        // terms1 and terms2, and add t1/t2 to the unifier array.
        var terms, termss = [unifier, terms1, terms2];
        while (terms = termss.shift()) {
            for (var i=0; i<terms.length; i++) {
                if (terms[i].isArray) termss.push(terms[i]);
                else if (terms[i] == t1) terms[i] = t2;
            }
        }
        unifier.push(t1); unifier.push(t2);
    }
    return unifier;
}

Array.prototype.normalize = function() {
    // returns an equivalent formula in negation normal form, in which
    // left subformulas are generally less complex than right
    // subformulas. (Complexity here means number of disjunctions.)
    switch (this[0]) {
    case tc.AND : {
        // |A&B| = |A|&|B| or |B|&|A|
        var sub1 = this[1].normalize();
        var sub2 = this[2].normalize();
        var res = (sub1.__complexity <= sub2.__complexity) ?
            [tc.AND, sub1, sub2] : [tc.AND, sub2, sub1];
        res.__complexity = sub1.__complexity * sub2.__complexity;
        return res;
    }
    case tc.OR : {
        // |AvB| = |A|v|B| or |B|v|A|
        var sub1 = this[1].normalize();
        var sub2 = this[2].normalize();
        var res = (sub1.__complexity <= sub2.__complexity) ?
            [tc.OR, sub1, sub2] : [tc.OR, sub2, sub1];
        res.__complexity = sub1.__complexity + sub2.__complexity;
        return res;
    }
    case tc.THEN : {
        // |A->B| = |~A|v|B| or |B|v|~A|
        var sub1 = this[1].negate().normalize();
        var sub2 = this[2].normalize();
        var res = (sub1.__complexity <= sub2.__complexity) ?
            [tc.OR, sub1, sub2] : [tc.OR, sub2, sub1];
        res.__complexity = sub1.__complexity + sub2.__complexity;
        return res;
    }
    case tc.IFF : {
        // |A<->B| = |A&B|v|~A&~B| or |~A&~B|v|A&B|
        var sub1 = [tc.AND, this[1], this[2]].normalize();
        var sub2 = [tc.AND, this[1].negate(), this[2].negate()].normalize();
        var res = (sub1.__complexity <= sub2.__complexity) ?
            [tc.OR, sub1, sub2] : [tc.OR, sub2, sub1];
        res.__complexity = sub1.__complexity + sub2.__complexity;
        return res;
    }
    case tc.ALL : case tc.SOME : {
        // |(Ax)A| = Ax|A|
        var sub1 = this[2].normalize();
        var res = [this[0], this[1], sub1];
        res.__complexity = sub1.__complexity;
        return res;
    }
    case tc.NOT : {
        switch (this[1][0]) {
        case tc.AND : {
            // |~(A&B)| = |~A|v|~B| or |~B|v|~A|
            var sub1 = this[1][1].negate().normalize();
            var sub2 = this[1][2].negate().normalize();
            var res = (sub1.__complexity <= sub2.__complexity) ?
                [tc.OR, sub1, sub2] : [tc.OR, sub2, sub1];
            res.__complexity = sub1.__complexity + sub2.__complexity;
            return res;
        }
        case tc.OR : {
            // |~(AvB)| = |~A|&|~B| or |~B|&|~A|
            var sub1 = this[1][1].negate().normalize();
            var sub2 = this[1][2].negate().normalize();
            var res = (sub1.__complexity <= sub2.__complexity) ?
                [tc.AND, sub1, sub2] : [tc.AND, sub2, sub1];
            res.__complexity = sub1.__complexity * sub2.__complexity;
            return res;
        }
        case tc.THEN : {
            // |~(A->B)| = |A|&|~B| or |~B|&|A|
            var sub1 = this[1][1].normalize();
            var sub2 = this[1][2].negate().normalize();
            var res = (sub1.__complexity <= sub2.__complexity) ?
                [tc.AND, sub1, sub2] : [tc.AND, sub2, sub1];
            res.__complexity = sub1.__complexity * sub2.__complexity;
            return res;
        }
        case tc.IFF : {
            // |~(A<->B)| = |A&~B|v|~A&B| or |~A&B|v|A&~B|
            var sub1 = [tc.AND, this[1][1], this[1][2].negate()].normalize();
            var sub2 = [tc.AND, this[1][1].negate(), this[1][2]].normalize();
            var res = (sub1.__complexity <= sub2.__complexity) ?
                [tc.OR, sub1, sub2] : [tc.OR, sub2, sub1];
            res.__complexity = sub1.__complexity + sub2.__complexity;
            return res;
        }
        case tc.ALL : case tc.SOME : {
            // |~(Ax)A| = Ex|~A|
            var sub = this[1][2].negate().normalize();
            var res = [(this[1][0] == tc.ALL) ? tc.SOME : tc.ALL, this[1][1], sub];
            res.__complexity = sub.__complexity;
            return res;
        }
        case tc.NOT : {
            // |~~A| = |A|
            return this[1][1].normalize();
        }
        // negated atom is treated with atoms in default case below
        }
    }
    default : {
        this.__complexity = 1;
        return this;
    }
    }
}

Array.prototype.getFreeVariables = function() {
    // returns all free variables in the formula (no duplicates)
    var result = [];
    this.__boundVars = [];
    var fla, flas = [this];
    while ((fla = flas.shift())) {
        if (fla.length == 3) { // complex (except negated)
            if (!fla[1].isArray) { // quantified
                fla[2].__boundVars = fla.__boundVars;
                fla[2].__boundVars.push(fla[1]);
                flas.push(fla[2]);
            }
            else {
                flas.push(fla[1]);
                flas.push(fla[2]);
            }
        }
        else if (fla[0] == tc.NOT) { // negated
            flas.push(fla[1]);
        }
        else { // atomic
            var terms, termss = [fla[1]];
            while ((terms = termss.shift())) {
                for (var i=0; i<terms.length; i++) {
                    if (terms[i].isArray) termss.push(terms[i]);
                    else if (term % 3 == 0 &&
                             !fla.__boundVars.includes(terms[i]) &&
                             !result.includes(terms[i])) {
                        result.push(terms[i]);
                    }
                }
            }
        }
        delete fla.__boundVars;
    }
    return result;
}

Array.prototype.getBoundVariables = function() {
    // returns all bound variables in the formula (no duplicates)
    var result = [];
    var fla, flas = [this];
    while ((fla = flas.shift())) {
        if (fla.length == 3) {
            if (!fla[1].isArray) { // quantified fla
                if (!result.includes(fla[1])) result.push(fla[1]);
                flas.push(fla[2]);
                continue;
            }
            flas.push(fla[1]);
            flas.push(fla[2]);
            continue;
        }
        if (fla[0] == tc.NOT) flas.push(fla[1]);
    }
    return result;
}


Array.prototype.getConstants = function(withArity) { 
    // returns a list of all constants and function symbols in the
    // formula. If <withArity> is set and true, the returned elements
    // are objects with properties 'constant' and 'arity'.
    var result = [], resultWithArity = [];
    var fla, flas = [this];
    while ((fla = flas.shift())) {
        if (fla.length == 3) { // complex (except negated)
            if (!fla[1].isArray) { // quantified
                flas.push(fla[2]);
                continue;
            }
            flas.push(fla[1]);
            flas.push(fla[2]);
            continue;
        }
        if (fla[0] == tc.NOT) { // negated
            flas.push(fla[1]);
            continue;
        }
        var term, terms = fla[1].copyDeep();
        while ((term = terms.shift())) {
            if (term.isArray) {
                for (var i=1; i<term.length; i++) terms.push(term[i]);
                if (result.includes(term[0])) continue;
                result.push(term[0]);
                if (withArity) {
                    resultWithArity.push({ constant : term[0], arity : term.length-1 });
                }
            }
            else if (term % 3 == 2 && !result.includes(term)) {
                result.push(term);
                if (withArity) {
                    resultWithArity.push({ constant : term, arity : 0 });
                }
            }
        }
    }
    return withArity ? resultWithArity : result;
}

Array.prototype.getPredicates = function(withArity) {
    // returns a list of all predicates in the formula. If <withArity>
    // is set and true, the returned elements are objects with
    // properties 'predicate' and 'arity'.
    var result = [], resultWithArity = [];
    var fla, flas = [this];
    while ((fla = flas.shift())) {
        if (fla.length == 3) {
            if (!fla[1].isArray) { // quantified fla
                flas.push(fla[2]);
                continue;
            }
            flas.push(fla[1]);
            flas.push(fla[2]);
            continue;
        }
        if (fla[0] == tc.NOT) {
            flas.push(fla[1]);
            continue;
        }
        if (!result.includes(fla[0])) {
            result.push(fla[0]);
            if (withArity) {
                resultWithArity.push({ predicate : fla[0], arity : fla[1].length });
            }
        }
    }
    return withArity ? resultWithArity : result;
}

Array.prototype.equals = function(formula) {
    // returns true iff two formulas are syntactically identical
    if (this.length != formula.length) return false;
    for (var i=0; i<this.length; i++) {
        if (this[i].isArray) {
            if (!formula[i].isArray) return false;
            if (!this[i].equals(formula[i])) return false;
        }
        else if (this[i] != formula[i]) return false;
    }
    return true;
}
