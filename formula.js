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
    // removes the first element that strictly equals <element>
    var index = this.indexOf(element);
    if (index > -1) this.splice(index, 1);
}

Array.prototype.insert = function(element, index) {
    // inserts <element> at the given position, shifting the existing
    // ones further back
    return this.splice(index, 0, element);
}

Array.prototype.randomElement = function() {
    return this[Math.floor(Math.random() * this.length)]
}

Array.getArrayOfZeroes = function(length) {
    // https://jsperf.com/zero-filled-array-creation/17
    for (var i = 0, a = new Array(length); i < length;) a[i++] = 0;
    return a;
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

Array.prototype.equals = function(arr2) {
    // return true iff two (possibly nested) arrays are equal (==) at all
    // positions
    if (this.length != arr2.length) return false;
    for (var i=0; i<this.length; i++) {
        if (this[i].isArray) {
            if (!arr2[i].isArray) return false;
            if (!this[i].equals(arr2[i])) return false;
        }
        else if (this[i] != arr2[i]) return false;
    }
    return true;
}


// Formula objects should be treated as immutable.

function Formula() {
}

Formula.prototype.toString = function() {
    return this.string;
}

Formula.prototype.equals = function(fla) {
    return this.string == fla.string;
}

Formula.prototype.negate = function() {
    return new NegatedFormula(this, this.signature);
}

Formula.prototype.unify = function(formula) {
    // checks whether this formula can be unified with the argument formula.
    // Returns a (minimally) unifying substitution (that, if applied to both
    // formulas, yields the same formula) if one exists, otherwise false.
    // A substitution is simply an array of terms, which is interpreted as
    // arr[1] -> arr[2], arr[3] -> arr[4], ... (arr[1], arr[3], etc.
    // are variables). Warning: Don't confuse an empty unifier [] with false!
    //
    // The following algorithm is losely based on the one described in S.
    // Hölldobler, Logik und Logikprogrammierung, Synchron Verlag,
    // Heidelberg 2001, §4.5.
    //
    // Note that this only works for literals.  For quantified
    // formulas one would have to care about capturing by quantified
    // variables, which would complicate things a little.
    if (this.type != 'literal') return false;
    if (this.sub && !formula.sub) return false;
    if (this.sub) return this.sub.unify(formula.sub);
    if (this.predicate != formula.predicate) return false;
    if (this.terms.length != formula.terms.length) return false;
    // So we have two atomic formulas of the same arity. Now we walk through all
    // the pairs of terms.
    var unifier = [];
    var terms1 = this.terms.copyDeep(); // xxx wouldn't copy() suffice?
    var terms2 = formula.terms.copyDeep();
    var t1, t2;
    while (t1 = terms1.shift(), t2 = terms2.shift()) {
        log('unify terms? '+t1+' <=> '+t2);
        if (t1 == t2) {
            // terms are equal: nothing to do.
            continue;
        }
        if (t1.isArray && t2.isArray) {
            // both terms are functional: unification fails if function symbols
            // differ; otherwise add all the argument pairs to the terms that
            // must be unified.
            if (t1[0] != t2[0]) return false;
            for (var i=1; i<t1.length; i++) {
                terms1.push(t1[i]);
                terms2.push(t2[i]);
            }
            continue;
        }
        if (t1[0] != 'ξ' && t2[0] != 'ξ') {
            // neither term is variable: unification failed
            return false;
        }
        if (t1[0] != 'ξ') {
            // only second term is a variable: exchange it with first term, so
            // that in what follows the first term is always a variable.
            var temp = t1; t1 = t2; t2 = temp; 
        }
        if (t2.isArray) {
            // t2 is a function term: unification fails if it contains t1 among
            // its arguments (or arguments of its ... arguments).
            var terms, termss = [t2];
            while (terms = termss.shift()) {
                // log(terms);
                for (var i=0; i<terms.length; i++) {
                    if (terms[i].isArray) termss.push(terms[i]);
                    else if (terms[i] == t1) return false;
                }
            }
        }
        // now we unify the variable t1 with the term t2: substitute t2
        // for t1 everywhere in the unifier array and in the remaining
        // terms1 and terms2, and add t1/t2 to the unifier array.
        log('yes: unify');
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

Formula.prototype.normalize = function() {
    // returns an equivalent formula in negation normal form, in which left
    // subformulas are generally less complex than right subformulas (complexity
    // here means number of disjunctions). This helps when constructing proofs:
    // we can always focus on the leftmost open branch in a tree. xxx todo
    // implement, and see if it helps at all.
    var op = this.operator || this.quantifier;
    if (!op) return this;
    switch (op) {
    case '∧' : case '∨' : {
        // |A&B| = |A|&|B|
        // |AvB| = |A|v|B|
        return new BinaryFormula(op, this.sub1.normalize(), this.sub2.normalize(),
                                 this.signature);
    }
    case '→' : {
        // |A->B| = |~A|v|B|
        return new BinaryFormula('∨', this.sub1.negate().normalize(), this.sub2.normalize(),
                                 this.signature);
    }
    case '↔' : {
        // |A<->B| = |A&B|v|~A&~B|
        var sub1 = new BinaryFormula('∧', this.sub1, this.sub2, this.signature);
        var sub2 = new BinaryFormula('∧', this.sub1.negate(), this.sub2.negate(), this.signature);
        return new BinaryFormula('∨', sub1.normalize(), sub2.normalize());
    }
    case '∀' : case '∃' : {
        // |(Ax)A| = Ax|A|
        return new QuantifiedFormula(op, this.variable, this.matrix.normalize(), this.signature);
    }
    case '□' : case '◇' : {
        // |[]A| = []|A|
        return new ModalFormula(op, this.sub.normalize(), this.signature);
    }
    case '¬' : {
        var op2 = this.sub.operator || this.sub.quantifier;
        if (!op2) return this;
        switch (op2) {
        case '∧' : case '∨' : {
            // |~(A&B)| = |~A|v|~B|
            // |~(AvB)| = |~A|&|~B|
            var sub1 = this.sub.sub1.negate().normalize();
            var sub2 = this.sub.sub2.negate().normalize();
            return new BinaryFormula(op2=='∧' ? '∨' : '∧', sub1, sub2, this.signature);
        }
        case '→' : {
            // |~(A->B)| = |A|&|~B|
            var sub1 = this.sub.sub1.normalize();
            var sub2 = this.sub.sub2.negate().normalize();
            return new BinaryFormula('∧', sub1, sub2, this.signature);
        }
        case '↔' : {
            // |~(A<->B)| = |A&~B|v|~A&B|
            var sub1 = new BinaryFormula('∧', this.sub.sub1, this.sub.sub2.negate(), this.signature);
            var sub2 = new BinaryFormula('∧', this.sub.sub1.negate(), this.sub.sub2, this.signature);
            return new BinaryFormula('∨', sub1.normalize(), sub2.normalize(), this.signature);
        }
        case '∀' : case '∃' : {
            // |~(Ax)A| = Ex|~A|
            var sub = this.sub.matrix.negate().normalize();
            return new QuantifiedFormula(op2=='∀' ? '∃' : '∀', this.sub.variable, sub, this.signature);
        }
        case '□' : case '◇' : {
            // |~[]A| = []|~A|
            var sub = this.sub.sub.negate().normalize();
            return new ModalFormula(op2=='□' ? '◇' : '□', sub, this.signature);
        }
        case '¬' : {
            // |~~A| = |A|
            return this.sub.sub.normalize();
        }
        }
    }
    }
}

Formula.prototype.translateToModal = function(worldVariable) {
    // return translation of modal formula into first-order formula with
    // explicit world variables
    log("translating modal formula");
    if (!worldVariable) {
        // xxx this changes original signature:
        for (var i=0; i<this.signature.symbols.length; i++) {
            var sym = this.signature.symbols[i];
            if (this.signature.expressionType[sym].indexOf('predicate') > -1) {
                this.signature.arities[sym] += 1;
            }
        }
        this.signature.arities['ℜ'] = 2;
        worldVariable = '⟒0';
        this.signature.registerExpression(worldVariable, 'constant', 0);
    }
    if (this.terms) { // atomic; add world variable to argument list
        var nterms = this.terms.copyDeep();
        nterms.push(worldVariable); // don't need to add world parameters to function terms; think of 0-ary terms
        return new AtomicFormula(this.predicate, nterms, this.signature);
    }
    if (this.quantifier) {
        var nmatrix = this.matrix.translateToModal(worldVariable);
        return new QuantifiedFormula(this.quantifier, this.variable, nmatrix, this.signature);
        // xxx assumes constant domains
    }
    if (this.sub1) {
        var nsub1 = this.sub1.translateToModal(worldVariable);
        var nsub2 = this.sub2.translateToModal(worldVariable);
        return new BinaryFormula(this.operator, nsub1, nsub2, this.signature);
    }
    if (this.operator == '¬') {
        var nsub = this.sub.translateToModal(worldVariable);
        return new NegatedFormula(nsub, this.signature);
    }
    if (this.operator == '□') {
        var newWorldVariable = '⟒'+(worldVariable.substr(1)*1+1);
        this.signature.registerExpression(newWorldVariable, 'variable', 0);
        var wRv = new AtomicFormula('ℜ', [worldVariable, newWorldVariable], this.signature)
        var nsub = this.sub.translateToModal(newWorldVariable);
        return new QuantifiedFormula('∀', newWorldVariable, new BinaryFormula('→', wRv, nsub), this.signature)
    }
    if (this.operator == '◇') {
        var newWorldVariable = 'w'+(worldVariable.substr(1)*1+1);
        this.signature.registerExpression(newWorldVariable, 'variable', 0);
        var wRv = new AtomicFormula('ℜ', [worldVariable, newWorldVariable], this.signature)
        var nsub = this.sub.translateToModal(newWorldVariable);
        return new QuantifiedFormula('∀', newWorldVariable, new BinaryFormula('∧', wRv, nsub), this.signature)
    }
}

Formula.prototype.isModal = function() {
    var fla, flas = [this];
    while ((fla = flas.shift())) {
        if (fla.operator == '□' || fla.operator == '◇') return true;
        if (fla.matrix) {
            flas.push(fla.matrix);
        }
        else if (fla.sub) {
            flas.push(fla.sub);
        }
        else if (fla.sub1) {
            flas.push(fla.sub1);
            flas.push(fla.sub2);
        }
    }
    return false;
}

// Formula.prototype.getBoundVariables = function() {
//     // returns all bound variables in the formula (no duplicates)
//     var result = [];
//     var fla, flas = [this];
//     while ((fla = flas.shift())) {
//         if (fla.variable) {
//             if (!result.includes(fla.variable)) result.push(fla.variable);
//             flas.push(fla.matrix);
//         }
//         else if (fla.sub) {
//             flas.push(fla.sub);
//         }
//         else if (fla.sub1) {
//             flas.push(fla.sub1);
//             flas.push(fla.sub2);
//         }
//     }
//     return result;
// }

// Formula.prototype.getConstants = function(withArity) { 
//     // returns a list of all constants and function symbols in the (normalized)
//     // formula. If <withArity> is set and true, the returned elements are
//     // objects with properties 'constant' and 'arity'.
//     var result = [], resultWithArity = [];
//     var boundVars = []; // xxx check: what if a variable occurs both free and bound?
//     var fla, flas = [this];
//     while ((fla = flas.shift())) {
//         if (fla.matrix) {
//             flas.push(fla.matrix);
//             boundVars.push(fla.variable);
//             continue;
//         }
//         if (fla.sub1) {
//             flas.push(fla.sub1);
//             flas.push(fla.sub2);
//             continue;
//         }
//         if (fla.sub) {
//             flas.push(fla.sub);
//             continue;
//         }
//         var term, terms = fla.terms.copyDeep();
//         while ((term = terms.shift())) {
//             if (term.isArray) {
//                 for (var i=1; i<term.length; i++) terms.push(term[i]);
//                 if (result.includes(term[0])) continue;
//                 result.push(term[0]);
//                 if (withArity) {
//                     resultWithArity.push({ constant : term[0], arity : term.length-1 });
//                 }
//             }
//             else if (!result.includes(term) && !boundVars.includes(term)) {
//                 result.push(term);
//                 if (withArity) {
//                     resultWithArity.push({ constant : term, arity : 0 });
//                 }
//             }
//         }
//     }
//     return withArity ? resultWithArity : result;
// }

// Formula.prototype.getPredicates = function(withArity) {
//     // returns a list of all predicates in the formula. If <withArity>
//     // is set and true, the returned elements are objects with
//     // properties 'predicate' and 'arity'.
//     var result = [], resultWithArity = [];
//     var fla, flas = [this];
//     while ((fla = flas.shift())) {
//         if (fla.matrix) {
//             flas.push(fla.matrix);
//             continue;
//         }
//         if (fla.sub1) {
//             flas.push(fla.sub1);
//             flas.push(fla.sub2);
//             continue;
//         }
//         if (fla.sub) {
//             flas.push(fla.sub);
//             continue;
//         }
//         if (!result.includes(fla.predicate)) {
//             result.push(fla.predicate);
//             if (withArity) {
//                 resultWithArity.push({ predicate : fla.predicate, arity : fla.terms.length });
//             }
//         }
//     }
//     return withArity ? resultWithArity : result;
// }

Formula.prototype.alpha = function(n) {
    // return first/second formula for sentree alpha expansion
    if (this.operator == '∧') {
        return n == 1 ? this.sub1 : this.sub2;
    }
    // formula is negated
    if (this.sub.operator == '∨') {
        return n == 1 ? this.sub.sub1.negate() : this.sub.sub2.negate();
    }
    if (this.sub.operator == '→') {
        return n == 1 ? this.sub.sub1 : this.sub.sub2.negate();
    }
}

Formula.prototype.beta = function(n) {
    // return first/second formula for sentree alpha expansion
    if (this.operator == '∨') {
        return n == 1 ? this.sub1 : this.sub2;
    }
    if (this.operator == '→') {
        return n == 1 ? this.sub1.negate() : this.sub2;
    }
    // We treat A <-> B as expanding to (A&B) | (~A&~B), and ~(A<->B) to
    // (A&~B) | (~A&B); these intermediate notes will be removed before
    // displaying trees.
    if (this.operator == '↔') {
        return n == 1 ? new BinaryFormula('∧', this.sub1, this.sub2) :
            new BinaryFormula('∧', this.sub1.negate(), this.sub2.negate())
    }
    // formula is negated
    if (this.sub.operator == '∧') {
        return n == 1 ? this.sub.sub1.negate() : this.sub.sub2.negate();
    }
    if (this.sub.operator == '↔') {
        return n == 1 ? new BinaryFormula('∧', this.sub.sub1, this.sub.sub2.negate()) :
            new BinaryFormula('∧', this.sub.sub1.negate(), this.sub.sub2)
    }
}

function AtomicFormula(predicate, terms, signature) {
    this.type = 'literal';
    this.predicate = predicate;
    this.terms = terms; // a,b,f(a,g(c),d) => a,b,[f,a,[g,c],d]
    this.string = this.predicate + AtomicFormula.terms2string(this.terms);
    this.signature = signature;
    this.predicates = [predicate];
    this.constants = [];
    this.variables = [];
    // classify atomic terms:
    var list = terms;
    for (var i=0; i<list.length; i++) {
        if (list[i].isArray) list = list.concat(list[i]);
        else if (this.signature.isVariable[list[i]]) this.variables.push(list[i]);
        else this.constants.push(list[i]);
    }
    // log(this.constants);
}

AtomicFormula.terms2string = function(list) {
    var res = '';
    for (var i=0; i<list.length; i++) {
        if (list[i].isArray) {
            var sublist = list[i].copy();
            var funcsym = sublist.shift();
            res += funcsym+'('+AtomicFormula.terms2string(sublist)+')';
        }
        else res += list[i];
    }
    return res;
}

AtomicFormula.prototype = Object.create(Formula.prototype);

AtomicFormula.prototype.substitute = function(origTerm, newTerm, shallow) {
    // return new formula with all free occurrences of <origTerm> replaced
    // by <newTerm>. If <shallow>, don't replace terms in function arguments
    var newTerms = [];
    for (var i=0; i<this.terms.length; i++) {
        newTerms.push(AtomicFormula.substituteInTerm(this.terms[i], origTerm, newTerm, shallow));
    }
    if (!this.terms.equals(newTerms)) {
        return new AtomicFormula(this.predicate, newTerms, this.signature);
    }
    else return this;
}
AtomicFormula.substituteInTerm = function(term, origTerm, newTerm, shallow) {
    // xxx this could be optimized (it's also used in prover)
    if (term.isArray && !shallow) {
        var nTerm = [];
        for (var i=0; i<term.length; i++) {
            nTerm.push(AtomicFormula.substituteInTerm(term[i], origTerm, newTerm));
        }
        return nTerm;
    }
    if (term == origTerm) return newTerm;
    return term;
}

function QuantifiedFormula(quantifier, variable, matrix, signature) {
    this.quantifier = quantifier;
    this.variable = variable;
    this.matrix = matrix;
    this.type = quantifier == '∀' ? 'gamma' : 'delta';
    this.string = quantifier + variable + matrix;
    this.signature = signature;
    this.predicates = matrix.predicates;
    this.constants = matrix.constants;
    this.variables = matrix.variables; // if current variable is vacuous we
                                       // don't care if it's listed under
                                       // variables
}

QuantifiedFormula.prototype = Object.create(Formula.prototype);

QuantifiedFormula.prototype.substitute = function(origTerm, newTerm, shallow) {
    // return new formula with all free occurrences of <origTerm> replaced
    // by <newTerm>. If <shallow>, don't replace terms in function arguments
    if (this.variable == origTerm) return this;
    var nmatrix = this.matrix.substitute(origTerm, newTerm, shallow);
    if (nmatrix == this.matrix) return this;
    return new QuantifiedFormula(this.quantifier, this.variable, nmatrix, this.signature);
}

function BinaryFormula(operator, sub1, sub2, signature) {
    this.operator = operator;
    this.sub1 = sub1;
    this.sub2 = sub2;
    this.type = operator == '∧' ? 'alpha' : 'beta';
    this.string = '(' + this.sub1 + this.operator + this.sub2 + ')';
    this.signature = signature;
    this.predicates = this.sub1.predicates.copy();
    // xxx optimize the following by defining Array.merge?
    for (var i=0; i<this.sub2.predicates.length; i++) {
        var pred = this.sub2.predicates[i];
        if (!this.predicates.includes(pred)) {
            this.predicates.push(pred);
        }
    }
    this.constants = this.sub1.constants.copy();
    for (var i=0; i<this.sub2.constants.length; i++) {
        var cons = this.sub2.constants[i];
        if (!this.constants.includes(cons)) {
            this.constants.push(cons);
        }
    }
    this.variables = this.sub1.variables.copy();
    for (var i=0; i<this.sub2.variables.length; i++) {
        var vari = this.sub2.variables[i];
        if (!this.variables.includes(vari)) {
            this.variables.push(vari);
        }
    }
}

BinaryFormula.prototype = Object.create(Formula.prototype);

BinaryFormula.prototype.substitute = function(origTerm, newTerm, shallow) {
    // return new formula with all free occurrences of <origTerm> replaced
    // by <newTerm>. If <shallow>, don't replace terms in function arguments
    var nsub1 = this.sub1.substitute(origTerm, newTerm, shallow);
    var nsub2 = this.sub2.substitute(origTerm, newTerm, shallow);
    if (this.sub1 == nsub1 && this.sub2 == nsub2) return this;
    return new BinaryFormula(this.operator, nsub1, nsub2, this.signature);
}

function ModalFormula(operator, sub, signature) {
    this.operator = operator;
    this.sub = sub;
    this.type = operator == '□' ? 'boxy' : 'diamondy';
    this.string = this.operator + this.sub;
    this.signature = signature;
    this.predicates = this.sub.predicates;
    this.constants = this.sub.constants;
    this.variables = this.sub.variables;
    this.is_modal = true;
}

ModalFormula.prototype = Object.create(Formula.prototype);

ModalFormula.prototype.substitute = function(origTerm, newTerm, shallow) {
    // return new formula with all free occurrences of <origTerm> replaced
    // by <newTerm>. If <shallow>, don't replace terms in function arguments
    var nsub = this.sub.substitute(origTerm, newTerm, shallow);
    if (this.sub == nsub) return this;
    return new ModalFormula(this.operator, nsub, this.signature);
}

function NegatedFormula(sub, signature) {
    this.operator = '¬';
    this.sub = sub;
    this.type = NegatedFormula.computeType(sub);
    this.string = '¬' + this.sub;
    this.signature = signature;
    this.predicates = this.sub.predicates;
    this.constants = this.sub.constants;
    this.variables = this.sub.variables;
}

NegatedFormula.computeType = function(sub) {
    if (sub.operator == '¬') return 'doublenegation';
    switch (sub.type) {
    case 'literal': { return 'literal'; }
    case 'alpha': { return 'beta'; }
    case 'beta': { return sub.operator == '↔' ? 'beta' : 'alpha'; }
    case 'gamma': { return 'delta'; }
    case 'delta': { return 'gamma'; }
    case 'boxy': { return 'diamondy'; }
    case 'diamondy': { return 'boxy'; }
    }
}

NegatedFormula.prototype = Object.create(Formula.prototype);

NegatedFormula.prototype.substitute = function(origTerm, newTerm, shallow) {
    // return new formula with all free occurrences of <origTerm> replaced
    // by <newTerm>. If <shallow>, don't replace terms in function arguments
    var nsub = this.sub.substitute(origTerm, newTerm, shallow);
    if (this.sub == nsub) return this;
    return new NegatedFormula(nsub, this.signature);
}


function Parser() {
    // store signature info so that we can parse multiple formulas and check if
    // they make sense together (e.g. matching arities for same predicate
    this.symbols = [];
    this.expressionType = {};
    this.isVariable = {};
    this.arities = {};
}

Parser.prototype.registerExpression = function(ex, exType, arity) {
    if (!this.expressionType[ex]) this.symbols.push(ex);
    else if (this.expressionType[ex] != exType) {
        throw "don't use '"+ex+"' as both "+this.expressionType[ex]+" and "+exType;
    }
    this.expressionType[ex] = exType;
    this.arities[ex] = arity;
    log('registering '+exType+' '+ex);
    if (exType == 'variable') this.registerVariable(ex);
}

Parser.prototype.registerVariable = function(ex) {
    this.isVariable[ex] = true;
}

Parser.prototype.parseFormula = function(str) {
    // return Formula for string
    var boundVars = arguments[1] ? arguments[1].slice() : [];
    log("parsing '"+str+"' (boundVars "+boundVars+")");
    str = str.trim();

    var reTest = /∧|∨|→|↔/.test(str);
    if (reTest) {
        // str contains a connective. Main operator might nevertheless be a
        // quantifier or negation etc. We replace every substring in parens by
        // "%0", "%1", etc.:
        var subStringsInParens = []; 
        var parenDepth = 0;
        var storingAtIndex = -1;
        var nstr = "";
        for (var i=0; i<str.length; i++) {
            if (str.charAt(i) == "(") {
                parenDepth++;
                if (parenDepth == 1) {
                    storingAtIndex = subStringsInParens.length;
                    subStringsInParens[storingAtIndex] = "";
                    nstr += "%" + storingAtIndex;
                }
            }
            if (storingAtIndex == -1) nstr += str.charAt(i);
            else subStringsInParens[storingAtIndex] += str.charAt(i);
            if (str.charAt(i) == ")") {
                parenDepth--;
                if (parenDepth == 0) storingAtIndex = -1;
            }
        }
        log("   nstr = '"+nstr+"'; ");
         
        // done. Now let's see if there is still a connective in the
        // modified string (in decreasing order of precedence):
        var reTest = nstr.match(/↔/) || nstr.match(/→/)  || nstr.match(/∨/) || nstr.match(/∧/);
        if (reTest) { 
            // yes. The matched connective is the main operator
            log("   string is complex; ");
            var op = reTest[0];
            log("   main connective: "+op+"; ");
            nstr = nstr.replace(op, "%split");
            // restore removed substrings:
            for (var i=0; i<subStringsInParens.length; i++) {
                nstr = nstr.replace("%"+i, subStringsInParens[i]);
            }
            var subFormulas = nstr.split("%split");
            if (!subFormulas[1]) {
                throw "argument missing for operator "+op+" in "+str;
            }
            log("   subformulas: "+subFormulas[0]+", "+subFormulas[1]+"; ");
            var sub1 = this.parseFormula(subFormulas[0], boundVars);
            var sub2 = this.parseFormula(subFormulas[1], boundVars);
            return new BinaryFormula(op, sub1, sub2, this);
        }
    }
    
    var reTest = str.match(/^¬|□|◇/);
    if (reTest) {
        log("   string is negated or modal; ");
        var op = reTest[0];
        var sub = this.parseFormula(str.substr(1), boundVars);
        if (op == '¬') return new NegatedFormula(sub, this);
        else return new ModalFormula(op, sub, this);
    }

    // if we're here the formula should be quantified or atomic
    reTest = /(∀|∃)([^\d\(\),%]\d*)/.exec(str);
    if (reTest && reTest.index == 0) {
        // quantified formula
        log("   string is quantified (quantifier = '"+reTest[1]+"'); ");
        var quantifier = reTest[1];
        var variable = reTest[2];
        this.registerExpression(variable, 'variable');
        if (!str.substr(reTest[0].length)) {
            throw "There is nothing in the scope of "+str;
        }
        boundVars.push(variable);
        var sub = this.parseFormula(str.substr(reTest[0].length), boundVars);
        return new QuantifiedFormula(quantifier, variable, sub, this);
    }

    // formula should be atomic
    reTest = /[^\d\(\),%]\d*/.exec(str);
    if (reTest && reTest.index == 0) {
        // atomic
        log("   string is atomic (predicate = '"+reTest[0]+"'); ");
        var predicate = reTest[0];
        var termstr = str.substr(reTest.length); // empty for propositional constants
        var terms = this.parseTerms(termstr, boundVars) || [];
        var predicateType = terms ? terms.length+"-ary predicate" : "proposition letter (0-ary predicate)";
        this.registerExpression(predicate, predicateType, terms.length);
        return new AtomicFormula(predicate, terms, this);
    }

    // if the entire formula was enclosed in parens we end up here
    log("   string could not be identified as anything;");
    if (str.match(/^\((.*)\)$/)) {
        log("   trying again without outer parens;");
        return this.parseFormula(str.replace(/^\((.*)\)$/, "$1"), boundVars);
    }

    throw "Parse Error.\n'" + str + "' is not a well-formed formula.";
}        

Parser.prototype.parseTerms = function(str, boundVars) {
    // parses a sequence of terms and returns the sequence in internal format,
    // as nested array
    log("parsing terms: "+str+" (boundVars "+boundVars+")");
    if (!str) return [];
    var result = [];
    str = str.replace(/^\((.+)\)$/, "$1"); // remove surrounding parens
    do {
        var reTest = /[^\(\),%]\d*/.exec(str);
        if (!reTest || reTest.index != 0) {
            throw "I expected a (sequence of) term(s) instead of '" + str + "'";
        }
        var nextTerm = reTest[0];
        str = str.substr(reTest[0].length);
        if (str.indexOf("(") == 0) {
            // term was a function symbol. Find and parse the arguments:
            // (I can't use a simple RegExp such as /^\(([^\)]+)\)/ here because
            // I have to keep track of *how many* parens open and close,
            // cf. Rf(a)g(b) vs. Rf(a,g(b))
            var args = "", openParens = 0, spos = 0;
            do {
                args += str.charAt(spos);
                if (str.charAt(spos) == "(") openParens++;
                else if (str.charAt(spos) == ")") openParens--;
                spos++;
            } while (openParens && spos < str.length);
            log("Arguments: "+args);
            nextTerm = [nextTerm].concat(this.parseTerms(args, boundVars));
            var arity = (nextTerm.length - 1);
            this.registerExpression(reTest[0], arity+"-ary function symbol", arity);
            str = str.substr(args.length);
        }
        else if (!boundVars.includes(nextTerm)) {
            this.registerExpression(nextTerm, 'individual constant', 0);
        }
        result.push(nextTerm);
        if (str.indexOf(",") == 0) str = str.substr(1);
    } while (str.length > 0);
    return result;
}

