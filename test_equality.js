
tests = {

    subterms: function() {
        assertEqual(subterms('a').toString(), '[a]');
        assertEqual(subterms(['f','b','b']).toString(), '[[f,b,b],b]');
        assertEqual(subterms(['g',['f',['f','b']]]).toString(), '[[g,[f,[f,b]]],[f,[f,b]],[f,b],b]');
        assertEqual(subterms(['g','ξ1','ξ2']).toString(), '[[g,ξ1,ξ2]]');
    },

    replaceSubterm: function() {
        assertEqual(replaceSubterm('a', 'a', 'b').toString(), '[b]');
        assertEqual(replaceSubterm('a', 'b', 'a').toString(), '[]');
        assertEqual(replaceSubterm(['f','a','a'], 'a', 'b').toString(), '[[f,b,a],[f,a,b]]');
        assertEqual(replaceSubterm(['f','a'], 'a', ['h','x']).toString(), '[[f,[h,x]]]');
        assertEqual(replaceSubterm(['f',['g','a'],['g',['g','a']]], ['g','a'], ['h','x']).toString(),
                    '[[f,[h,x],[g,[g,a]]],[f,[g,a],[g,[h,x]]]]');
    },

    solvedFormAddEqual: function() {
        var sf = new SolvedForm();
        assertEqual(sf.addEqual('b','b')[0], sf);
        assertEqual(sf.addEqual('a','b').length, 0);
        assertEqual(sf.addEqual('ξ1','b').length, 1);
        assertEqual(sf.addEqual(['f','ξ1'],'ξ1').length, 0);
    },
    
    solvedFormAddGreater: function() {
        var sf = new SolvedForm();
        assertEqual(sf.addGreater('b','b').length, 0);
        assertEqual(sf.addGreater('b','a')[0].inequalities.length, 0);
        assertEqual(sf.addGreater('ξ1','b')[0].inequalities.length, 1);
        assertEqual(sf.addGreater(['f','ξ1'],'ξ1').length, 1);
        assertEqual(sf.addGreater('ξ1',['f','ξ1']).length, 0);
    },

    eqProbLrbs: function() {
        // [b=d,c=d] ⊢ [b]=[c]
        var sols = solveEqualityProblem(['b'], ['c'], [
            new AtomicFormula('=', ['b','d']),
            new AtomicFormula('=', ['c','d'])
        ]);
        assertEqual(sols.length, 1);
    },

    eqProbBeckert98ex1: function() {
        var sols = solveEqualityProblem(['a'], ['c'], [
            new AtomicFormula('=', ['a','ξ1']),
            new AtomicFormula('=', ['b','c'])
        ]);
        assertEqual(sols.length, 2);
        assert(sols.includes('[ξ1,b]'));
        assert(sols.includes('[ξ1,c]'));
    },

    eqProbBeckert98ex2: function() {
        var sols = solveEqualityProblem([['g', ['g', ['g','ξ1']]]], ['ξ1'], [
            new AtomicFormula('=', [['f','a'],'a']),
            new AtomicFormula('=', [['g',['g','ξ1']],['f','a']])
        ]);
        assertEqual(sols.length, 1);
        assertEqual(sols[0], '[ξ1,[g,[f,a]]]');
    }

}

function solveEqualityProblem(terms1, terms2, equationFormulas) {
    // return list of all substitutions (as strings) that are found to solve the
    // given problem
    var ep = new EqualityProblem();
    for (var i=0; i<equationFormulas.length; i++) {
        ep.equations.push(new Node(equationFormulas[i]));
    }
    ep.terms1 = terms1;
    ep.terms2 = terms2;
    var eps = [ep];
    var solutions = [];
    while ((ep = eps.shift())) {
        var res = ep.nextStep();
        for (var i=0; i<res.length; i++) {
            if (!res[i].nextStep) solutions.push(res[i]);
            else eps.unshift(res[i]);
        }
    }
    var solstrs = solutions.map(function(ep) { return ep.getSubstitution().toString() });
    return solstrs.removeDuplicates();
}
