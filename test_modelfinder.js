
tests = {

    setup: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('p'), parser.parseFormula('Ff(a,a)')], parser);
        assert(mf.predicates.equals(['p','F']));
        assertEqual(mf.constants.toString(), '[a]');
        assertEqual(mf.funcSymbols.toString(), '[f]');
        assertEqual(mf.model.domain.length, 1);
        assertEqual(mf.model.worlds.length, 0);
    },

    skolemize: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('p')], parser);
        var f = parser.parseFormula('∀x∃y(Fx∧∀zHxyz)');
        f = f.nnf();
        var sk = mf.skolemize(f);
        assertEqual(sk.toString(), '∀x(Fx ∧ ∀zHxf(x)z)');
    },
    
    skolemize2: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('p')], parser);
        var f = parser.parseFormula('∀x∃y∃zHxyz ∨ ∃v∀wGvw');
        f = f.nnf();
        var sk = mf.skolemize(f);
        assertEqual(sk.string, '(∀xHxf(x)g(x) ∨ ∀wGaw)');
    },

    cnf_basic: function() {
        var parser = new Parser();
        var m = new ModelFinder([parser.parseFormula('p')], parser);
        var cnf = m.cnf(parser.parseFormula('p'));
        assertEqual(cnf.toString(), '[[p]]');
        var cnf = m.cnf(parser.parseFormula('¬p'));
        assertEqual(cnf.toString(), '[[¬p]]');
        var cnf = m.cnf(parser.parseFormula('p∨q'));
        assertEqual(cnf.toString(), '[[p,q]]');
        var cnf = m.cnf(parser.parseFormula('p∧q'));
        assertEqual(cnf.toString(), '[[p],[q]]');
        var cnf = m.cnf(parser.parseFormula('p→q'));
        assertEqual(cnf.toString(), '[[q,¬p]]');
        var cnf = m.cnf(parser.parseFormula('p↔q'));
        assertEqual(cnf.toString(), '[[q,¬p],[p,¬q]]');
        var cnf = m.cnf(parser.parseFormula('¬(p∨q)'));
        assertEqual(cnf.toString(), '[[¬p],[¬q]]');
        var cnf = m.cnf(parser.parseFormula('¬(p∧q)'));
        assertEqual(cnf.toString(), '[[¬p,¬q]]');
        var cnf = m.cnf(parser.parseFormula('¬(p→q)'));
        assertEqual(cnf.toString(), '[[p],[¬q]]');
        var cnf = m.cnf(parser.parseFormula('¬(p↔q)'));
        assertEqual(cnf.toString(), '[[p,q],[¬p,¬q]]');
        var cnf = m.cnf(parser.parseFormula('¬¬p'));
        assertEqual(cnf.toString(), '[[p]]');
    },

    cnf_sort_and_simplify: function() {
        var parser = new Parser();
        var m = new ModelFinder([parser.parseFormula('p')], parser);
        var cnf = m.cnf(parser.parseFormula('(p∨p)'));
        assertEqual(cnf.toString(), '[[p]]');
        var cnf = m.cnf(parser.parseFormula('(p∨q)∧(p∨q)'));
        assertEqual(cnf.toString(), '[[p,q]]');
        var cnf = m.cnf(parser.parseFormula('(p∨q)∧(q∨p)'));
        assertEqual(cnf.toString(), '[[p,q]]');
        var cnf = m.cnf(parser.parseFormula('(p∨q)∧(q∨p∨q)'));
        assertEqual(cnf.toString(), '[[p,q]]');
    },
    
    cnf1: function() {
        var parser = new Parser();
        var m = new ModelFinder([parser.parseFormula('p')], parser);
        var cnf = m.cnf(parser.parseFormula('((a∧b)∨(c∧d))∨e'));
        assertEqual(cnf.toString(), '[[a,c,e],[a,d,e],[b,c,e],[b,d,e]]');
    },

    cnf2: function() {
        var parser = new Parser();
        var m = new ModelFinder([parser.parseFormula('p')], parser);
        var f = parser.parseFormula('((¬F∨G)∧(B∧¬W))∨((C∧¬E)∧(¬T∨D))');
        var cnf = m.cnf(f);
        // wolframalpha: CNF (((~F || G) && (B && ~W)) || ((C && ~E) && (~T || D)))
        // var correct = '[[¬F,G,C],[¬F,G,¬E],[¬F,G,¬T,D],[B,C],[B,¬E],[B,¬T,D],[¬W,C],[¬W,¬E],[¬W,¬T,D]]';
        var correct = '[[B,C],[B,¬E],[C,¬W],[¬E,¬W],[B,D,¬T],[D,¬T,¬W],[C,G,¬F],[G,¬E,¬F],[D,G,¬F,¬T]]';
        assertEqual(cnf.toString(), correct);
    },

    cnf3: function() {
        var parser = new Parser();
        var m = new ModelFinder([parser.parseFormula('p')], parser);
        var f = parser.parseFormula("(¬Px∨((¬Py∨Pf(xy))∧(Qxg(x)∧(¬Pg(x)∨¬Rcg(x)))))");
        var cnf = m.cnf(f);
        assertEqual(cnf.toString(), '[[Qxg(x),¬Px],[Pf(x,y),¬Px,¬Py],[¬Pg(x),¬Px,¬Rcg(x)]]');
    },

    cnfbicond: function(){
        var parser = new Parser();
        var m = new ModelFinder([parser.parseFormula('p')], parser);
        var f = parser.parseFormula('r ↔ (p↔q)');
        var cnf = m.cnf(f);
        assertEqual(cnf.toString(), '[[q,¬p,¬r],[p,¬q,¬r],[p,q,r],[r,¬p,¬q]]');
    },

    tseitinCNF_basic: function() {
        var parser = new Parser();
        var m = new ModelFinder([parser.parseFormula('p')], parser);
        var cnf = m.tseitinCNF(parser.parseFormula('p'));
        assertEqual(cnf.toString(), '[[p]]');
        var cnf = m.tseitinCNF(parser.parseFormula('¬p'));
        assertEqual(cnf.toString(), '[[¬p]]');
        var cnf = m.tseitinCNF(parser.parseFormula('p∨q'));
        assertEqual(cnf.toString(), '[[$],[$,¬p],[$,¬q],[p,q,¬$]]');
        var cnf = m.tseitinCNF(parser.parseFormula('p∧q'));
        assertEqual(cnf.toString(), '[[p],[q]]');
        // assertEqual(cnf.toString(), '[[$2],[p,¬$2],[q,¬$2],[$2,¬p,¬q]]');
    },
    
    // transformations2: function() {
    //     // example from http://www8.cs.umu.se/kurser/TDBB08/vt98b/Slides4/norm1_4.pdf
    //     var parser = new Parser();
    //     var f = parser.parseFormula('∀x(Px→(∀y(Py→Pf(x,y)))∧¬∀y(Qxy→(Py∧Rcy)))');
    //     f = f.nnf();
    //     var mf = new ModelFinder([f], parser);
    //     var cnf = mf.clauses;
    //     assertEqual(cnf.toString(), '[[¬Px,¬Py,Pf(xy)],[¬Px,Qxg(x)],[¬Px,¬Pg(x),¬Rcg(x)]]');
    // },

    simplifyCNF: function() {
        var parser = new Parser();
        var m = new ModelFinder([parser.parseFormula('p')], parser);
        var f = parser.parseFormula(
            '(p ∨ q) ∧ (q ∨ q ∨ r) ∧ (q ∨ r ∨ t) ∧ (r ∨ s) ∧ (s ∨ r) ∧ p '
        );
        var cnf = m.simplifyClauses(m.cnf(f));
        assertEqual(cnf, '[[p],[q,r],[r,s]]');
    },

    simplifyCNF2: function() {
        var parser = new Parser();
        var m = new ModelFinder([parser.parseFormula('p')], parser);
        var f = parser.parseFormula('((p∧(Fa∧Fb))∨(p∧(Fc∧Fd)))∧((q∧(Fe∧Ff))∨(q∧(Fg∧Fh)))');
        var cnf = m.simplifyClauses(m.cnf(f));
        assertEqual(cnf, '[[p],[q],[Fa,Fc],[Fa,Fd],[Fb,Fc],[Fb,Fd],[Fe,Fg],[Fe,Fh],[Ff,Fg],[Ff,Fh]]');
    },

    tseitin1: function() {
        var parser1 = new Parser();
        var parser2 = new Parser();
        var m1 = new ModelFinder([parser1.parseFormula('p')], parser1);
        var m2 = new ModelFinder([parser2.parseFormula('p')], parser2);
        var f = parser1.parseFormula('((p∨q)∧r)→¬s');
        // var tseitin = parser2.parseFormula('($↔¬s)∧($↔(p∨q))∧($2↔($∧r))∧($3↔($2→$3))∧$3');
        // [[$3],[$,¬p],[$,¬q],[$,¬$2],[r,¬$2],[$2,$3],[$3,s],[p,q,¬$],[$2,¬$,¬r],[¬$2,¬$3,¬s]]
        var res = m1.tseitinCNF(f);
        var tseitin = parser2.parseFormula('($↔(p∨q))∧($2↔($∧r))∧($3↔($2→¬s))∧$3');
        var cnf = m2.cnf(tseitin);
        assertEqual(res.toString(), cnf.toString());
    },

    // tseitin2_fails_because_in_cnf: function() {
    //     var parser = new Parser();
    //     var m = new ModelFinder([parser.parseFormula('p')], parser);
    //     var f = parser.parseFormula('(¬(p∨¬q)∧r)→¬s');
    //     var res = m.tseitinCNF(f);
    //     assertEqual(res.toString(), '[(p2↔¬s),(p3↔¬q),(p4↔(p∨p3)),(p5↔¬p4),(p6↔(p5∧r)),(p7↔(p6→p2)),p7]');
    // },

    transformation1: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('∀x∃y(Fx∧∀zHxyz)')], parser);
        // skolem: Fx & Hxf(x)z
        // tseitin: p & (p<->(Fx & Hxf(x)z)
        // cnf: p & (~p v Fx) & (~p v Hxf(x)z)) & (p v ~Fx v ~Hxf(x)z) 
        //    = p & (~p v Fx) & (~p v Hxf(x)z))
        // assertEqual(mf.clauses.toString(), '[[$xz],[Fx,¬$xz],[Hxf(x)z,¬$xz]]');
        // but since we don't tseitin expand conjunctions, we should simply get
        // Fx & Hxf(x)z
        assertEqual(mf.clauses.toString(), '[[Fx],[Hxf(x)z]]');
    },

    transformation2: function() {
        var parser = new Parser();
        var f = parser.parseFormula('¬∃y∀x(Fy→Fx)').nnf();
        var mf = new ModelFinder([f], parser);
        // skolem: Fy & ~Ff(y)
        // assertEqual(mf.clauses.toString(), '[[$y],[Fy,¬$y],[¬$y,¬Ff(y)]]');
        assertEqual(mf.clauses.toString(), '[[Fy],[¬Ff(y)]]');
    },

    transformation3: function() {
        var parser = new Parser();
        var f = parser.parseFormula('◇p');
        f = parser.translateFromModal(f).nnf();
        var mf = new ModelFinder([f], parser);
        //assertEqual(mf.initFormulas.toString(), '[(Rwu∧pu)]');
        // assertEqual(mf.clauses.toString(), '[[$],[Rwu,¬$],[pu,¬$]]');
        assertEqual(mf.clauses.toString(), '[[Rwu],[pu]]');
        assertEqual(parser.expressionType['u'], 'world constant');
    },

    several_inputformulas: function() {
        var parser = new Parser();
        var initflas = [parser.parseFormula('r∧p'), parser.parseFormula('q∧(r∧p)')];
        var m = new ModelFinder(initflas, parser);
        // assertEqual(m.clauses.toString(), '[[$],[$2],[r,¬$],[p,¬$],[q,¬$2]]');
        assertEqual(m.clauses.toString(), '[[r],[p],[q]]');
        initflas.push(parser.parseFormula('Fa'))
        m = new ModelFinder(initflas, parser);
        // assertEqual(m.clauses.toString(), '[[$3],[$4],[Fa],[r,¬$3],[p,¬$3],[q,¬$4]]');
        assertEqual(m.clauses.toString(), '[[r],[p],[q],[Fa]]');
    },

    modelclauses_quantified1: function() {
        var parser = new Parser();
        var initflas = [parser.parseFormula('∀xFx')];
        var mf = new ModelFinder(initflas, parser);
        var m = mf.model;
        assertEqual(m.clauses.toString(), '[[F0]]');
        m = new Model(mf, 2, 0);
        assertEqual(m.clauses.toString(), '[[F0],[F1]]');
    },

    modelclauses_quantified2: function() {
        var parser = new Parser();
        var initflas = [parser.parseFormula('∀x∃yGxy')];
        // skolemized: Gxf(x)
        var mf = new ModelFinder(initflas, parser);
        var m = mf.model;
        assertEqual(m.clauses.toString(), '[[G0f(0)]]');
        m = new Model(mf, 2, 0);
        assertEqual(m.clauses.toString(), '[[G0f(0)],[G1f(1)]]');
        assertEqual(mf.constants.toString(), '[]');
    },

    modelclauses_quantified3: function() {
        var parser = new Parser();
        var initflas = [parser.parseFormula('∀x∃y(Fx∧∀zHxyz)')];
        // skolemized: (Fx∧Hxf(x)z); tseitin-cnf: [$xz],[Fx,¬$xz],[Hxf(x)z,¬$xz],[$xz,¬Fx,¬Hxf(x)z]]');
        var mf = new ModelFinder(initflas, parser);
        var m = mf.model;
        // assertEqual(m.clauses.toString(), '[[$00],[F0,¬$00],[H0f(0)0,¬$00]]');
        assertEqual(m.clauses.toString(), '[[F0],[H0f(0)0]]');
        m = new Model(mf, 2, 0);
        // var correct = '[[$00],[$01],[$10],[$11],[F0,¬$00],[F0,¬$01],[F1,¬$10],[F1,¬$11],[H0f(0)0,¬$00],[H0f(0)1,¬$01],[H1f(1)0,¬$10],[H1f(1)1,¬$11]]'
        // reduces to [[F0],[F1],[H0f(0)0],[H0f(0)1],[H1f(1)0],[H1f(1)1]]
        var correct = '[[F0],[F1],[H0f(0)0],[H0f(0)1],[H1f(1)0],[H1f(1)1]]';
        assertEqual(m.clauses.toString(), correct);
    },

    countermodel1: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('¬p')], parser);
        mf.nextStep();
        var res = mf.nextStep();
        assertEqual(res, true);
        assertEqual(mf.model.toString().trim(), 'p: false');
    },

    countermodel2: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('p'), parser.parseFormula('¬q')], parser);
        mf.nextStep();
        var res = mf.nextStep();
        assertEqual(res, false);
        res = mf.nextStep();
        assertEqual(res, true);
        assertEqual(mf.model.toString().trim(), 'p: true\nq: false');
    },

    countermodel3: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('Ff(a,b)')], parser);
        mf.nextStep();
        var res = mf.nextStep();
        assertEqual(res, true);
        assert(mf.model.toString().indexOf('f: { (0,0,0) }')>0);
        assert(mf.model.toString().indexOf('F: { 0 }')>0);
    },

    countermodel4: function() {
        var parser = new Parser();
        var f = parser.parseFormula('Ff(a)∧¬Ff(f(a))').nnf();
        var mf = new ModelFinder([f], parser);
        for (var i=0; i<100; i++) {
            if (mf.nextStep()) break;
        }
        assert(mf.model.toString().indexOf('f: { (0,1), (1,0) }')>0);
        assert(mf.model.toString().indexOf('a: 0')>0);
        assert(mf.model.toString().indexOf('F: { 1 }')>0);
    },

    countermodel5: function() {
        var parser = new Parser();
        var mf = new ModelFinder([parser.parseFormula('∀xFx')], parser);
        var m = mf.nextStep();
        assert(mf.model.toString().indexOf('F: { 0 }')>0);
    },

    countermodel6: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('Fa ∧ ¬Fb')];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<100; i++) {
            if (mf.nextStep()) break;
        }
        assertEqual(mf.model.domain.length, 2);
        assert(mf.model.toString().indexOf('F: { 0 }')>0);
    },

    countermodel7: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('∀x∃yRxy ∧ ¬∃xRxx').nnf()];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<100; i++) {
            if (mf.nextStep()) break;
        }
        assertEqual(mf.model.domain.length, 2);
        assert(mf.model.toString().indexOf('R: { (0,1), (1,0) }') > 0);
    },

    countermodel8a: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('(∃xFx→∃xGx)→∀x(Fx→Gx)').negate().nnf()];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<800; i++) {
            if (mf.nextStep()) break;
        }
        assert(i<500);
        assertEqual(mf.model.domain.length, 2);
        assert(mf.model.toString().indexOf('F: { 1 }') > 0);
        assert(mf.model.toString().indexOf('G: { 0 }') > 0);
    },

    countermodel8: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('∃y∀x(Fx→Gx) ↔ (∃xFx → ∃xGx)').negate().nnf()];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<500; i++) {
            if (mf.nextStep()) break;
        }
        assert(i<500);
        assertEqual(mf.model.domain.length, 2);
        log(mf.model.toString());
        assert(mf.model.toString().indexOf('F: { 0 }') > 0);
        assert(mf.model.toString().indexOf('G: { 1 }') > 0);
    },

    countermodel9: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('∃y∃z∀x((Fx→Gy)∧(Gz→Fx))→∀x∃y(Fy↔Gy)').negate().nnf()];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<500; i++) {
            if (mf.nextStep()) break;
        }
        assert(i<500);
        assertEqual(mf.model.domain.length, 2);
        assert(mf.model.toString().indexOf('F: { 1 }') > 0);
        assert(mf.model.toString().indexOf('G: { 0 }') > 0);
    },

    countermodel10: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('p→p').nnf()];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<10; i++) {
            if (mf.nextStep()) break;
        }
        assert(i<5);
    },
     
    countermodel_shortestformulawith3individuals: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('∀y∃x(Ryx ∧ ¬Rxy)').nnf()];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<100; i++) {
            if (mf.nextStep()) break;
        }
        assertEqual(mf.model.domain.length, 3);
    },

    countermodel_shortestformulawith4individuals: function() { 
        var parser = new Parser();
        var fs = [parser.parseFormula('∀z∀y∃x(Rzx ∧ ¬Rxy)').nnf()];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<10000; i++) {
            if (mf.nextStep()) break;
        }
        assert(i<10000);
        assertEqual(mf.model.domain.length, 4);
    },
    
    iterateTermValues: function() {
        // If termValues aren't iterated properly a countermodel is found for this valid formula.
        var parser = new Parser();
        var fs = [parser.parseFormula('Na∧∀x(Nx→Nf(x))→Nf(f(f(f(f(a)))))').negate().nnf()];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<1000; i++) {
            if (mf.nextStep()) break;
        }
        assertEqual(i, 1000);
    },
    
    countermodel_modal1: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('◇p'), parser.parseFormula('¬p')];
        fs = fs.map(function(f){return parser.translateFromModal(f).nnf()});
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<100; i++) {
            if (mf.nextStep()) break;
        }
        assertEqual(mf.model.worlds.length, 2);
        assert(mf.model.toString().indexOf('@: w0') > 0);
        assert(mf.model.toString().indexOf('R: { (w0,w1) }') > 0);
        assert(mf.model.toString().indexOf('p: { w1 }') > 0);
    },

    countermodel_modal2: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('□p→p')];
        fs = fs.map(function(f){return parser.translateFromModal(f).nnf()});
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<100; i++) {
            if (mf.nextStep()) break;
        }
        assertEqual(mf.model.worlds.length, 1);
        assert(mf.model.toString().indexOf('p: { w0 }') > 0);
    },

    countermodel_modal3: function() {
        var parser = new Parser();
        var fs = [parser.translateFromModal(parser.parseFormula('□p')).nnf(),
                  parser.parseAccessibilityFormula('∀v∃u(Rvu)')];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<100; i++) {
            if (mf.nextStep()) break;
        }
        assertEqual(mf.model.worlds.length, 1);
        assert(mf.model.toString().indexOf('R: { (w0,w0) }') > 0);
        assert(mf.model.toString().indexOf('p: { w0 }') > 0);
    },

    countermodel_s5: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('□p')];
        fs = fs.map(function(f){
            var f2 = parser.translateFromModal(f).nnf();
            return parser.stripAccessibilityClauses(f2);
        });
        var mf = new ModelFinder(fs, parser, [], true);
        for (var i=0; i<100; i++) {
            if (mf.nextStep()) break;
        }
        assertEqual(mf.model.worlds.length, 1);
        assertEqual(mf.model.toString().indexOf('R:'), -1);
        assert(mf.model.toString().indexOf('p: { w0 }') >= 0);
    },

    totalfunctions1: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('f(a)=a∧¬Fb').negate().nnf()];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<500; i++) {
            if (mf.nextStep()) break;
        }
        assert(mf.model.toString().indexOf('f: { (0,0) }') > 0);
    },

    totalfunctions2: function() {
        var parser = new Parser();
        var fs = [parser.parseFormula('f(a)=a∧(Fa∨¬Fa)∧g(a,b)=a').negate().nnf()];
        var mf = new ModelFinder(fs, parser);
        for (var i=0; i<500; i++) {
            if (mf.nextStep()) break;
        }
        assert(mf.model.toString().indexOf('f: { (0,1), (1,0) }') > 0);
        assert(mf.model.toString().indexOf('g: { (0,0,0), (0,1,0), (1,0,0), (1,1,0) }') > 0);
    },

    github_issue_3_chrome: function() {
        var parser = new Parser();
        var f = parser.parseFormula('(((∀x(Mx→(◇Px∧◇¬Px))∧∃xMx)∧(∀x(Sx→(◇Mx∧◇¬Mx))∧∃xSx))→(∀x(Sx→(◇Px∧◇¬Px))∧∃xSx))');
        fs = [parser.translateFromModal(f).negate().nnf(),
              parser.parseAccessibilityFormula('∀v∀uRvu'),
              parser.parseAccessibilityFormula('∀v∀u∀t(Rvu→(Rut→Rvt))'),
              parser.parseAccessibilityFormula('∀v∀u∀t(Rvu→(Rvt→Rut))')];
        var mf = new ModelFinder(fs, parser, [], true);
        for (var i=0; i<1000; i++) {
            if (mf.nextStep()) break;
        }
        assert(i<1000);
        assertEqual(mf.model.worlds.length, 2);
    }

}
