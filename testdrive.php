<meta charset="utf-8">
<head>

<title>Tree Proof Generator Test</title>

<style type="text/css">
#canvas { position:absolute; left:0px; top:80px; width:2000px; height:3000px; background-color:#fff; visibility:hidden; }
#rootAnchor { position:absolute; left:50px; top:0; width:100%; font-family:Arial,sans-serif; }
.treeNode, .treeNodeHiParent, .treeNodeHiChild { white-space:nowrap; color:#666; text-align:center; }
.treeNodeHiParent { background-color:#fd9; border:1px dotted #96c; }
.treeNodeHiChild { background-color:#fff7d9; border:1px dotted #96c; }
.formula { color:#600; text-decoration:none; }
</style>

<?php
$scripts = array("array", "formula", "parser", "prover", "modelfinder", "sentree", "painter");
if ($_GET['debug'] || $_GET['comments']) {
	$flag = $_GET['debug'] ? "debug" : "comments";
	foreach ($scripts as $script) {
		print "<script type='text/javascript' src='$script.$flag.js'></script>\n";
	}
    print "<script>\n";
    print 'debug = function(str) { if (!self.debugWin) debugPopup(); debugWin.document.write("<pre>"+str+"</pre>"); }'."\n";
    print 'debugPopup = function() { debugWin = self.open("about:blank","debugWin"); if (!self.debugWin) alert("unblock popups!"); }'."\n";
    print 'debug("hello, this is the debugging window");'."\n";
    print 'function log(str) { debug(str); }'."\n";
    print '</script>';
}
else {
	$allscripts = implode("-", $scripts);
	print "<script type='text/javascript' src='$allscripts.js'></script>\n";
    print "<script>\n";
    print "function log(str) {};\n";
    print '</script>';
}
?>
<?php 
if ($_GET['script']) {
	$scripts = explode(",", $_GET['script']);
	foreach ($scripts as $scr) print "<script type='text/javascript' src='" . script($scr) . "'></script>\n";
}
?>
<script>

function prover_status(str) {
	document.getElementById("status").firstChild.nodeValue = str;
}

function paintTree() {
	if (prover.counterModel) document.getElementById("rootAnchor").innerHTML = prover.counterModel.toString();
	else painter.paintTree();
}

</script>

</head>

<body>

<div style="position:fixed; left:0; top:0; padding:10px; width:100%; background-color:#ccddee; text-align:center;">

TPG Test Drive / 
Debugging <?=($_GET["debug"] ? "on (<a href='?debug=0'>off</a>)" : "off (<a href='?debug=1'>on</a>)")?> /
<form style="display:inline;" onsubmit="setTimeout('prove(document.forms[0].f.value, null, document.forms[0].d.value)', 100); return false">
<input type="checkbox" onchange="self.prover.fastMode=(this.checked)? true : false"> Fast Mode / 
<input type="text" size="50" name="f" id="flaInput" value=""> <input type="submit" value="Prove!">
(depth <input type="text" size="1" name="d" value="1">)
</form><br>

<div id="flaDiv" style="padding:5px; display:none;">
</div>

<div style="padding:5px;">
<span id="status">
</span>
<button onclick="prover.stop()">stop</button>
<input type="checkbox" onchange="document.getElementById('canvas').style.visibility=(this.checked)? 'visible' : 'hidden'; if (this.checked) paintTree()"> canvas
</div>

</div>

<div id="canvas">
<div id="rootAnchor">
</div>
</div>

<br><br><br><br>

<div id="flas" style="display:none">

simp	(p\lor(q\landr))\to((p\lorq)\land(p\lorr))	valid

merg	\lnot((p\land\lnot(p\top))\lor\lnot(p\top))	valid

fun	\forall x F(x) \to Ff(a)	valid

func	\lnot(Pa\land\lnotPf(f(a))\land\forallx(Px\toPf(x)))	valid

bost2nnf	\lnot(\forallx(f(x)\landg(a)\lor\lnotf(x)\land\lnotg(a)) \land \forally\forallz(f(b)\land\lnotg(y)\lorg(z)\land\lnotf(b)) \lor \forallw(f(d)\land\lnotg(w)\lor\lnotf(d)\landg(w)) \land \foralls((\lnotf(s)\lorg(e)) \land (\lnotg(k)\lorf(s))))	valid

t5	\existsx(P\landFx)\leftrightarrowP\land\existsxFx	valid

t6	\forallx\existsy(Fx\leftrightarrowGy)\to\existsy\existsz\forallx((Fx\toGy)\land(Gz\toFx))	valid

t7	\existsy\existsz\forallx((Fx\toGy)\land(Gz\toFx))\to\forallx\existsy(Fx\leftrightarrowGy)	valid

t8	\forallx(Fx\toFf(x))\landFf(a)\toFf(f(f(a)))	valid

t9	\forallx(Fx\toFf(x))\landFf(g(f(a),b))\toFf(f(f(g(f(a),b))))	valid

ddelta	\neg\forallx(Fx\land\existsy\negFy)	valid

b162.2	\forally\existsx(Fx\landGy)\to\existsx\forally(Fx\landGy)	valid

b164.1	\existsx(Fx\to\forallxFx)	valid

b164.k	\forallx\existsy(Fx\leftrightarrowGy)\leftrightarrow\existsy\forallx(Fx\toGy)\land\existsy\forallx(Gy\toFx)	valid

b164.l	\forallx\existsy(Fx\leftrightarrowGy)\leftrightarrow\existsy\existsz\forallx((Fx\toGy)\land(Gz\toFx))	valid

conpos	\forally(Iy\to\forallx(Px\leftrightarrowCxy))\land\existsyIy\to\forallx(Px\leftrightarrow\forally(Iy\toCxy))	valid

carnap	(\existsxFx\toFw)\land(\neg\existsxFx\land\existsxGx\toGw)\leftrightarrow(\existsx(Fx\lor(\neg\existsyFy\landGx))\to(Fw\lor(\neg\existsyFy\landGw)))	valid

pel1	((p\toq)\leftrightarrow(\negq\to\negp))	valid

pel2	(\neg\negp\leftrightarrowp)	valid

pel3	(\neg(p\toq)\to(q\top))	valid

pel4	((\negp\toq)\leftrightarrow(\negq\top))	valid

pel5	(((p\lorq)\to(p\lorr))\to(p\lor(q\tor)))	valid

pel6	(p\lor\negp)	valid

pel7	(p\lor\neg(\neg(\negp)))	valid

pel8	(((p\toq)\top)\top)	valid

pel9	((((p\lorq)\land(\negp\lorq))\land(p\lor\negq)) \to \neg(\negp\lor\negq))	valid

pel10	\neg(\neg(p\leftrightarrowq)\land(q\tor) \land(r\to(p\landq))\land(p\to(q\lorr)))	valid

pel11	(p\leftrightarrowp)	valid

pel12	(((p\leftrightarrowq)\leftrightarrowr) \leftrightarrow (p\leftrightarrow(q\leftrightarrowr)))	valid

pel13	((p\lor(q\landr))\leftrightarrow((p\lorq)\land(p\lorr)))	valid

pel14	((p\leftrightarrowq)\leftrightarrow((q\lor\negp)\land(\negq\lorp)))	valid

pel15	((p\toq)\leftrightarrow(\negp\lorq))	valid

pel16	((p\toq)\lor(q\top))	valid

pel17	(((p\land(q\tor))\tos) \leftrightarrow (((\negp\lorq)\lors)\land((\negp\lor\negr)\lors)))	valid

pel18	\existsy\forallx(Fy\toFx)	valid

pel19	\existsx\forally\forallz((Py\toQz)\to(Px\toQx))	valid

pel20	(\forallx\forally\existsz\forallw((Px\landQy)\to(Rz\landSw)) \to \existsx1\existsy1((Px1\landQy1)\to\existsz1(Rz1)))	valid

pel21	\neg(\neg\existsx(P\leftrightarrowFx) \land\existsx1(P\toFx1)\land\existsx2(Fx2\toP))	valid

pel22	\forallx(P\leftrightarrowFx)\to(P\leftrightarrow\forallyFy)	valid

pel23	\forallx(P\lorFx)\leftrightarrow(P\lor\forallyFy)	valid

pel24	\neg(\neg\existsx(Px\landRx) \land \neg\existsy(Sy\landQy) \land \forallv(Pv\to(Qv\lorRv)) \land (\neg\existsyPy\to\existszQz) \land \forallw((Qw\lorRw)\toSw))	valid

pel25	\neg(\neg\existsx(Qx\landPx) \land \existsyPy \land \forally(Fy\to(\negGy\landRy)) \land \forally(Py\to(Gy\landFy)) \land (\forally(Py\toQy)\lor\existsz(Pz\landRz)))	valid

pel26	\neg(\neg(\forallx(Px\toRx)\leftrightarrow\forally(Qy\toSy)) \land (\existszPz\leftrightarrow\existszQz) \land \forallx\forally((Px\landQy)\to(Rx\leftrightarrowSy)))	valid

//	pel26nnf	\neg(((q(a)\land \negs(a))\land \forallx(\negp(x)\lorr(x))\lor (p(b)\land \negr(b))\land \forally(\negq(y)\lors(y)))\land (p(c)\land q(d)\lor\forallz\negp(z)\land \forallw\negq(w))\land \forallv\forallw((\negp(v)\lor\negq(w))\lorr(v)\land s(w)\lor\negr(v)\land \negs(w)))	valid

pel27	\neg(\neg\forallx (J(x) \to \negI(x)) \land \existsy (F(y) \land \negG(y)) \land \forallz (F(z) \to H(z)) \land \forallw ((J(w) \land I(w)) \to F(w)) \land (\existsx2 (H(x2) \land \negG(x2)) \to \forallx3 (I(x3) \to \negH(x3))))	valid

pel28	\neg(\neg\forallx ((P(x) \land F(x)) \to G(x)) \land \forally (P(y) \to \forallz (Q(z))) \land (\forallw (Q(w) \lor R(w)) \to \existsx2 (Q(x2) \land S(x2))) \land (\existsx3 (S(x3)) \to \forallx4 (F(x4) \to G(x4))))	valid

pel29	\neg(\neg((\forallx (F(x) \to H(x)) \land \forally (G(y) \to J(y))) \leftrightarrow \forallz \forallw ((F(z) \land G(w)) \to (H(z) \land J(w)))) \land (\existsx2 (F(x2)) \land \existsx3 (G(x3))))	valid

pel30	\neg(\neg\forallx (I(x)) \land \forally ((F(y) \lor G(y)) \to \negH(y)) \land \forallz ((G(z) \to \negI(z)) \to (F(z) \land H(z))))	valid

pel31	\neg(\neg\existsx (I(x) \land J(x)) \land \neg\existsy (F(y) \land (G(y) \lor H(y))) \land \existsz (I(z) \land F(z)) \land \forallw (\negH(w) \to J(w)))	valid

pel32	\neg(\neg\forallx ((F(x) \land K(x)) \to J(x)) \land \forally ((F(y) \land (G(y) \lor H(y))) \to I(y)) \land \forallz ((I(z) \land H(z)) \to J(z)) \land \forallw (K(w) \to H(w)))	valid

pel33	\forallx ((P(a) \land (P(x) \to P(b))) \to P(c)) \leftrightarrow \forally ((\negP(a) \lor (P(y) \lor P(c))) \land (\negP(a) \lor (\negP(b) \lor P(c))))	valid

pel34	(\existsx \forally (P(x) \leftrightarrow P(y)) \leftrightarrow (\existsz (Q(z)) \leftrightarrow \forallw (Q(w)))) \leftrightarrow (\existsx2 \forallx3 (Q(x2) \leftrightarrow Q(x3)) \leftrightarrow (\existsx4 (P(x4)) \leftrightarrow \forallx5 (P(x5))))	valid

pel35	\existsx \existsy (P(x,y) \to \forallz \forallw (P(z,w)))	valid

pel36	\neg(\neg\forallx \existsy (H(x,y)) \land \forallz \existsw (F(z,w)) \land \forallx2 \existsx3 (G(x2,x3)) \land \forallx4 \forallx5 ((F(x4,x5) \lor G(x4,x5)) \to \forallx6 ((F(x5,x6) \lor G(x5,x6)) \to H(x4,x6))))	valid

pel37	\neg(\neg\forallx \existsy (R(x,y)) \land \forallz \existsw \forallx2 \existsx3 (P(x2,z) \to ((P(x3,w) \land P(x3,z)) \land (P(x3,w) \to \existsx4 (Q(x4,w))))) \land \forallx5 \forallx6 (\negP(x5,x6) \to\existsx7 (Q(x7,x6))) \land (\existsx8 \existsx9 (Q(x8,x9)) \to \forally1 (R(y1,y1))))	valid

pel38	\forallx ((P(a) \land (P(x) \to \existsy (P(y) \land R(x,y)))) \to \existsz \existsw ((P(z) \land R(x,w)) \land R(w,z))) \leftrightarrow \forallx2 ((((\negP(a)) \lor P(x2)) \lor \existsx3 \existsx4 ((P(x3) \land R(x2,x4)) \land R(x4,x3))) \land (((\negP(a)) \lor (\neg\existsx5 (P(x5) \land R(x2,x5)))) \lor \existsx6 \existsx7 ((P(x6) \land R(x2,x7)) \land R(x7,x6))))	valid

pel39	\neg\existsx \forally (F(y,x) \leftrightarrow \negF(y,y))	valid

pel40	\existsx \forally (F(y,x) \leftrightarrow F(y,y)) \to \neg\forallz \existsw \forallx2 (F(x2,w) \leftrightarrow \negF(x2,z))	valid



i1	p	invalid

i2	((p\toq)\leftrightarrow(q\top))	invalid

i3	\forallxFx	invalid

i4	\existsxFx	invalid

i5	\forallx\existsyRxy	invalid

i6	\existsy\forallxFxy	invalid

ifun	\forallx\existsy (Fx \to Ff(y)) \to (\negFa \lor Ff(a))	invalid

Her	\neg\forallx((Fx\wedge\negFa)\veeGa)	invalid

bost1	\forallx\forally\forallz(Fxy\landFyz\toFxz) \land \forallx\forally(Fxy\toFyx) \land \existsx\existsyFxy \to \forallxFxx	invalid

2ind	\neg\existsx\existsy(Fx\land\negFy)	invalid

4ind	\neg(Fa \land Ga \land Fb \land \negGb \land \negFc \land Gc \land \negFd \land \negGd)	invalid

infinity	\neg(\forallx\existsyFxy \land \forallx\forally\forallz(Fxy\landFyz\toFxz) \land \forallx\negFxx)	invalid

bx	\forally\existsxFxy\to\existsx\forallyFxy	invalid

bn	\existsy\existsz\forallx((Fx\toGy)\land(Gz\toFx))\to\forallx\existsy(Fy\leftrightarrowGy)	invalid

conpos1	\forally(Iy\to\forallx(Px\leftrightarrowCxy))\to\forallx(Px\leftrightarrow\forally(Iy\toCxy))	invalid

conpos2	\forallx(Px\leftrightarrow\forally(Iy\toCxy))\to\forally(Iy\to\forallx(Px\leftrightarrowCxy))	invalid



</div>

<script type="text/javascript">

function latex2str(str) {
    str = str.replace(/\s*/g, '');
    str = str.replace(/\\forall[\{ ]?\}?/g, '∀');
    str = str.replace(/\\exists[\{ ]?\}?/g, '∃');
    str = str.replace(/(\\neg|\\lnot)[\{ ]?\}?/g, '¬');
    str = str.replace(/\\Box[\{ ]?\}?/g, '□');
    str = str.replace(/\\Diamond[\{ ]?\}?/g, '◇');
    str = str.replace(/(\\vee|\\lor)[\{ ]?\}?/g, '∨');
    str = str.replace(/(\\wedge|\\land)[\{ ]?\}?/g, '∧');
    str = str.replace(/(\\to|\\rightarrow)[\{ ]?\}?/g, ' → ');
    str = str.replace(/\\leftrightarrow[\{ ]?\}?/g, ' ↔ ');
    //str = str.replace(/([^'])(\\[^<]*)/, '$1<span class="latex">$2</span>'); // unfinished latex commands
    //str = str.replace(/^(\\[^<]*)/, '<span class="latex">$1</span>'); // unfinished latex commands
    str = str.replace(/([^'])(\\[^<]*)/, '$1$2'); // unfinished latex commands
    str = str.replace(/^(\\[^<]*)/, '$1'); // unfinished latex commands
    return str;
}

if (document.getElementById("flas")) {
	var flas = "";
	for (var i=0; i<document.getElementById("flas").childNodes.length; i++) {
		flas += document.getElementById("flas").childNodes[i].nodeValue;
	}
	flas = flas.split("\n");
	var validTests = [];
	var invalidTests = [];
	for (var i=0; i<flas.length; i++) {
		if (flas[i] == "") continue;
		var fvals = flas[i].split("\t");
		if (fvals.length != 3) continue;
        fvals[1] = latex2str(fvals[1]);
		if (fvals[2] == 'valid') validTests.push({ name: fvals[0], fla : fvals[1] });
		else invalidTests.push({ name: fvals[0], fla : fvals[1] });
	}
	document.getElementById("flas").parentNode.removeChild(document.getElementById("flas"));
	
	document.write("<table id='testTable'>\n");
	document.write("<tr><th colspan='3'>Valid Formulas</th><th>Result</th></tr>\n");
	for (var i=0; i<validTests.length; i++) {
		document.write("<tr" + (i%2 ? " style='background-color:#eee'" : "") + "><td>"+validTests[i].name+"</td><td>"+validTests[i].fla+"</td><td><button onclick='prove(\""+validTests[i].fla+"\", \""+i+"0\")'>prove</button></td><td id='res"+i+"0'>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;</td></tr>\n");
	}
	document.write("<tr><th colspan='3'><br>Invalid Formulas</th><th><br>Result</th></tr>\n");
	for (var i=0; i<invalidTests.length; i++) {
		document.write("<tr" + (i%2 ? " style='background-color:#eee'" : "") + "><td>"+invalidTests[i].name+"</td><td>"+latex2str(invalidTests[i].fla)+"</td><td><button onclick='prove(\""+latex2str(invalidTests[i].fla)+"\", \""+i+"1\")'>prove</button></td><td id='res"+i+"1'>&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;</td></tr>\n");
	}
	document.write("</table>\n");
}

function prove(fla, resultId) {
    var parser = new Parser();
    var formula = parser.parseFormula(fla);
	self.resultId = resultId;
	self.startDate = new Date();
    self.prover = new Prover([formula.negate()]);
    prover.status = prover_status;
    prover.onfinished = get_onfinished(formula.negate());
	prover.start();
}

function proveAll(timeLimit) {
	self.arr = validTests;
	self.ind = 0;
    self.provingAll = true;
    self.timeLimit = timeLimit;
	proveNext();
}

function proveNext() {
	if (!arr[ind]) {
		if (arr == invalidTests) {
            self.provingAll = false;
			return;
		}
		arr = invalidTests;
		ind = 0;
	}
	var test = arr[ind];
	prove(test.fla, ind + (arr == validTests ? "0" : "1"));
	ind++;
	stopTimer = setTimeout("prover.stop(); proveNext()", timeLimit);
}

function get_onfinished(initFormula) {
    return function(state) {
        endDate = new Date();
        // var sentenceTree = new SenTree(this.tree, [initFormula.negate()]);
        // if (!state) {
        //     if (!this.counterModel) this.counterModel = sentenceTree.getCounterModel();
        //     if (!this.counterModel) alert("no countermodel for invalid formula");
        // }
        // painter = new TreePainter(sentenceTree, document.getElementById("rootAnchor"));
        var res = (endDate - startDate) + ": " + (state ? "valid" : "invalid");
        if (resultId !== null) document.getElementById("res"+resultId).firstChild.nodeValue = res;
        else alert(res);
        if (self.stopTimer) clearTimeout(stopTimer);
        if (self.provingAll) setTimeout('proveNext()', 500);
    }
}


</script>

<br><br><br><br>

<div id="bottombar" style="position:fixed; bottom:0; left:0; padding:10px; width:100%; background-color:#ccddee; text-align:center;">
<form action="#" method="get" style="display:inline">
<input type="button" onclick="proveAll(this.form.l.value)" value="run all tests"> 
Limit <input type="text" size="7" name="l" value="30000"> ms/test
</form>
-
<form action="_dump.php" method="post"  style="display:inline">
<input type="button" onclick="this.form.content.value=''; this.form.content.value=document.body.innerHTML; this.form.submit()" value="dump"> 
as <input type="text" size="20" name="filename" value="dump_1.html">
<input type="hidden" name="content" value="">
</form>
</div>

</body>
</html>
