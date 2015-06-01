<!DOCTYPE HTML PUBLIC "-//W3C//DTD HTML 4.0 Transitional//EN">



<html>

<head>

<title>Tree Proof Generator: Examples</title>



<style type="text/css">

body { padding-left:60px; padding-top:20px; font-family:Verdana,Arial,sans-serif; font-size:11pt; }

#title { background-color:#EAB700; border:1px outset #EAB700; padding:2px; text-align:center; color:#000033; font-weight:bold; font-size:22px; }

td.menu { background-color:#EAB700; border:1px outset #EAB700; padding:2px; text-align:center; }

td.menuhi { background-color:#F6DE00; border:1px outset #EAB700; padding:2px; text-align:center; }

td.menu:hover { background-color:#F6DE00; }

a.menu { text-decoration:none; color:#000000; font-size:14px; font-weight:bold; }

.content { width:500px; position:absolute; left:110px; top:130px; border-left:1px solid #EAB700; border-right:1px solid #EAB700; padding:10px; }

.code { font-family:Arial,Helvetica,sans-serif; font-size:16px; color:#660000; text-decoration:none; }

</style>



</head>



<body>



<table cellspacing="0" cellpadding="0" width="600">

<tr><td id="title" colspan="5">Tree Proof Generator</td></tr>

<tr>

<td class="menu">&nbsp;<a class="menu" href="index.html">New Proof</a> </td>

<td class="menuhi">&nbsp;<a class="menu" href="examples.html">Examples</a> </td>

<td class="menu">&nbsp;<a class="menu" href="help.html"> &nbsp; Help &nbsp; </a> </td>

<td class="menu">&nbsp;<a class="menu" href="feedback.html">Feedback</a> </td>

</tr>

</table>



<div id="content1a" class="content">



<p>Click on a formula to see its tree proof:</p>



<?php 

function makeLink($fla) {

	$href = "proof.html?f=".urlencode($fla);

	$text = preg_replace("/\\\\(neg|wedge|vee|to|leftrightarrow|forall|exists)/", "<img src='\\0.gif' alt='then' align='top' border='0'>", $fla);

	print "<p><a class='code' href='$href'>$text</a></p>\n";

}



makeLink('A\\wedge\\negA\\toB');

makeLink('\\neg(A\\wedgeB)\\leftrightarrow\\negA\\vee\\negB');

makeLink('(A\\to(B\\toC))\\to((A\\toB)\\to(A\\toC))');

makeLink('((A\\toB)\\toA)\\toA');

makeLink('(\\forallxFx\\to\\neg\\forallx\\negGx)\\to\\neg\\forallx\\neg(Fx\\toGx)');



?>



<p>These are not valid:</p>



<?php



makeLink('\\forallx\\forally\\forallz(Fxy\\wedgeFyz\\toFxz)\\wedge\\forallx\\forally(Fxy\\toFyx)\\to\\forallxFxx');

makeLink('\\forallx\\forally\\forallz(Fxy\\wedgeFyz\\toFxz)\\wedge\\forallx\\forally(Fxy\\toFyx)\\wedge\\existsx\\existsyFxy\\to\\forallxFxx');



?>



</div>



</body>

</html>

