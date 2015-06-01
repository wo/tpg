<?php

/**
 * Preprocesses JS files. 
 * If name.js is requested, strip all comments and debugging code and output the rest.
 * If name.comments.js is requested, comments are preserved;
 * if name.debug.js is requested, debugging code is also preserved;
 * *.linenumbers.js adds linenumbers in front of each line (for debugging).
 * Several script files can be packaged into one by requesting name1-name2[etc.].[comments|debug.][linenumbers.]js.
**/

header("Content-type: text/javascript");

$linenumbers = false;
// strip 'linenumbers' flag and store information in a variable:
if (preg_match("/(.+)\.linenumbers\.js/", $_GET['file'], $matches)) {
	$_GET['file'] = $matches[1].".js";
	$linenumbers = true;
}

// parse request:
if (!preg_match("/^([^\.]+)(\.comments)?(\.debug)?\.js/", $_GET['file'], $matches)) {
	print "alert('JS loading error: invalid request {$_GET['file']}');\n";
	exit;
}
$files = explode("-", $matches[1]);
$debug = isset($matches[3]) ? $matches[3] : '';
$comments = $debug || (isset($matches[2]) ? $matches[2] : '');

// put together output:
$result = "";
if (count($files) > 1) {
	$result .= "/* If you're interested in the source, have a look at index.html?comments=true. */\n\n";
}
foreach ($files as $file) {
	if (!file_exists("$file.js")) {
		print "alert('JS loading error: file {$_GET['file']} not found');\n";
		exit;
	}
	$js = file("$file.js");
	if (!$debug) $js = strip_debugging($js);
	if (!$comments) $js = compress($js);
	if ($linenumbers) $js = addlinenumbers($js);
	$result .= implode("", $js)."\n";
}

// send output (gzipped if browser supports that):
ob_start("ob_gzhandler");
print $result;
ob_flush();
exit;

function strip_debugging($js) {
	// strip all debugging commands, i.e. all lines beginning with "debug":
	$newjs = array();
	foreach ($js as $line) {
		if (preg_match("/^\s*debug/", $line)) continue;
		$newjs[] = $line;
	}
	return $newjs;
}

function compress($js) {
	// strip comments and superfluous whitespace:
	$newjs = array();
	foreach ($js as $line) {
		if (strpos($line, "//") !== false) $line = substr($line, 0, strpos($line, "//"));
		$line = trim($line);
		if ($line != "") $newjs[] = $line;
	}
	$jsstr = implode("\t\n", $newjs);
	$jsstr = preg_replace("!\s*/\*.*?\*/\s*!s", "\n", $jsstr);
	$js = explode("\t", $jsstr);
	return $js;
}

function addlinenumbers($js) {
	$newjs = array();
	for ($i=0; $i<count($js); $i++) $newjs[] = ($i+1)." ".$js[$i];
	return $newjs;
}

?>
