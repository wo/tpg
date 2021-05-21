<?php

/**
 * Preprocesses JS files. 
 * If name.js is requested, strip all comments and debugging code and output the rest.
 * if name.debug.js is requested, comments and debugging code are preserved;
 * Several script files can be packaged into one by requesting name1-name2-etc.js.
**/

header("Content-type: text/javascript");

// parse request:
if (!preg_match("/^([^\.]+)(\.debug)?\.js/", $_GET['file'], $matches)) {
	print "alert('JS loading error: invalid request {$_GET['file']}');\n";
	exit;
}
$files = explode("-", $matches[1]);
$debug = isset($matches[2]) ? $matches[2] : '';

// put together output:
$result = "";
if (count($files) > 1) {
	$result .= "/* check the source on github.com/wo/tpg */\n\n";
}
foreach ($files as $file) {
	if (!file_exists("$file.js")) {
		print "alert('JS loading error: file {$_GET['file']} not found');\n";
		exit;
	}
	$js = file("$file.js");
	if (!$debug) $js = compress(strip_debugging($js));
	$result .= implode("", $js)."\n";
}

// send output (gzipped if browser supports that):
ob_start("ob_gzhandler");
print $result;
ob_flush();
exit;

function strip_debugging($js) {
	// strip all debugging commands, i.e. all lines beginning with "log(":
	$newjs = array();
	foreach ($js as $line) {
		if (preg_match("/^\s*log\(/", $line)) continue;
		$newjs[] = $line;
	}
	return $newjs;
}

function compress($js) {
	// strip comments and superfluous whitespace:
	$newjs = array();
	foreach ($js as $line) {
		if (strpos($line, "// ") !== false) $line = substr($line, 0, strpos($line, "// "));
		$line = trim($line);
		if ($line != "") $newjs[] = $line;
	}
	$jsstr = implode("\t\n", $newjs);
	$jsstr = preg_replace("!\s*/\*.*?\*/\s*!s", "\n", $jsstr);
	$js = explode("\t", $jsstr);
	return $js;
}

?>
