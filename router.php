<?php
// convert GET parameters:
$urlparts = explode('?', $_SERVER['REQUEST_URI']);
if (@$urlparts[1]) {
    $params = $urlparts[1];
    while (preg_match("/(\w+)=(\d)/", $url, $matches)) {
        $_GET[$matches[1]] = $matches[2];
        $params = replace($matches[0], '', $params);
    }
}
$requested = dirname(__FILE__) . $urlparts[0];
if (preg_match('/\.js$/', $requested)) {
   $_GET['file'] = $requested;
   include_once('_js.php');
}
elseif (preg_match('/\.(?:html|php)/', $requested)) {
   include_once($requested);
}
else {
   return false;    // serve the requested resource as-is.
}
?>
