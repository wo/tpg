<?php



// GET-Parameter und ihre Default-Werte:

if (!isset($w) || $w > 30) $w = 10;           // Breite

if (!isset($h) || $h > 50) $h = 16;           // Hoehe

if (!isset($s) || $h > 20) $s = 14;           // Schriftgroesse

if (!isset($c) || strlen($c) > 5) $c = "x";   // Zeichen ("_J" fuer Polnischen Operator J)



header ("Content-type: image/gif");

$img = ImageCreate($w, $h);

$bg = ImageColorAllocate($img, 255, 255, 255);

$txt = ImageColorAllocate($img, 0, 0, 0);

$angle = ($c=="_Q" || $c=="_S")? 90 : 0;

ImageTTFText($img, $s, $angle, 1, $h-1, $txt, "arial.ttf", $c);

ImageGIF($img);



?>

