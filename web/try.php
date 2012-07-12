<?php
session_start();
?>

<!DOCTYPE html PUBLIC "-//W3C//DTD HTML 4.01 Transitional//EN"
      "http://www.w3.org/TR/html4/loose.dtd">
<html>
<head>
  <meta http-equiv="Content-Type" content="text/html; charset=iso-8859-15">
  <title>Heptagon - try it !</title>
</head>

<?php

define("HEC", "/home_nas/gdelaval/bin/hec-stable");
define("HEAPPLET", "/home_nas/gdelaval/bin/heapplet-stable");
define("HEPTLIB", "/home_nas/gdelaval/synchronics/heptagon/lib/");

function tempdir($prefix) {
    $tempfile=tempnam(sys_get_temp_dir(),$prefix);
    if (file_exists($tempfile)) { unlink($tempfile); }
    mkdir($tempfile);
    if (is_dir($tempfile)) { return $tempfile; }
}

?>

<body>

<center>
<h1>Try Heptagon !</h1>

<form enctype="multipart/form-data"
      action="<?php echo $_SERVER['PHP_SELF']; ?>"
      method="post">
  <input type="hidden" name="MAX_FILE_SIZE" value="30000" />
  Heptagon program (with "<code>main</code>" node):
  <input name="heptfile" type="file" value="<?php echo $_FILES['heptfile']['name']; ?>"/>
  <br/>
  <textarea name="heptprog" rows="8" cols="100%">
<?php
if (isset($_POST['heptprog'])) {
  echo $_POST['heptprog'];
} else {
?>
node main(x:bool) returns (last y:int)
let
  automaton
    state Up
      do y = (0 -> last y) + 1
      until y = 10 then Down
    state Down
      do y = last y - 1
      until y = 0 then Up
  end
tel
<?php
}
?>
  </textarea><br/>
  <input type="submit" name="submit" value="Compile" />
</form>
</center>

<?php
if(isset($_POST['submit'])){
  // Ne marche pas : s'affiche une fois que la compil. est terminee
  //echo '<p>Compilation...</p>';
  flush();
  ob_flush();
  // Temporary directory creation
  $workdir = tempdir("heptagon-");
  // Copy Heptagon program to working directory
  $heptfile = $workdir . "/main.ept";
  $isfile = move_uploaded_file($_FILES['heptfile']['tmp_name'], $heptfile);
  if (! $isfile) {
    $hepthandle = fopen($heptfile,'a+');
    fputs($hepthandle,"(*@ java\npackage main;\n@*)\n");
    fputs($hepthandle,$_POST['heptprog']);
    fclose($hepthandle);
  };
  // Go to working directory
  chdir($workdir);
  // Compile main file
  echo '<pre>';
  $last_line = system(HEC
                      . ' -stdlib '
                      . HEPTLIB
                      . ' -target java -i main.ept 2> main.out',$res);
  echo '</pre>';
  flush();
  if ($res == 0) {
    // Make interface Java class
    mkdir('main_interface');
    echo '<!-- ';
    $h = system(HEAPPLET . ' -mod Main -node main -targetpath main_interface 2>&1');
    echo ' -->';
    echo '<pre>';
    // Java compilation
    system('javac '
           . '-classpath /home_nas/gdelaval/public_html/bzr/heptagon_applet.jar:.'
           . ' main_interface/MainInterface.java 2>&1');
    //system('ls -l *');
    echo '</pre>';
    // Make jar file
    $tempfile=tempnam('/home_nas/gdelaval/public_html/bzr/jar','main-');
    system('jar cf ' . $tempfile . '.jar main/*.class main_interface/*.class 2>&1');
    // $_SESSION['jarfile'] = $tempfile;
    // Generate applet HTML code
    ?>
<center>
  <applet name="HeptagonApplet" 
	  code="heptagon_applet.HeptagonApplet.class"
	  archive=<?php echo '"heptagon_applet.jar,jar/' . basename($tempfile) . '.jar"'?>
	  width="800"
	  height=<?php echo '"' . (60*$h + 60) . '"'?>
	  alt="Simulation loading...">
  </applet>
</center>
<?php      
  } else {
    echo '<pre>';
    passthru('cat main.out');
    echo '</pre>';
    echo '<p>Compilation failed !</p>';
  }
  system("rm -fr " . $workdir. "/*");
  // Get the compilation result
  // Working directory suppression
  rmdir($workdir);
}
?>

</body>
</html>
