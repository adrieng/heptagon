<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.1//EN"
                      "http://www.w3.org/TR/xhtml11/DTD/xhtml11.dtd">
<html>
  <head>
    <link rel="stylesheet" type="text/css" href="http://haltools.inrialpes.fr/css/VisuGen.css" />
    <link rel="stylesheet" type="text/css" href="http://haltools.inrialpes.fr/css/VisuRubriqueEncadre.css" />    <link type="text/css" href="style.css" rel="stylesheet">
    <meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1">
    <title>Heptagon/BZR publications</title>
  </head>
  
<body>
  
<?php include('toc.php'); ?>

<?php include('header.php'); ?>

<div id="content">
  <h3>Publications about Heptagon/BZR: definition, compilation, case studies</h3>

<?php
  $url = 'https://haltools.inria.fr/Public/afficheRequetePubli.php?collection_exp=HEPTAGON&CB_auteur=oui&CB_titre=oui&CB_article=oui&langue=Anglais&tri_exp=date_publi&ordre_aff=TA&Fen=Aff&css=../css/VisuRubriqueEncadre.css&noHeader';
  $http_page = file_get_contents($url,FILE_USE_INCLUDE_PATH);
  echo $http_page;
?>

  
                                           
</div>
</body>
</html>
