<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.1//EN"
                      "http://www.w3.org/TR/xhtml11/DTD/xhtml11.dtd">
<html>
  <head>
    <link type="text/css" href="style.css" rel="stylesheet">
    <meta http-equiv="Content-Type" content="text/html; charset=iso-8859-1">
    <title>Heptagon</title>
  </head>
  
<body>
  
<?php include('toc.php'); ?>

<?php include('header.php'); ?>

<div id="content">
<p>
Heptagon is a synchronous dataflow language whose syntax and semantics is
inspired from <a href="http://www-verimag.imag.fr/Synchrone,30.html">Lustre</a>,
with a syntax allowing the expression of control structures (e.g., switch or
mode automata).
</p>
<p>
Heptagon is also a research compiler, whose aim is to facilitate
experimentation. The current version of the compiler includes the following
features:
<ul>
  <li><strong>Inclusion of <em>discrete controller synthesis</em> within the
  compilation</strong>: the language is equipped with a behavioral contract
  mechanisms, where assumptions can be described, as well as an "enforce"
  property part. The semantics of this latter is that the property should be
  enforced by controlling the behaviour of the node equipped with the
  contract. This property will be enforced by an automatically built controller,
  which will act on free controllable variables given by the programmer. This
  extension has been named <a href="http://bzr.inria.fr">BZR</a> in previous
  works.</li>
  <li><strong>Expression and compilation of array values with modular memory
  optimization.</strong> The language allows the expression and operations on
  arrays (access, modification, iterators). With the use of <em>location annotations</em>, the
  programmer can avoid unnecessary array copies.</li>
</ul>
</p>

<p>
  Heptagon is developed in
  the <a href="http://www.di.ens.fr/ParkasTeam.html">Parkas (ENS)</a>
  and <a href="http://pop-art.inrialpes.fr">Pop-Art (LIG/INRIA)</a> research teams.
</p>

<h2>How to get it or try it</h2>

<h3>Download</h3>

Heptagon can be freely downloaded <a href="http://gforge.inria.fr/projects/heptagon">here</a>.

<h3> Technical requirements</h3>
  
The use of the Heptagon compiler by itself does not require any additional
tools. However, the usual use involves a compiler for the generated code (target
languages are currently C or Java).

The tools below are optional or are related to some subparts of Heptagon:
<ul> 
  <li>The graphical display tool sim2chro can be obtained from
    <a href="http://www-verimag.imag.fr/~raymond/edu/distrib/">
      Verimag</a>. It can be used together with Heptagon's graphical simulator.</li>
  <li> <a href="https://gforge.inria.fr/projects/bzr">Sigali</a>, the
    controller synthesis tool, developed by the Espresso and Vertecs team at INRIA
    Rennes. </li>
</ul>


 <h3>Contact </h3> Please
 contact <a href="mailto:heptagon-developers@lists.gforge.inria.fr">us</a> for
 further information.


<h2>Main participants</h2>

<table>
  <tr>
    <td>Gwenaël Delaval</td>
    <td>Assistant Prof. at <a href="http://www.ujf-grenoble.fr/">UJF</a></td>
    <td>+33 4 76 61 54 31</td>
    <td><a href="mailto:gwenael.delaval@inria.fr">mail</a></td>
    <td><a href="http://pop-art.inrialpes.fr/people/delaval/">web</a></td>
  </tr>
  <tr>
    <td>Léonard Gérard</td>
    <td>PhD student at <a href="http://www.ens.fr/">ENS</a></td>
    <td></td>
    <td><a href="mailto:leonard.gerard at ens.fr">mail</a></td>
    <td></td>
  </tr>
  <tr>
    <td>Adrien Guatto</td>
    <td>PhD student at <a href="http://www.ens.fr/">ENS</a></td>
    <td></td>
    <td><a href="mailto:adrien dot guatto at ens dot fr">mail</a></td>
    <td><a href="http://www.di.ens.fr/~guatto/">web</a></td>
  </tr>
  <tr>
    <td>Hervé Marchand</td>
    <td>Researcher at <a href="http://www.inria.fr/">INRIA</a></td>
    <td>+33 2 99 84 75 09</td>
    <td><a href="mailto:herve.marchand@inria.fr">mail</a></td>
    <td><a href="http://www.irisa.fr/prive/hmarchan/">web</a></td>
  </tr>  
  <tr>
    <td>Cédric Pasteur</td>
    <td>PhD student at <a href="http://www.ens.fr/">ENS</a></td>
    <td></td>
    <td><a href="mailto:cedric dot pasteur at ens dot fr">mail</a></td>
    <td><a href="http://www.di.ens.fr/~pasteur/">web</a></td>
  </tr> 
  <tr>
    <td>Marc Pouzet</td>
    <td>Professor at <a href="http://www.ens.fr/">ENS</a></td>
    <td></td>
    <td><a href="mailto:marc dot pouzet at ens dot fr">mail</a></td>
    <td><a href="http://www.di.ens.fr/~pouzet/">web</a></td>
  </tr>
  <tr>
    <td>Eric Rutten</td>
    <td>Researcher at <a href="http://www.inria.fr/">INRIA</a></td>
    <td>+33 4 76 61 55 50</td>
    <td><a href="mailto:eric.rutten@inria.fr">mail</a></td>
    <td><a href="http://sardes.inrialpes.fr/~rutten">web</a></td>
  </tr>
</table>
</div>
</body>
</html>
