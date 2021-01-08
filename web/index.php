<!DOCTYPE html PUBLIC "-//W3C//DTD XHTML 1.1//EN"
                      "http://www.w3.org/TR/xhtml11/DTD/xhtml11.dtd">
<html>
  <head>
    <link type="text/css" href="style.css" rel="stylesheet">
    <meta http-equiv="Content-Type" content="text/html; charset=utf-8">
    <title>Heptagon/BZR</title>
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
  and <a href="http://team.inria.fr/ctrl-a">Ctrl-A (LIG/INRIA)</a> research teams.
</p>

<h2>How to get it or try it</h2>

<h3>Installation with OPAM</h3>

<p>The easiest and recommended way to install Heptagon/BZR is to use
the OCaml Package Manager (OPAM).</p>

<p>The installation sequence using OPAM is :
    <ol>
      <li>Install OPAM (at least v2.0) : the procedure depends on your system and is
        described <a href="http://opam.ocaml.org/doc/Install.html">on
          the OPAM webpage</a>.</li>
      <li>(optional, for the graphical simulator) Install
        the <i>gtk2.0</i> libraries (on debian systems, the package is
        named <tt>libgtk2.0-dev</tt>)</li>
      <li>Initialize OPAM:
        <pre>
          opam init
        </pre>
        This command should install a version of OCaml at least ≥
        4.08. Follow the instructions given throughout this initialization.
      </li>
      <li>Install Heptagon:
        <pre>opam install heptagon</pre>
      </li>
    </ol>
</p>
<p>To use the controller synthesis tool ReaX with Heptagon/BZR :
  <ol>
    <li>Install the <i>mpfr</i> and <i>gmp</i> libraries (on debian
        systems, packages named <tt>libmpfr-devel</tt>
        and <tt>libgmp-devel</tt>)</li>
    <li>Add the repository for ReaX and its libraries (named here
      nberth-repo) :
      <pre>
        opam repo add nberth-repo "http://nberth.space/opam-repo"
        opam update
      </pre>
    </li>
    <li>Install ReaX and its libraries, and the BZReaX script:
      <pre>opam install bzreax</pre>
    </li>
  </ol>
</p>
<p>The source code is also available from <a
        href="https://gitlab.inria.fr/synchrone/heptagon">the Heptagon/BZR repository</a> for manual
      compilation and installation. Further indications about ReaX can
      be found on <a href="http://reatk.gforge.inria.fr">the ReaX/ReaTk
        page</a>.<br>
    </p>

<h3>Manual installation</h3>
<h4>Download</h4>

<p>
Heptagon can be freely downloaded <a href="http://gforge.inria.fr/projects/heptagon">here</a>.
</p>

<h4>Technical requirements</h4>
<p>  
The use of the Heptagon compiler by itself does not require any
additional tools. However, the usual use involves a compiler for the
generated code (target languages are currently C or Java).
</p>
<p>
  To manually compile and install the Heptagon compiler, the following tools and libraries are needed:
  <ul>
    <li>ocamlfind</li>
    <li>The <em>menhir</em> tool</li>
    <li>The <em>ocamlgraph</em> library</li>
    <li><em>camlp4</em></li>
    <li>The <em>lablgtk</em> library (optional, for the graphical simulator)</li>
    <li>The <em>reatk</em> library (optional, for the backend towards the ReaX controller synthesis too)</li>
  </ul>
</p>
<p>
The tools below are optional or are related to some subparts of Heptagon:
<ul> 
  <li>The graphical display tool sim2chro can be obtained from
    <a href="http://www-verimag.imag.fr/~raymond/edu/distrib/">
      Verimag</a>. It can be used together with Heptagon's graphical simulator.</li>
  <li> <a href="https://gforge.inria.fr/projects/bzr">Sigali</a>, the
    controller synthesis tool, developed by the Espresso and Vertecs team at INRIA
    Rennes. </li>
</ul>
</p>

<h4>Compilation and installation</h4>

<p>Once the previously described libraries and tools are installed, the Heptagon compiler and libraries can be installed with:
  <pre>
    ./configure
    make
    make install
  </pre>
</p>

<h2>Contact</h2>

<p>
Please
contact <a href="mailto:heptagon-developers@lists.gforge.inria.fr">us</a>
for further information.
</p>

<h2>Main participants</h2>

<table>
  <tr>
    <td>Gwena&euml;l Delaval</td>
    <td>Assistant Prof. at <a href="http://www.univ-grenoble-alpes.fr/">UGA</a></td>
    <td>+33 4 76 61 54 31</td>
    <td><a href="mailto:gwenael.delaval@inria.fr">mail</a></td>
    <td><a href="http://pop-art.inrialpes.fr/people/delaval/">web</a></td>
  </tr>
  <tr>
    <td>Herv&eacute; Marchand</td>
    <td>Researcher at <a href="http://www.inria.fr/">INRIA</a></td>
    <td>+33 2 99 84 75 09</td>
    <td><a href="mailto:herve.marchand@inria.fr">mail</a></td>
    <td><a href="http://www.irisa.fr/prive/hmarchan/">web</a></td>
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
