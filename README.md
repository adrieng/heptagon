# Heptagon/BZR

Heptagon is a synchronous dataflow language whose syntax and semantics is
inspired from [Lustre](http://www-verimag.imag.fr/Synchrone,30.html),
with a syntax allowing the expression of control structures (e.g., switch or
mode automata).

Heptagon is also a research compiler, whose aim is to facilitate
experimentation. The current version of the compiler includes the following
features:
- **Inclusion of *discrete controller synthesis* within the
  compilation**: the language is equipped with a behavioral contract
  mechanisms, where assumptions can be described, as well as an "enforce"
  property part. The semantics of this latter is that the property should be
  enforced by controlling the behaviour of the node equipped with the
  contract. This property will be enforced by an automatically built controller,
  which will act on free controllable variables given by the programmer. This
  extension has been named [BZR](http://bzr.inria.fr) in previous
  works.
- **Expression and compilation of array values with modular memory
  optimization.** The language allows the expression and operations on
  arrays (access, modification, iterators). With the use of *location annotations*, the
  programmer can avoid unnecessary array copies.

  Heptagon is developed in
  the [Parkas (ENS)](http://www.di.ens.fr/ParkasTeam.html)
  and [Ctrl-A (LIG/INRIA)](http://team.inria.fr/ctrl-a) research teams.


## How to get it or try it

### Installation with OPAM

The easiest and recommended way to install Heptagon/BZR is to use
the OCaml Package Manager (OPAM).

The installation sequence using OPAM is :
1. Install OPAM (at least v2.0) : the procedure depends on your system and is
        described [on the OPAM webpage](http://opam.ocaml.org/doc/Install.html).
2. (optional, for the graphical simulator) Install
        the *gtk2.0* libraries (on debian systems, the package is
        named `libgtk2.0-dev`)
3. Initialize OPAM:
        ```
          opam init
        ```
        This command should install a version of OCaml at least ≥
        4.08. Follow the instructions given throughout this initialization.
4. Install Heptagon:
        ```opam install heptagon```

To use the controller synthesis tool ReaX with Heptagon/BZR :
1. Install the *mpfr* and *gmp* libraries (on debian
        systems, packages named `libmpfr-dev`
        and `libgmp-devel`)
2. Add the repository for ReaX and its libraries (named here
      nberth-repo) :
      ```
        opam repo add nberth-repo "http://nberth.space/opam-repo"
        opam update
      ```
3. Install ReaX and its libraries, and the BZReaX script:
      ```opam install bzreax```

The source code is also available from [the Heptagon/BZR repository](https://gitlab.inria.fr/synchrone/heptagon) for manual
      compilation and installation. Further indications about ReaX can
      be found on [the ReaX/ReaTk page](http://reatk.gforge.inria.fr).

### Manual installation
#### Download

Heptagon can be freely downloaded [here](https://gitlab.inria.fr/synchrone/heptagon).

#### Technical requirements

The use of the Heptagon compiler by itself does not require any
additional tools. However, the usual use involves a compiler for the
generated code (target languages are currently C or Java).

To manually compile and install the Heptagon compiler, the following tools and libraries are needed:
- ocamlfind
- The *menhir* tool
- The *ocamlgraph* library
- *camlp4*
- The *lablgtk* library (optional, for the graphical simulator)
- The *reatk* library (optional, for the backend towards the ReaX controller synthesis too)

The tools below are optional or are related to some subparts of Heptagon:
- The graphical display tool sim2chro can be obtained from
      [Verimag](https://www-verimag.imag.fr/The-Lustre-Toolbox.html). It can be used together with Heptagon's graphical simulator.

#### Compilation and installation

Once the previously described libraries and tools are installed, the Heptagon compiler and libraries can be installed with:
```
    ./configure
    make
    make install
```
