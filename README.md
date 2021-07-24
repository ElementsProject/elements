# Simplicity

Simplicity is a blockchain programming language designed as an alternative to Bitcoin script.

The language and implementation is still under development.

## Contents

This project contains

* A Haskell implementation of Simplicity's language semantics, type inference engine, serialization functions, and some example Simplicity code.
* A Coq implementation of Simplicity's formal denotational and operational semantics.

## Build

### Building with Nix

Software artifacts can be built using [Nix](https://nixos.org/nix/).

* To build the Haskell project, run `nix-build -A haskell`.
* To use the Haskell project, try `nix-shell -p "(import ./default.nix {}).haskellPackages.ghcWithPackages (pkgs: [pkgs.Simplicity])"`.
* To build the Coq project, run `nix-build -A coq`.

### Building without Nix

#### Building the Coq project

These instructions assume you start within the `simplicity` root directory of this repository.

Coq 8.12.0 is most easily installed via [opam](https://opam.ocaml.org/) by following the instruction at <https://coq.inria.fr/opam-using.html>.

1. Install `opam` using your distribution's package manager.
1. `opam init`
1. `eval $(opam env)`
1. `opam pin -j$(nproc) add coq 8.12.0`
1. `opam install -j$(nproc) coqide # optional step`

Next we use opam to install the [CompCert](http://compcert.inria.fr/) dependency

1. `opam repo add coq-released https://coq.inria.fr/opam/released`
1. `opam install -j$(nproc) coq-compcert.3.7+8.12~coq_platform~open_source`

While the [VST](https://vst.cs.princeton.edu/) dependency is available via opam, we need a custom build.

1. `wget -O - https://github.com/PrincetonUniversity/VST/archive/v2.6.tar.gz | tar -xvzf -`
1. `cd VST-2.6`
    1. `make -j$(nproc) default_target sha`
    1. `make install`
    1. `install -d $(coqc -where)/user-contrib/sha`
    1. `install -m 0644 -t $(coqc -where)/user-contrib/sha sha/*.v sha/*.vo`
    1. `cd ..`

Now we can build (and install) the Simplicity Coq library.

1. `cd Coq`
    1. `coq_makefile -f _CoqProject -o CoqMakefile`
    1. `make -f CoqMakefile -j$(nproc)`
    1. `make -f CoqMakefile install # optional`
    
## Documentation

Detailed documentation can be found in the `Simplicity-TR.tm` TeXmacs file.
A recent PDF version can be found in the [pdf](https://github.com/ElementsProject/simplicity/blob/pdf/Simplicity-TR.pdf) branch.

## Further Resources

* Our [paper that originally introduced Simplicity](https://arxiv.org/abs/1711.03028).  Some of the finer details are out of date, but it is still a good introduction.
* [BPASE 2018 presentation](https://youtu.be/VOeUq3oR2fk) of the above paper ([slides](https://cyber.stanford.edu/sites/g/files/sbiybj9936/f/slides-bpase-2018.pdf)).
* [Scale by the Bay 2018 presentation](https://youtu.be/M4XnDrRIKx8) that illustrates formal verification of Simplicity in Agda ([slides](https://lists.ozlabs.org/pipermail/simplicity/2018/000011.html)).

## Contact

Interested parties are welcome to join the [Simplicity mailing list](https://lists.ozlabs.org/listinfo/simplicity).
Issues and pull-requests can be made through GitHub's interface.
