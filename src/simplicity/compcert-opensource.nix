{ stdenv, lib, fetchurl
, coq, flocq, ocaml, menhir, menhirLib, findlib
, ccomp-platform ? if stdenv.isDarwin then "x86_64-macosx" else "x86_64-linux"
}:

assert lib.versionAtLeast ocaml.version "4.05";
assert lib.versionAtLeast coq.coq-version "8.8";

stdenv.mkDerivation {
  pname = "compcert";
  version = "3.9";

  src = fetchurl {
    url = "https://github.com/AbsInt/CompCert/archive/v3.9.tar.gz";
    sha256 = "1yxf2w8wsv6bik2diljb4is6izcygh20h6islkmpdrxnqbjb8mka";
  };

  # Unpack only those files that are open source licensed (GPL2 or GPL3).
  unpackPhase = ''
    tar -xf $src --wildcards --no-wildcards-match-slash \
      'CompCert*/MenhirLib' \
      'CompCert*/lib' \
      'CompCert*/common' \
      'CompCert*/cfrontend/C2C.ml' \
      'CompCert*/cfrontend/Clight.v' \
      'CompCert*/cfrontend/ClightBigstep.v' \
      'CompCert*/cfrontend/Cop.v' \
      'CompCert*/cfrontend/CPragmas.ml' \
      'CompCert*/cfrontend/Csem.v' \
      'CompCert*/cfrontend/Cstrategy.v' \
      'CompCert*/cfrontend/Csyntax.v' \
      'CompCert*/cfrontend/Ctypes.v' \
      'CompCert*/cfrontend/Ctyping.v' \
      'CompCert*/cfrontend/PrintClight.ml' \
      'CompCert*/cfrontend/PrintCsyntax.ml' \
      'CompCert*/backend/Cminor.v' \
      'CompCert*/backend/PrintCminor.ml' \
      'CompCert*/cparser' \
      'CompCert*/exportclight' \
      'CompCert*/*/Archi.v' \
      'CompCert*/*/Builtins1.v' \
      'CompCert*/*/CBuiltins.ml' \
      'CompCert*/*/extractionMachdep.v' \
      'CompCert*/extraction/extraction.v' \
      'CompCert*/configure' \
      'CompCert*/Makefile' \
      'CompCert*/Makefile.extr' \
      'CompCert*/Makefile.menhir' \
      'CompCert*/LICENSE' \
      'CompCert*/README.md' \
      'CompCert*/VERSION'
    cd CompCert*
    mkdir doc
  '';

  patches = [ ./compcert-opensource.patch ];

  buildInputs = [ ocaml findlib coq menhir menhirLib ];
  propagatedBuildInputs = [ flocq ];

  enableParallelBuilding = true;

  configurePhase = ''
    ./configure \
      -bindir $out/bin \
      -libdir $out/lib \
      -install-coqdev \
      -use-external-Flocq \
      -coqdevdir $out/lib/coq/${coq.coq-version}/user-contrib/compcert \
      -ignore-coq-version \
      ${ccomp-platform}
  '';

  preBuild = "make depend";
  buildFlags = [ "proof" "exportclight/Clightdefs.vo" "compcert.config" ];

  meta = with lib; {
    description = "Formally verified C compiler";
    homepage    = "http://compcert.inria.fr";
    license     = licenses.gpl3; # These particular files are all gpl3 compatible.
    platforms   = [ "x86_64-linux" "x86_64-darwin" ];
  };
}
