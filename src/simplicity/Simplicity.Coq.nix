{ coq, lib, vst, stdenv }:
stdenv.mkDerivation {
  name = "Simplicity-coq-0.0.0";
  src = lib.sourceFilesBySuffices
      (lib.sourceByRegex ./Coq ["_CoqProject" "Simplicity" "Simplicity/.*" "Util" "Util/.*"])
    ["_CoqProject" ".v"];
  postConfigure = ''
    coq_makefile -f _CoqProject -o CoqMakefile
  '';
  buildInputs = [ coq ];
  propagatedBuildInputs = [ vst ];
  enableParallelBuilding = true;
  makefile = "CoqMakefile";
  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";
  meta = {
    license = lib.licenses.mit;
  };
}
