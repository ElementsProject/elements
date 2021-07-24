{ lib, stdenv }:
stdenv.mkDerivation {
  name = "libSimplicity-0.0.0";
  src = lib.sourceFilesBySuffices ./C ["Makefile" ".c" ".h"];
  doCheck = true;
  meta = {
    license = lib.licenses.mit;
  };
}
