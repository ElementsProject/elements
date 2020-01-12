{ lib, stdenv }:
stdenv.mkDerivation {
  name = "libsha256compression";
  src = lib.sourceFilesBySuffices ./. ["Makefile" ".c" ".h"];
  meta = {
    license = lib.licenses.mit;
  };
}
