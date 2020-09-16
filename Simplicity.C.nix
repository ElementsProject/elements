{ lib, stdenv, gperf, libsha256compression }:
stdenv.mkDerivation {
  name = "libSimplicity-0.0.0";
  src = lib.sourceFilesBySuffices ./C ["Makefile" ".c" ".h" ".gperf"];
  nativeBuildInputs = [ gperf ];
  buildInputs = [ libsha256compression ];
  doCheck = true;
  meta = {
    license = lib.licenses.mit;
  };
}
