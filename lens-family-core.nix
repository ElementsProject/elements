{ pkgs ? import <nixpkgs> {}
, hp ? pkgs.haskellPackages
}:
hp.callPackage ({mkDerivation, stdenv, transformers}:
mkDerivation {
  pname = "lens-family-core";
  version = "2.0.0";
  src = pkgs.fetchdarcs {
    url = https://hub.darcs.net/roconnor/lens-family;
    context = ./lens-family.context;
    sha256 = "1ska853yfby58cnqk876xr9khq21ni4s8xaq583lq7c4cb83m6s1";
  };
  prePatch = "cd core";
  buildDepends = [ hp.transformers ];
  license = stdenv.lib.licenses.bsd3;
}) {}
