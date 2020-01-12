{ pkgs ? import <nixpkgs> {}
, hp ? pkgs.haskellPackages
, lfc ? import ./core { inherit pkgs hp; }
}:

hp.callPackage ({ mkDerivation, transformers, mtl, lfc }:
mkDerivation {
  pname = "lens-family";
  version = "2.0.0";
  src = pkgs.fetchdarcs {
    url = https://hub.darcs.net/roconnor/lens-family;
    context = ./lens-family.context;
    sha256 = "1ska853yfby58cnqk876xr9khq21ni4s8xaq583lq7c4cb83m6s1";
  };
  buildDepends = [ transformers mtl lfc ];
  license = pkgs.lib.licenses.bsd3;
})
{ inherit lfc; }
