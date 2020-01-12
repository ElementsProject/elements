{ mkDerivation, base, binary, cereal, lens-family, lib, MemoTrie, mtl, QuickCheck, stdenv, SHA, split, tasty, tasty-hunit, tasty-quickcheck, unification-fd, vector }:
mkDerivation (rec {
  pname = "Simplicity";
  version = "0.0.0";
  src = lib.sourceFilesBySuffices
      (lib.sourceByRegex ./. ["^LICENSE$" "^Simplicity\.cabal$" "^Setup.hs$" "^Tests.hs$" "^Haskell$" "^Haskell/.*"])
    ["LICENSE" ".cabal" ".hs" ".hsig"];
  libraryHaskellDepends = [ base binary cereal lens-family MemoTrie mtl SHA split unification-fd vector ];
  testHaskellDepends = libraryHaskellDepends ++ [ QuickCheck tasty tasty-hunit tasty-quickcheck ];
  testTarget = ''--test-option="--quickcheck-replay=582534"'';

  # Cabal's haddock doesn't work for Backpack / internal libraries / modules reexports.
  # Until that is fix we manually generate some documentation pages
  haddockFlags = ["--haddock-option='--use-contents=index.html'"];
  postInstall = ''
    cp ${./manual-index.html} $doc/share/doc/${pname}-${version}/html/index.html
    cp ${./Simplicity-Primitive.html} $doc/share/doc/${pname}-${version}/html/Simplicity-Primitive.html
  '';

  license = stdenv.lib.licenses.mit;
})
