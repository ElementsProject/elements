{stdenv, fetchgit, secp256k1git} :
stdenv.mkDerivation {
  name = "libsecp256k1.o";
  src = fetchgit {
    url = secp256k1git;
    rev = "40140d544dfa3d96d57adbad466bae97659e0140"; # simplicity branch
    sha256 = "1cpc5jrx83sf7d7zk0yaykr1f49wgv4gv5xfa69xd4bq71k33hkx";
  };

  buildPhase = ''
    gcc -fPIC -c src/field_10x26_impl.c src/field_impl.c src/group_impl.c src/scalar_8x32_impl.c src/scalar_impl.c src/ecmult_impl.c  -D SECP256K1_INLINE=inline
  '';

  installPhase = ''
    ld -r *.o -o $out
  '';
}
