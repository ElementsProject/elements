{stdenv, fetchgit, secp256k1git} :
stdenv.mkDerivation {
  name = "libsecp256k1.o";
  src = fetchgit {
    url = secp256k1git;
    rev = "ae5e0b5f8ad5909f4003cf865b68934f241050f4"; # simplicity branch
    sha256 = "0697fpp2ss6ghzzlna6qkl8ysj8kzkqvif5w99gnax7b55ga9r7k";
  };

  buildPhase = ''
    gcc -fPIC -c src/field_10x26_impl.c src/field_impl.c src/group_impl.c src/scalar_8x32_impl.c src/ecmult_impl.c  -D SECP256K1_INLINE=inline
  '';

  installPhase = ''
    ld -r *.o -o $out
  '';
}
