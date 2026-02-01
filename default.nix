{ pkgs ? import <nixpkgs> {} }:

pkgs.stdenv.mkDerivation
{
  name = "FormalSystems";

  src = pkgs.lib.cleanSource ./.;

  enableParallelBuilding = true;

  buildInputs =
  [
    pkgs.coq_8_20
    pkgs.coqPackages_8_20.equations
  ];

  buildPhase =
  ''
    patchShebangs build.sh
    ./build.sh
    rm -f makefile makefile.conf .makefile.d
  '';

  installPhase =
  ''
    INSTALLPATH=$out/lib/coq/${pkgs.coq_8_20.coq-version}/user-contrib/FormalSystems
    mkdir -p $INSTALLPATH
    cp -r * $INSTALLPATH
  '';
}
