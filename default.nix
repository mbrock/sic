{ stdenv, haskell, haskellPackages, fetchFromGitHub, AgdaStdlib }:

let
  stdlib = AgdaStdlib.overrideDerivation (x: {
    src = fetchFromGitHub {
      owner = "agda";
      repo = "agda-stdlib";
      rev = "b9c8e02597751a1b15045cbc5108c221999bd540";
      sha256 = "0d9galdgijnc8cr9b1mj6wqra51l4vhd0na4sh4nblgmklxj0bbn";
    };
  });

  dapphub = import (fetchFromGitHub {
    owner = "dapphub";
    repo = "nixpkgs-dapphub";
    rev = "bd743f6a4a864325cd22a2bc766aa4881972b3be";
    sha256 = "0gh5d5a88gx3j7xlwgqw07mh9l0s2mbrbrris324dpkbj365sskx";
    fetchSubmodules = true;
  }) {};

in stdenv.mkDerivation rec {
  name = "sic-${version}";
  version = "1.0";
  contract = "Example";

  src = ./.;
  buildInputs =
    [(dapphub.haskellPackages.ghcWithPackages
      (x: with x; [ieee754 text hevm bytestring base16-bytestring]))];

  buildPhase = ''
    ${haskellPackages.Agda}/bin/agda --compile ${contract}.agda \
       -i ${stdlib}/share/agda
    mkdir html
    ${haskellPackages.Agda}/bin/agda --html ${contract}.agda \
       --html-dir=html -i ${stdlib}/share/agda
  '';

  installPhase = ''
    mkdir -p "$out"/{bin,sic}
    cp ${contract} "$out/bin"
    cp -r html "$out/sic/${contract}"
  '';
}
