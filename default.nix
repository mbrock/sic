{ stdenv, haskell, haskellPackages, fetchFromGitHub, AgdaStdlib }:

let stdlib = AgdaStdlib.overrideDerivation (x: {
  src = fetchFromGitHub {
    owner = "agda";
    repo = "agda-stdlib";
    rev = "b9c8e02597751a1b15045cbc5108c221999bd540";
    sha256 = "0d9galdgijnc8cr9b1mj6wqra51l4vhd0na4sh4nblgmklxj0bbn";
  };
}); in

stdenv.mkDerivation rec {
  name = "sic-${version}";
  version = "1.0";
  contract = "Example";

  src = ./.;
  buildInputs =
    [(haskell.packages.ghc822.ghcWithPackages
      (x: with x; [ieee754 text]))];
  buildPhase = ''
    ${haskellPackages.Agda}/bin/agda --compile ${contract}.agda \
       -i ${stdlib}/share/agda
    ${haskellPackages.Agda}/bin/agda --html-dir=docs ${contract}.agda \
       -i ${stdlib}/share/agda
  '';
  installPhase = ''
    mkdir -p "$out"/{bin,sic}
    cp Example "$out/bin"
    cp -r docs "$out/sic/${contract}"
    ./Example > "$out/sic/${contract}/${contract}.evm"
  '';
}
