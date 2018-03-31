{ stdenv, haskell, haskellPackages, fetchFromGitHub, AgdaStdlib, z3 }:

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

  ds-token = "${dapphub.dappsys.ds-token}/dapp/ds-token";

in stdenv.mkDerivation rec {
  name = "sic-${version}";
  version = "1.0";
  contract = "Example";

  src = ./.;
  buildInputs =
    [z3
     (dapphub.haskellPackages.ghcWithPackages (x: with x; [
       ieee754 text hevm bytestring base16-bytestring lens
       hedgehog
     ]))
    ];

  buildPhase = ''
    result=$(z3 math.z3)
    test $result = unsat
    ${haskellPackages.Agda}/bin/agda --compile ${contract}.agda \
       -i ${stdlib}/share/agda
  '';

  doCheck = true;
  checkPhase = ''
    export EXAMPLE_CODE=$(./${contract} | tr -d '\n')
    export TOKEN_FACTORY_CODE=$(cat ${ds-token}/out/DSTokenFactory.bin | tr -d '\n')
    export DAPP_ROOT=${ds-token}
    export DAPP_FILE=${ds-token}/out/factory.sol.json
    runghc Test.hs
    output=$(set -x; runghc TestFail.hs) || true
    if message=$(grep passed <<<"$output"); then
      echo $'\e[31m'"$message"$'\e[0m'
      exit 1
    else
      message=$(grep -E -o '[0-9]+ failed.' <<<"$output")
      echo $'\e[32m'"  ✓ $message"$'\e[0m'
    fi
  '';

  installPhase = ''
    mkdir html
    ${haskellPackages.Agda}/bin/agda --html ${contract}.agda \
       --html-dir=html -i ${stdlib}/share/agda
    mkdir -p "$out"/{bin,sic}
    cp ${contract} "$out/bin"
    cp -r html "$out/sic/${contract}"
  '';
}
