{ stdenv, haskell, haskellPackages, fetchFromGitHub, AgdaStdlib, z3 }:

let
  stdlib =
    AgdaStdlib.overrideDerivation (
      _: {
        src = fetchFromGitHub {
          owner = "agda";
          repo = "agda-stdlib";
          rev = "b9c8e02597751a1b15045cbc5108c221999bd540";
          sha256 = "0d9galdgijnc8cr9b1mj6wqra51l4vhd0na4sh4nblgmklxj0bbn";
        };
      }
    );

  dapphub =
    import (
      fetchFromGitHub {
        owner = "dapphub";
        repo = "nixpkgs-dapphub";
        rev = "56ad3e95da873ad3a24a9b76fe5391832b5c138c";
        sha256 = "0dazyfwkanh4jcmb9ylphb22j4snj9v07yrx4a36gdkz0bfh31zb";
        fetchSubmodules = true;
      }
    ) {};

  coins =
    let
      src = fetchFromGitHub {
        owner = "rainbreak";
        repo = "coins";
        rev = "245952cc906d3fbb94981115d374e742c6748e07";
        sha256 = "13jfl3fn5kjdsaa16wq8k7801kvn3ks9i954bwavkw3587h0ij10";
      };
    in
      dapphub.callSolidityPackage (
        { dappsys }:
          dapphub.solidityPackage {
            name = "coins";
            deps = with dappsys; [ds-test ds-token];
            src = "${src}/src";
          }
      ) {};

  aux =
    let
      src = ./solidity;
    in
      dapphub.callSolidityPackage (
        { dappsys }:
          dapphub.solidityPackage {
            name = "aux";
            deps = [dappsys.ds-token];
            inherit src;
          }
      ) {};

  coins-root =
    "${coins}/dapp/coins";
  aux-root =
    "${aux}/dapp/aux";

in
  stdenv.mkDerivation rec {
    name = "sic-${version}";
    version = "1.0";
    contract = "Example";
    src = ./.;

    buildInputs =
      let
        ghc =
          dapphub.haskellPackages.ghcWithPackages (
            x: with x; [
              base16-bytestring
              bytestring
              hedgehog
              hevm
              ieee754
              lens
              silently
              text
            ]
          );
      in
        [z3 ghc];

    buildPhase = ''
      result=$(z3 math.z3)
      test $result = unsat

      ${haskellPackages.Agda}/bin/agda \
         --compile ${contract}.agda \
         -i ${stdlib}/share/agda
    '';

    doCheck = true;
    checkPhase = ''
      ${envPhase}
      runghc Test.hs
      output=$(set -x; runghc TestFail.hs) || true
      if message=$(grep ✓ <<<"$output"); then
        echo $'\e[31m'"$message"$'\e[0m'
        exit 1
      else
        echo -n $'\e[32m'
        grep ✗ <<<"$output"
        echo -n $'\e[0m'
      fi
    '';

    envPhase =
      let
        solidity =
          root: name:
            "$(cat ${root}/out/${name}.bin | tr -d '\n')";
      in ''
        export EXAMPLE_CODE=$(./${contract} | tr -d '\n')
        export BIN_CODE=${solidity coins-root "Bin"}
        export PIE_CODE=${solidity aux-root "Pie"}
        export DAPP_ROOT=${coins-root}
        export DAPP_FILE=${coins-root}/out/frob.t.sol.json
      '';

    ghci = ''
      ${envPhase}
      ghci Test.hs
    '';

    installPhase = ''
      mkdir html
      ${haskellPackages.Agda}/bin/agda \
         --html ${contract}.agda \
         --html-dir=html \
         -i ${stdlib}/share/agda
      mkdir -p "$out"/{bin,sic}
      cp ${contract} "$out/bin"
      cp -r html "$out/sic/${contract}"
    '';
  }
