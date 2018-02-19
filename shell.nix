{ nixpkgs ? import <nixpkgs> {} }:
let
  dapphub = import (
    (import <nixpkgs> {}).fetchFromGitHub {
      owner = "dapphub";
      repo = "nixpkgs-dapphub";
      rev = "bd743f6a4a864325cd22a2bc766aa4881972b3be";
      sha256 = "0gh5d5a88gx3j7xlwgqw07mh9l0s2mbrbrris324dpkbj365sskx";
      fetchSubmodules = true;
    }
  ) {};
  drv = dapphub.callPackage (import ./default.nix) {};
in
  if dapphub.lib.inNixShell then drv.env else drv
