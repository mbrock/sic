{ nixpkgs ? import <nixpkgs> {} }:
let
  pkgs = import (
    (import <nixpkgs> {}).fetchFromGitHub {
      owner = "NixOS";
      repo = "nixpkgs-channels";
      rev = "831ef4756e372bfff77332713ae319daa3a42742";
      sha256 = "1rbfgfp9y2wqn1k0q00363hrb6dc0jbqm7nmnnmi9az3sw55q0rv";
    }
  ) {};
in
  pkgs.callPackage (import ./default.nix) {}
