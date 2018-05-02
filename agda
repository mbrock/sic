#!/usr/bin/env bash
nix run -f ./agda.nix -c agda "$@"
