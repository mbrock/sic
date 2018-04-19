all: build
nix:; nix-build shell.nix -o out
html:; rm -rf docs && cp -r --no-preserve=ownership out/sic/Example docs && chmod +w docs
test:; nix-shell --command 'eval "$$checkPhase"'
ghci:; nix-shell --command 'eval "$$ghci"'
build:; nix-shell --command 'eval "$$buildPhase"'
