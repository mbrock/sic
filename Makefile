all: build html
build:; nix-build shell.nix -o out
html:; rm -rf docs && cp -r --no-preserve=ownership out/sic/Example docs && chmod +w docs
