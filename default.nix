## Specification for nix-build

let
  environment = import ./misc/nix/environment.nix;
in environment.buildEnv {
  name = "ufcoq";
  paths = environment.packages;
}

### End of file
