### Nix expression for the environment for the project

let
  nixpkgsPath = builtins.fetchTarball {
    ## github:NixOS/nixpkgs, nixpkgs-unstable branch, 2021-05-12
    url = "https://github.com/NixOS/nixpkgs/archive/4d8dd0afd2d5a35acb5e34c5c7b1674b74173d87.tar.gz";
    sha256 = "1d7z53vzq9jjy0dmq8w952dlxvajxrbmbn9926yhfp610p93ns84";
  };
  nixpkgs = import nixpkgsPath {};
  coq = nixpkgs.coq;
  ocamlPackages = with coq.ocamlPackages; [
    dune_2
    findlib
    ocaml
    zarith
  ];
  coqPackages = [ coq ] ++ ocamlPackages;
  generalPackages = with nixpkgs; [ gawk recutils ];
  packages = coqPackages ++ generalPackages;
in {
  inherit (nixpkgs) buildEnv mkShell;
  inherit packages;
}

### End of file
