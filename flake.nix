{
  description = "A dev shell with scala-cli and Java 21";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    plutus.url = "github:input-output-hk/plutus/914b7f3108362cfa925810af8082d2ad5564c7b2";
  };

  outputs = { self, nixpkgs, flake-utils, plutus, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        patchedUplc = plutus.${system}.plutus.library.plutus-project.hsPkgs.plutus-core.components.exes.uplc.overrideAttrs (oldAttrs: {
          patches = oldAttrs.patches or [] ++ [ ./uplc.patch ];
          patchFlags = [ "-p2" ];
        });

      in
      {
        devShell = pkgs.mkShell {
          nativeBuildInputs = [
            pkgs.scala-cli
            pkgs.jdk19
            patchedUplc
          ];
          # Set any environment variables or shell hooks if needed
          # Example:
          # shellHook = ''
          #   export JAVA_HOME=${pkgs.openjdk17}
          # '';
        };
      }
    );
}
