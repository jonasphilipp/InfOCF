
{
  description = "A work environment flake for SAT solving, data analysis, and web development";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          config = {
            allowUnfree = true;
          };
        };


        antlr4_9_3 = pkgs.antlr4.overrideAttrs (oldAttrs: rec {
          version = "4.9.3";
          src = pkgs.fetchurl {
            url = "https://www.antlr.org/download/antlr-${version}-complete.jar";
           sha256 = "sha256-r81AlG095NgeKNfIjUZyieBYcoXSetsXKuzFSUoX3zY=";
          };
        });

        antlr4_13_2 = pkgs.antlr4.overrideAttrs (oldAttrs: rec {
          version = "4.13.2";
          src = pkgs.fetchurl {
            url = "https://www.antlr.org/download/antlr-${version}-complete.jar";
           sha256 = "sha256-6uLfoRmmQydERnKv9j6ew1ogGA3FuAkLemq4USXfTXY=";
          };
        });

        coreEnv = import ./core-env.nix { inherit pkgs antlr4_13_2; };

        nvimConfig = import ./nvim-config.nix { inherit pkgs; };

        mkShell = { withNeovim ? false }: pkgs.mkShell {
          buildInputs = coreEnv.buildInputs ++ (if withNeovim then nvimConfig.nvimDependencies else []);
          shellHook = coreEnv.shellHook + (if withNeovim then nvimConfig.nvimEnvSetup else "");
        };

      in {
        devShells = {
          default = mkShell { withNeovim = false; };
          withNeovim = mkShell { withNeovim = true; };
        };
      }
    );
}

