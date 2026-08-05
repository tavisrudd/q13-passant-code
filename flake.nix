{
  description = "Pinned toolchains for building and verifying the papers";

  # One nixpkgs revision for every paper. A manuscript build is byte-reproducible only
  # when both the clock and the toolchain are fixed: pinning SOURCE_DATE_EPOCH alone
  # leaves the TeX engine version free, and that version determines the producer string
  # and the font subset tags. A paper resolving TeX from the mutable flake registry
  # rebuilds to different bytes whenever the registry moves, which turns a byte-equality
  # staleness check into a false alarm against a correct tracked PDF.
  #
  # This file is copied verbatim into each paper, and into each standalone paper
  # repository by the exporter, so every paper and every mirror builds against the same
  # revision. Change the revision deliberately: every tracked PDF must then be rebuilt.
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  };

  outputs = { nixpkgs, ... }:
    let
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" ];
      forAllSystems = nixpkgs.lib.genAttrs systems;
    in {
      # A shell per capability set rather than one union shell: Singular and Macaulay2
      # are large closures, and a reader rebuilding a manuscript should not realise a
      # computer algebra system that paper never invokes. Nix builds only the shell
      # entered, so naming the right one keeps each paper's dependency honest.
      devShells = forAllSystems (system:
        let
          pkgs = nixpkgs.legacyPackages.${system};
          base = with pkgs; [ python3 texlive.combined.scheme-full git coreutils ];
        in {
          # Manuscript build and stdlib-only verification.
          default = pkgs.mkShell { packages = base; };
          manuscript = pkgs.mkShell { packages = base; };

          # Adds Singular, for papers whose verification runs ideal computations.
          manuscript-cas = pkgs.mkShell {
            packages = base ++ [ pkgs.singular ];
          };

          # Adds Macaulay2 alongside Singular.
          manuscript-cas-full = pkgs.mkShell {
            packages = base ++ [ pkgs.singular pkgs.macaulay2 ];
          };

          # Adds poppler-utils, for papers whose checks read the rendered PDF.
          manuscript-pdf = pkgs.mkShell {
            packages = base ++ [ pkgs.poppler_utils ];
          };

          # Adds sympy to the Python environment.
          manuscript-sympy = pkgs.mkShell {
            packages = with pkgs;
              [ (python3.withPackages (ps: [ ps.sympy ]))
                texlive.combined.scheme-full git coreutils ];
          };
        });
    };
}
