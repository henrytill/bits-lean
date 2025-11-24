{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    utils.url = "github:numtide/flake-utils";
  };
  outputs =
    {
      self,
      nixpkgs,
      utils,
      ...
    }:
    utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ ];
        };
      in
      {
        packages.default = pkgs.stdenv.mkDerivation {
          name = "bits-lean";
          src = self;

          nativeBuildInputs = with pkgs; [ lean4 ];

          buildPhase = ''
            lake build
            lake pack build-archive.tar.gz
          '';

          installPhase = ''
            mkdir -p $out
            tar -xzf build-archive.tar.gz -C $out
          '';
        };

        devShells.default = pkgs.mkShell {
          inputsFrom = [ self.packages.${system}.default ];
          packages = with pkgs; [ yaml-language-server ];
        };
      }
    );
}
