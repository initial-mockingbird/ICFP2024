{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    haskell-flake.url = "github:srid/haskell-flake";
    ghc-wasm.url = "git+https://gitlab.haskell.org/ghc/ghc-wasm-meta"; 
    
    singletons-base.url = "github:/initial-mockingbird/singletons/d6c49e43e25c73540446a220148acf796be42409";
    singletons-base.flake = false;

    singletons-base_3_3.url = "github:/initial-mockingbird/singletons/d6c49e43e25c73540446a220148acf796be42409";
    singletons-base_3_3.flake = false;

    singletons.url = "github:/initial-mockingbird/singletons/545265e028d8c63b10be0f034a1c2641df831e2c";
    singletons.flake = false;

    singletons-th.url = "github:/initial-mockingbird/singletons/545265e028d8c63b10be0f034a1c2641df831e2c";
    singletons-th.flake = false;
  };
  outputs = inputs@{ self, nixpkgs, flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = nixpkgs.lib.systems.flakeExposed; 
      imports = [ inputs.haskell-flake.flakeModule];

      perSystem = { self', pkgs, config, ... }: 
        let 
          stack-wrapped = pkgs.symlinkJoin {
            name = "stack"; # will be available as the usual `stack` in terminal
            paths = [ pkgs.stack ];
            buildInputs = [ pkgs.makeWrapper ];
            postBuild = ''
              wrapProgram $out/bin/stack \
                --add-flags "\
                  --no-nix \
                  --system-ghc \
                  --no-install-ghc \
                "
            '';
          };
        in {

        haskellProjects.default = {
          basePackages = pkgs.haskell.packages.ghc982;
          packages = {
            #singletons-base.source     = inputs.singletons-base;
            #singletons-base_3_3.source = inputs.singletons-base_3_3;
            #singletons.source          = inputs.singletons;
            #singletons-th.source       = inputs.singletons-th;
          };
          settings = {
             #singletons-base = {
              #check = false;
             #};
             #singletons-base_3_3 = {
              #check = false;
             #};

             #singletons = {
              #check = false;
             #};

             #singletons-th = {
              #check = false;
             #};
          };
          devShell = {
            hlsCheck.enable = true;
            hoogle = true;

           };
          autoWire = [ "packages" "apps" "checks" ];

        };
        packages.default = self'.packages.ICFP2024;

        devShells.default = pkgs.mkShell {
          name = "haskell-template";
          meta.description = "Haskell development environment";
          inputsFrom = [
            config.haskellProjects.default.outputs.devShell
          ];
          nativeBuildInputs = 
            [ inputs.ghc-wasm.packages.${pkgs.system}.all_9_8
              stack-wrapped
              pkgs.hpack
              pkgs.just
            ];
        };
      };
    };
}
