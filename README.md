# bee2-agda
Agda FFI bindings to Haskell [bee2-hs](https://github.com/semenov-vladyslav/bee2-hs.git) library.

## Build & Install
While compiling and building executables we need to tell `agda` where to find `bee2-hs`. 
There are two ways to do it. 
1. Tell `agda` to not call `ghc` with `--ghc-dont-call-ghc` flag and then build haskell files with `ghc`, `cabal` or `stack`. 
At this point the project lacks cabal and stack.yaml files, so this approach is not easy.
2. Provide `ghc-flag`s to `agda` which would specify where to find `bee2-hs`. 

Let's run the latter approach. First, you need to manually follow build instructions for `bee2-hs` with `cabal` sandboxes. 
```
cd bee2-agda
# specify compile-dir in order to reuse already compiled agda-files
# specify `-package-db` flag for ghc, use package-db from your sandbox, it's name will differ depending on your machine architecture, OS and `ghc` version
> agda -c app/bee2.agda --compile-dir=../.agda-ghc --ghc-flag=-package-db=../.cabal-sandbox/x86_64-windows-ghc-8.2.2-packages.conf.d
# bee2 executable should be built, let's try it
> ../.agda-ghc/bee2
```

