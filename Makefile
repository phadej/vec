.PHONY : build doctest ghcid-fin ghcid-vec

build :
	cabal new-build --enable-tests --enable-benchmarks all

doctest :
	doctest --fast -fdiagnostics-color=never ral/src
	doctest --fast -fdiagnostics-color=never bin/src
	doctest --fast -fdiagnostics-color=never fin/src
	doctest --fast -fdiagnostics-color=never vec/src

ghcid-fin :
	ghcid -c 'cabal new-repl fin' -C fin

ghcid-vec :
	ghcid -c 'cabal new-repl vec' -C vec

deps.png :
	cabal build --disable-tests --disable-benchmarks -w ghc-8.6.5 --dry-run all
	cabal-plan dot --tred --tred-weights --hide-builtin --output deps.png --run-dot-png
