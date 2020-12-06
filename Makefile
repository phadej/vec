.PHONY : build doctest ghcid-fin ghcid-vec

build :
	cabal new-build --enable-tests --enable-benchmarks all

doctest :
	doctest --fast -fdiagnostics-color=never ral/src
	doctest --fast -fdiagnostics-color=never bin/src
	doctest --fast -fdiagnostics-color=never fin/src
	doctest --fast -fdiagnostics-color=never vec/src
	doctest --fast -fdiagnostics-color=never vec-lens/src
	doctest --fast -fdiagnostics-color=never ral-lens/src
	doctest --fast -fdiagnostics-color=never vec-optics/src
	doctest --fast -fdiagnostics-color=never ral-optics/src

ghcid-fin :
	ghcid -c 'cabal new-repl fin' -C fin

ghcid-vec :
	ghcid -c 'cabal new-repl vec' -C vec

deps.png :
	cabal build --disable-tests --disable-benchmarks -w ghc-8.6.5 --dry-run all
	cabal-plan dot --tred --tred-weights --hide-builtin --output deps.png --run-dot-png

deps-mini.png :
	cabal build --disable-tests --disable-benchmarks -w ghc-8.6.5 --dry-run all --constraint="vec -semigroupoids" --constraint="vec -adjunctions" --constraint="vec -distributive"  --constraint="ral -semigroupoids" --constraint="ral -adjunctions" --constraint="ral -distributive"
	cabal-plan dot --tred --tred-weights --hide-builtin --output deps-mini.png --run-dot-png --root vec --root fin --root dec --root bin --root ral

stats :
	for pkg in bin dec fin ral vec ral-lens vec-lens; do echo $$pkg; find $$pkg/src -type f -name '*.hs' | xargs wc; done
