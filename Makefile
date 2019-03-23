.PHONY : build doctest ghcid-fin ghcid-vec

build :
	cabal new-build --enable-tests --enable-benchmarks all

doctest : build
	for ghcenv in .ghc.environment.*; do grep -Ev 'base-compat-[0-9]' $$ghcenv > .ghc.env; mv .ghc.env $$ghcenv; done
	doctest --fast -fdiagnostics-color=never fin/src
	doctest --fast -fdiagnostics-color=never vec/src

ghcid-fin :
	ghcid -c 'cabal new-repl fin' -C fin

ghcid-vec :
	ghcid -c 'cabal new-repl vec' -C vec
