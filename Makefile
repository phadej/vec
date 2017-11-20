.PHONY : build doctest ghcid-fin ghcid-vec

build :
	cabal new-build --enable-tests --enable-benchmarks all

doctest : build
	mkdir -p tmp
	python cabal-new-install.py doctest doctest tmp
	tmp/doctest --fast -fdiagnostics-color=never fin/src
	tmp/doctest --fast -fdiagnostics-color=never vec/src

ghcid-fin :
	ghcid -c 'cabal new-repl fin' -C fin

ghcid-vec :
	ghcid -c 'cabal new-repl vec' -C vec
