feyn: src/*.hs src/frontends/*.hs
	cabal build
	cp dist/build/feyn/feyn ./feyn
