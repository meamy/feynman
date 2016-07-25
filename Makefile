feyn: src/*.hs src/frontends/*.hs
	cabal build feyn
	cp dist/build/feyn/feyn ./feyn

prof: src/*.hs src/frontends/*.hs
	cabal build feyn-prof
	cp dist/build/feyn-prof/feyn-prof ./feyn-prof
