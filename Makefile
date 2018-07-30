.PHONY: feynman
feynman:
	cabal build exe:feyn
	cp dist/build/feyn/feyn ./feyn
