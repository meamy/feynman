.PHONY: feynman
feynman:
	cabal build exe:feynman
	cp dist/build/feynman/feynman ./feynman
