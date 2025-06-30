all: agda

agda:
	agda --latex --only-scope-checking PolyP30.lagda
	latexmk -pdf -cd latex/PolyP30

quickly:
	agda --latex --only-scope-checking PolyP30.lagda
	latexmk -e "\$$max_repeat=1" -pdf -cd latex/PolyP30

