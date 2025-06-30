all: agda

agda:
	agda --latex --only-scope-checking PolyP30.lagda
	latexmk -pdf -cd latex/PolyP30

quickly:
	agda --latex --only-scope-checking PolyP30.lagda
	latexmk -e "\$$max_repeat=1" -pdf -cd latex/PolyP30

submit1: agda
	-mkdir tex
	cp latex/splncs04.bst \
           latex/agda.sty	  \
           latex/llncs.cls	  \
           latex/PolyP30.bbl  \
           latex/PolyP30.tex  \
           tex

submit2: submit1
	latexmk -pdf -cd tex/PolyP30

