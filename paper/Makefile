MAIN = main
OUT  = build

.PHONY: all clean watch
all:
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=$(OUT) $(MAIN).tex

watch:
	latexmk -pdf -pvc -interaction=nonstopmode -outdir=$(OUT) $(MAIN).tex

clean:
	latexmk -C -outdir=$(OUT) $(MAIN).tex
	rm -rf $(OUT)
