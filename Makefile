LATEXMK ?= nix shell nixpkgs\#texlive.combined.scheme-full -c latexmk
LATEXMK_FLAGS ?= -xelatex -interaction=nonstopmode -halt-on-error
SOURCE := passant_code_q13.tex

.PHONY: all check evidence warnings clean distclean

all: passant_code_q13.pdf

check: evidence passant_code_q13.pdf warnings

evidence:
	python3 verification/verify_evidence.py

passant_code_q13.pdf: $(SOURCE)
	$(LATEXMK) $(LATEXMK_FLAGS) $(SOURCE)

warnings: passant_code_q13.pdf
	@if grep -En 'Overfull|Underfull|LaTeX Warning|Package .* Warning|undefined references|Citation .* undefined' passant_code_q13.log; then \
		exit 1; \
	fi

clean:
	$(LATEXMK) -c $(SOURCE)

distclean:
	$(LATEXMK) -C $(SOURCE)
