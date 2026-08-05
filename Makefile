# The tracked PDF is byte-reproducible: the pinned epoch fixes the timestamps TeX
# and the PDF writer would otherwise embed, so two builds of one source agree even
# at different filesystem paths.  verification/check_manuscript_build.py compares a
# fresh build against the tracked PDF and is the supported way to refresh it.
export SOURCE_DATE_EPOCH = 1767225600
export FORCE_SOURCE_DATE = 1

# The pinned toolchain: same nixpkgs revision as every other paper, so the tracked
# PDF is reproducible here, in a standalone mirror, and on another machine.
TEXSHELL ?= nix develop .\#manuscript --command
LATEXMK ?= $(TEXSHELL) latexmk
LATEXMK_FLAGS ?= -xelatex -interaction=nonstopmode -halt-on-error
SOURCE := passant_code_q13.tex

.PHONY: all check evidence manuscript warnings clean distclean

all: passant_code_q13.pdf

check: evidence manuscript

evidence:
	python3 verification/verify_evidence.py

passant_code_q13.pdf: $(SOURCE)
	$(LATEXMK) $(LATEXMK_FLAGS) $(SOURCE)

manuscript:
	$(TEXSHELL) python3 verification/check_manuscript_build.py

warnings: passant_code_q13.pdf
	@if grep -En 'Overfull|Underfull|LaTeX Warning|Package .* Warning|undefined references|Citation .* undefined' passant_code_q13.log; then \
		exit 1; \
	fi

clean:
	$(LATEXMK) -c $(SOURCE)

distclean:
	$(LATEXMK) -C $(SOURCE)
