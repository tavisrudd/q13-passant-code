# Reconstructing PG(2,13), its conic, and polarity from the minimum words of a binary conic code

[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.21783971-blue.svg)](https://doi.org/10.5281/zenodo.21783971)

[Read the paper (PDF).](passant_code_q13.pdf)

Let C be a nonsingular conic in PG(2,13), and form the binary incidence code on
its 78 internal points using the 78 passant lines.  The paper proves that this
code has parameters [78,36,12]_2 and exactly 364 minimum words.  Their weighted
pair concurrences alone reconstruct the passant incidence matrix, the code, and
the six-class elliptic association scheme; the resulting group action then
reconstructs every point and line of PG(2,13), the distinguished conic, and its
polarity, with no coordinates and no triple concurrence.  Equivalently, the
weighted 2-section of the minimum-support hypergraph is a complete invariant of
this marked conic-plane presentation.

The four minimum-word families are one octahedral family and three
chord-indexed punctured-conic families, and each one spans the code.
Structurally the code is 12-dimensional over a canonical operator field F_8,
and that hidden scalar action is what explains why every minimum-word family
spans.  Exact positive-semidefinite and line-moment certificates exclude
weights eight and ten, replacing the corresponding subset and syndrome
searches.

The theorem is a standalone coding result, developed from the computational
companion of *Reconstructing the Clebsch code and its golden orientation from
its deep-hole syndrome locus* (concept DOI
[`10.5281/zenodo.21650878`](https://doi.org/10.5281/zenodo.21650878)).  Reading
that paper is not needed here. This is Paper IV of the *The Clebsch cubic*
series; the broader five-paper Clebsch portfolio also contains the companion
MDS--CSS transversal-groups paper. The papers share context but are logically
independent entry points.

## Building and checking

The manuscript is `passant_code_q13.tex`.  From this directory:

    make check

This runs the evidence verifier, builds the PDF, and fails on any LaTeX
warning.  The evidence programs use only the Python standard library; the PDF
build uses a Nix-pinned TeX environment.

## Verification surface

The proof is human and structural.  Exact theta and moment certificates replace
the earlier weight-eight subset and weight-ten syndrome searches.  Everything
under `verification/` checks those certificates together with the minimum
layer, pair-only reconstruction, homogeneous geometry, the ambient plane, and
the hidden field; `verification/README.md` describes each program and states
which claims rest on exact execution rather than on a proof.

## Formal companion

The Lean development is deposited separately and is not part of this version.
The current release intentionally excludes the formal companion; a future
version will add it. Until then, the trust table in the
manuscript is the authority on which claims are kernel-checked Lean theorems,
compiled-evaluation leaves, exact executions, or explicit human transports.

## License

CC BY 4.0.  See `LICENSE`.
