# Paper IV: the q=13 passant code

This is the authoritative manuscript root for Paper IV of the Clebsch program.
Its working title is *Minimum-word reconstruction of PG(2,13) from a binary
conic code*.

Paper IV owns the standalone coding theorem extracted from the computational
companion to Paper I: the minimum distance, the four minimum-word orbits,
exact weighted-pair reconstruction of the code and full marked conic plane,
toric--octahedral minimum geometry, the hidden operator field, the span of
the code by each orbit, and the exact coordinate-permutation automorphism
group. Paper I may summarize and cite this theorem, but future versions
should not retain a second full proof.

The manuscript is `passant_code_q13.tex`. Build and check it with:

    make check

The proof is human and structural. Exact theta and moment certificates replace
the former weight-eight subset and weight-ten syndrome leaves. The
verification surface under `verification/` checks those certificates, the
minimum layer, pair-only reconstruction, homogeneous geometry, ambient plane,
and hidden field. The semantic and paper-owned Lean packages formalize the
structural implications and bounded q=13 leaves recorded in the trust table.
Release still requires replacing the repository-relative Lean dependency with
a pinned public dependency, replaying both bundles from fresh isolated
checkouts, and inserting their immutable artifact locators.
