# Verification surface for the q=13 passant code

This directory is the paper-owned trust boundary for Paper IV. The human
structural proof is primary. Evidence records discovery and discharges only
finite terminal leaves that have not admitted useful conceptual compression.
Within that hierarchy, the release verifier distinguishes five modes:

1. human structural proof;
2. published theorem imported by pinpoint citation;
3. kernel-checked Lean theorem;
4. compact finite certificate checked by a proved or transparent checker; and
5. independent trusted exact execution.

The current `claim_map.json` records the structural source claims and their
present trust modes. `evidence_manifest.json` records both the original
Paper-I migration and the paper-owned structural certificates, including
paths, byte counts, hashes, commands, and replay relationships. The
paper-owned Lean package, distributed separately from the manuscript and
recorded in the manifest under `lean-certificates/`, together with the shared semantic library, checks the q=13 coordinate
semantics, transports the normalized weight-eight reduction to the cyclic tangent graph, checks
both weight-ten syndrome profiles, and checks four displayed minimum-word orbits.  Its fixed-point
weight-twelve leaf exhausts the four pencil-profile domains and identifies their 56 solutions with
the four disjoint 14-support orbit slices; the point stabilizer acts transitively on each slice.
Its association transport proves that every displayed orbit spans the rho-zero kernel.
Its formal scope is strictly smaller than the complete release theorem.
The old normalized weight-eight terminal is retained as an independent
semantic transport; the theorem-facing bound now uses the exact theta
certificate and its kernel-checked quadratic-form implication. The old
weight-ten syndrome shards are likewise retained as an independent replay;
the theorem-facing proof uses the global moment and stabilizer certificates.
The normalized transport terminals remain
`RelativeConicArcs.Gates.PassantCodeQ13.weightEight_semantic_transport`.
The arbitrary-word weight-ten profile terminal is
`RelativeConicArcs.Gates.PassantCodeQ13.arbitrary_weightTen_profile_transport`.

## Derived evidence programs

Four programs here were copied from the computational companion of
*Reconstructing the Clebsch code and its golden orientation from its deep-hole
syndrome locus* (concept DOI
[`10.5281/zenodo.21650878`](https://doi.org/10.5281/zenodo.21650878)) and then
adapted:

- `check_q13_tangent_code.py`, from that companion's q=13 tangent-code program;
- `generate_weight_ten_profiles.py`, from its q=13 weight-ten profile
  generator;
- `weight_ten_profiles.json`, from the corresponding weight-ten profile
  certificate;
- `replay_weight_ten_profiles.py`, from its independent weight-ten replay.

`evidence_manifest.json` records, for each of the four, the SHA-256 digest of
the exact antecedent it was copied from together with the digest of the file as
it now stands, so the derivation stays checkable against any published revision
of the companion. These files are regular files owned by this paper. Later
changes must keep paper-local names and semantics, preserve those antecedent
digests, and refresh the current-file digests.

The current paper-local entry points are:

- `generate_weight_ten_profiles.py --check` for the canonical certificate;
- `replay_weight_ten_profiles.py` for the independent dynamic program; and
- `check_q13_tangent_code.py` for the full exact replay.

Inside the separately distributed formal package,
`generate_rank_transport.py --check` regenerates, byte-identically, the
recovery and expansion masks used by the semantic rank theorem.
- `verify_weight_eight_theta.py --check weight_eight_theta.json` for the exact rank-28 PSD and
  equality-kernel certificate;
- `verify_weight_ten_moment.py --check weight_ten_moment.json` for the global moment and two
  stabilizer leaves;
- `verify_pair_reconstruction.py --check pair_reconstruction.json` for exact arity-two recovery;
- `verify_minimum_geometry.py --check minimum_geometry.json` for the toric--octahedral families;
- `verify_ambient_plane.py --check ambient_plane.json` for the Sylow/involution plane; and
- `verify_hidden_field.py --check hidden_field.json` for the compact operator-field theorem.

Run all three together, after checking the manifest hashes and byte counts,
with `python3 verify_evidence.py`.

## Lean release layout

The shared Lean library contains these semantic, reusable modules:

```text
RelativeConicArcs/ConicPassantCode.lean
RelativeConicArcs/PassantCodeQ13/Geometry.lean
RelativeConicArcs/PassantCodeQ13/Rank.lean
RelativeConicArcs/PassantCodeQ13/WeightEight.lean
RelativeConicArcs/PassantCodeQ13/WeightTen.lean
RelativeConicArcs/PassantCodeQ13/AssociationAlgebra.lean
RelativeConicArcs/PassantCodeQ13/Reconstruction.lean
RelativeConicArcs/PassantCodeQ13/StructuralUpgrade.lean
RelativeConicArcs/Gates/PassantCodeQ13.lean
```

The paper-owned standalone Lake package contains finite leaves partitioned by
mathematical role rather than build chronology:

```text
PassantCodeQ13/WeightTen/IsolatedProfile/Fibre0.lean ... Fibre6.lean
PassantCodeQ13/WeightTen/CycleProfile/Residue0.lean ... Residue6.lean
PassantCodeQ13/WeightTen/Aggregate.lean
PassantCodeQ13/MinimumWords/OrbitS4.lean
PassantCodeQ13/MinimumWords/OrbitDihedral.lean
PassantCodeQ13/MinimumWords/Exhaustion.lean
PassantCodeQ13/MinimumWords/Reconstruction.lean
PassantCodeQ13/AssociationTransport/Base.lean
PassantCodeQ13/AssociationTransport/RelationSquares/RhoZero.lean
PassantCodeQ13/AssociationTransport/RelationSquares/Nine.lean
PassantCodeQ13/AssociationTransport/RelationSquares/Ten.lean
PassantCodeQ13/AssociationTransport/RelationSquares/Twelve.lean
PassantCodeQ13/AssociationTransport/RelationSquares.lean
PassantCodeQ13/AssociationTransport/OrbitS4.lean
PassantCodeQ13/AssociationTransport/OrbitDihedralA.lean
PassantCodeQ13/AssociationTransport/OrbitDihedralB.lean
PassantCodeQ13/AssociationTransport/OrbitDihedralC.lean
PassantCodeQ13/AssociationTransport.lean
PassantCodeQ13/Automorphisms/Base.lean
PassantCodeQ13/Automorphisms/TripleOrbit.lean
PassantCodeQ13/Automorphisms/FourthAnchor.lean
PassantCodeQ13/Automorphisms/Signatures.lean
PassantCodeQ13/Automorphisms/Transport.lean
PassantCodeQ13/Gates/Main.lean
PassantCodeQ13/Gates/AxiomAudit.lean
PassantCodeQ13/StructuralUpgrade.lean
```

The public aggregate transports its exact 42-column elimination certificate to semantic rank and
code dimension, transports every supported point of every weight-ten word to one of the two
exhaustive pencil profiles, and checks the fixed-point weight-twelve exhaustion against the four
projective orbit slices.  The fixed-point stabilizer acts transitively on each 14-support slice.
Eight bounded association leaves, joined by one generic parity-to-matrix theorem, identify the four
orbit Grams and prove that every orbit row space equals the kernel of the rho-zero relation matrix.
Polarity identifies that matrix with the incidence matrix up to row order.  The passage from the
fixed point to the global 364-support layer remains
the human projective-transitivity and double-count argument.  The aggregate also identifies every
automorphism of the six-valued polar-relation scheme with one of the 2184 normalized
symmetric-square projective maps.  The passage from support-hypergraph automorphisms to
polar-relation automorphisms remains the human concurrence transport.  Its axiom report comes
from the pinned toolchain's actual `#print axioms` output. Task identifiers,
manuscript section numbers, private reports, and workflow status language are
forbidden from module names, declaration names, comments, and generated
banners.

## Semantic mirror and finite-leaf target

The preferred endpoint is a semantic Lean mirror of the human mechanisms,
with kernel checking at irreducibly finite leaves. It should eventually
establish, apart from Mathlib's standard logical axioms:

- the binary code has length 78, dimension 36, and minimum distance 12;
- its minimum layer has 364 words in the stated four orbits;
- each orbit spans the code;
- weighted pairs recover the six elliptic relations, 78 incidence rows, code,
  and full marked conic plane;
- the resulting coordinate-permutation automorphism group is
  `PGL(2,13)`.

This formal surface is supporting evidence, not the manuscript's narrative
spine. It should preserve the human mechanisms. In particular, it
formalizes the tangent-graph reduction and theta implication in weight eight,
the global moment compression in weight ten, pair-neighborhood reconstruction,
three toric parities, the hidden cubic, both normalized projective-plane
uniqueness axioms, the mod-two association-algebra spanning argument, and the
anchor proof of the elliptic-scheme automorphism group. Exact PSD positivity,
stabilizer tables, and the group-theoretic Sylow/involution census remain
named paper-owned trusted leaves.
It should not replace the entire theorem by an opaque enumeration of
`2^78` words.
