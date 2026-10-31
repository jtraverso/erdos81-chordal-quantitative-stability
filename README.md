# Clique partitions of chordal graphs: quantitative stability and sharp eventual bounds (Erdős #81, Paper IV) in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

A Lean 4 / Mathlib formalization of the chordal results of the preprint *Clique partitions with
rooted simplicial defect: quantitative stability and sharp eventual bounds* (Erdős #81 series,
Paper IV, preprint v1.24.1; series repository
[jtraverso/erdos-81-chordal-clique-partitions](https://github.com/jtraverso/erdos-81-chordal-clique-partitions),
`preprints/PAPER_IV`; Zenodo [doi:10.5281/zenodo.23479507](https://doi.org/10.5281/zenodo.23479507)).

A clique partition of `G` is a family of cliques with at least two vertices whose edge sets are
pairwise disjoint and cover the edges of `G`; `M(n) = ⌊n(n+1)/6⌋`. Erdős Problem #81 asks for a
bound `n²/6 + O(n)` on the clique partition number of chordal graphs.

| Lean (namespace `ErdosPaperIV`) | Paper | Statement |
|---|---|---|
| `theorem_A` | Theorem A | There is `b` such that every chordal graph on `n` vertices has a clique partition into pieces of order at most four with at most `M(n) + b` pieces. |
| `theorem_B` | Theorem B | For `n` large, every chordal graph on `n` vertices has such a partition with at most `M(n)` pieces; some chordal graph on `n` vertices has one with exactly `M(n)` pieces that is optimal among all clique partitions. |
| `quadratic_constant_isLeast` | §6.3 | `1/6` is the least quadratic coefficient. |
| `theorem_3_1` | Theorem 3.1 | Uniform mixed rounding: fractional triangle/`K₄` packings are matched by physical ones up to `εn²`. |
| `theorem_6_1` | Theorem 6.1 | Integral stability: a near-extremal chordal graph has a clique root with explicit outside-edge and missing-incidence bounds and edit distance at most `16δ` to a complete-split graph. |
| `corollary_6_1a` | Corollary 6.1a | For that root, every partition with at most `M(n) + τ` pieces has at most `τ + 48δ` noncanonical pieces. |
| `identity_6_7b` | (6.7b) | The root-defect identity. |
| `corollary_6_2` | Corollary 6.2 | For large `n`, the extremal chordal graphs are the complete-split graphs with a core of optimal size, and `cp = c₄ = M(n)` on them. |

## Files

- [`PaperIVChallenge.lean`](PaperIVChallenge.lean): the definitions and the eight statements; it
  imports only Mathlib. Chordality is the definition of the registered entry
  [chordal-split-threshold-graphs](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-18-000006&version=1),
  copied verbatim; the other definitions are copied from the library.
- [`PaperIVSolution.lean`](PaperIVSolution.lean): the same definitions, the bridges (clique
  partitions and packings converted field by field) and the eight theorems.
- `PaperIV/` (279 modules), `MixedRounding/` (4), `PaperI/` (3): the library, the author's Lean freeze
  of Paper IV.
- [`comparator.json`](comparator.json), [`formalization.yaml`](formalization.yaml).

## Dependencies on registered entries

- [`jtraverso/asymptotic-triangle-packing`](https://github.com/jtraverso/asymptotic-triangle-packing)
  @ `760e503` (PALOMAR-2026-10-15-000011, version 2), pinned. Its nibble
  (`LeanPool.AsymptoticTrianglePacking.Internal`, with the same declarations and namespaces)
  replaces the 60 `Nibble` modules of the freeze; only the 67-line wrapper
  `PaperIV/FracNibbleRepaired.lean` remains.
- [`jtraverso/chordal-split-threshold-graphs`](https://github.com/jtraverso/chordal-split-threshold-graphs)
  @ `ed65dcd` (PALOMAR-2026-10-18-000006), pinned. Chordality, simplicial vertices and Dirac's
  theorem (`GraphClassesLib.Erdos81PaperIIContrib.Chordal`) and clique trees
  (`GraphClassesLib.PaperIVCliqueTree`) replace the freeze's `ChordalStructure` and `CliqueTree`
  modules.

## Not included

Theorem C, Theorem C′, Corollary 6.3, Proposition 6.3a and the uniform bounds of §6.7 (Proposition
6.4, Theorem 6.5, Corollary 6.6) are proved in the freeze but not yet ported. Corollary 3.5, Theorem
5.0, Corollary 5.4 and Proposition D.3 are proved in the library but not stated in the Challenge.
The bounded-clique-gap annex is not included.

## Provenance and checks

The library is the author's Lean freeze of Paper IV (`piv-v12-fb459343d234`, Lean 4.28): 317 of its
modules come from the Lean 4.35 port in the series Note II, the other 37 from the freeze. It is
ported to Lean `v4.35.0-rc3` and the module system. Besides the replacements above and the
normalized headers, the changes are: `private` removed from two example definitions used in
public statements (`SplitUniformIncidence`), one missing tactic import (`OneFactorization`), two
structure fields given by their defining terms instead of `simpa` (`PhysicalToCliquePartition`,
`SplitCompleteExactValue`), and four proofs of `ChordalCopy` taken from the registered Paper II
(PALOMAR-2026-10-29-000004), where the freeze used `grind` with library suggestions. Lean
`v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```
lake exe cache get
lake build
```

No `sorry`; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound` for the eight
theorems; the elaborated statements and definitions of `PaperIVChallenge.lean` and
`PaperIVSolution.lean` are identical (`pp.all`).
