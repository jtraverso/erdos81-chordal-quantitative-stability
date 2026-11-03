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
| `corollary_6_1a` | Corollary 6.1a | One clique root satisfies all the conclusions of Theorem 6.1 and, for it, every partition with at most `M(n) + τ` pieces has at most `τ + 48δ` noncanonical pieces. |
| `identity_6_7b` | (6.7b) | The root-defect identity. |
| `corollary_6_2` | Corollary 6.2 | For large `n`, the extremal chordal graphs are the complete-split graphs with a core of optimal size, and `cp = c₄ = M(n)` on them. |
| `theorem_C` | Theorem C | For each `s` and large `n`, every graph on `n` vertices with rooted simplicial defect at most `s` has a partition of order at most four with at most `Q_s(n)` pieces, and the bound is attained by one that is optimal among all clique partitions. |
| `theorem_C_prime` | Theorem C′ | Fixed-defect same-root stability with `A_s = 2·10⁴¹·(s + 1)⁸`: edit distance at most `A_s δ` to a template, baseline gap at most `(1 + 4A_s)δ`, at most `τ + (1 + 7A_s)δ` noncanonical pieces carrying at most `10τ + 10(1 + 7A_s)δ` edges. |
| `corollary_6_3`, `corollary_6_3_equality` | Corollary 6.3 | (6.17) some optimal-size template is at edit distance at most `A_s δ + n·√((1 + 4A_s)δ)`; (6.18) for large `n`, `cp = Q_s(n)` iff `c₄ = Q_s(n)` iff `G` is an extremal template. |
| `proposition_6_3a`, `proposition_6_3a_deficit_one` | Proposition 6.3a | The square-root term is necessary: graphs with `cp = c₄ = Q_s(n) − (d² + C(d,2))` far from every optimal-size template, and no bound linear in the deficit. |
| `proposition_6_4`, `proposition_6_4_integral` | Proposition 6.4 | `F₄(G) ≤ M(n − s) + ns` (minus `C(s + 1, 2)` when `4s ≤ n`), and its integral form up to `εn²` with a threshold independent of `s`. |
| `theorem_6_5_partition_bound`, `theorem_6_5_stability` | Theorem 6.5 | For sublinear defect: partitions with `|Q| ≤ n²/6 + o(n²)`, and a clique root controlling every near-optimal partition. |
| `corollary_6_6`, `corollary_6_6_sMax` | Corollary 6.6 | If `T(P(S)) ≤ n` (explicit tower `T`, polynomial `P`), the bound `Q_s(n)` holds for every `s ≤ S`; in particular for every `s ≤ s_max(n)`. |
| `chordal_gap_linear_cliqueFree` | Annex, (G.1) | A chordal graph with no clique on `d + 2` vertices has fractional triangle packing number at most `ν₃(G) + (10 + d/2)·n`. |

## Files

- [`PaperIVChallenge.lean`](PaperIVChallenge.lean): the definitions and the 21 statements; it
  imports only Mathlib. Chordality is the definition of the registered entry
  [chordal-split-threshold-graphs](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-18-000006&version=1),
  copied verbatim; the other definitions are copied from the library.
- [`PaperIVSolution.lean`](PaperIVSolution.lean): the same definitions, the bridges (clique
  partitions and packings converted field by field) and the 21 theorems.
- `PaperIV/` (312 modules), `PaperIVExt/` (180), `MixedRounding/` (4), `PaperI/` (3): the library,
  the author's Lean freeze of Paper IV. `PaperIVExt/` holds the freeze's root-level modules (fixed
  defect, §6.7) and, in `PaperIVExt/BoundedCliqueGap/`, the bounded-clique-gap annex.
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

Corollary 3.5, Theorem 5.0, Corollary 5.4 and Proposition D.3 are proved in the library but not
stated in the Challenge.

## Version 2

Version 1 (PALOMAR-2026-11-01-000021) had the eight statements from Theorem A to Corollary 6.2.
Version 2 adds Theorem C, Theorem C′, Corollary 6.3, Proposition 6.3a, the uniform bounds of §6.7
(Proposition 6.4, Theorem 6.5, Corollary 6.6) and the main inequality (G.1) of the bounded-clique-gap
annex; the eight statements of version 1, their definitions and their modules are unchanged.

## Provenance and checks

The library is the author's Lean freeze of Paper IV (`piv-v12-fb459343d234`, Lean 4.28): 317 of the
version 1 modules come from the Lean 4.35 port in the series Note II, the other 37 from the freeze;
of the 213 modules added in version 2, 176 come from the freeze and the 37 of the annex from
`preprints/PAPER_IV/05_formalization/lean_v1.0_gap_annex` of the series repository (Lean 4.28).
Everything is ported to Lean `v4.35.0-rc3` and the module system. Besides the replacements above and the
normalized headers, the changes are: `private` removed from two example definitions used in
public statements (`SplitUniformIncidence`), one missing tactic import (`OneFactorization`), two
structure fields given by their defining terms instead of `simpa` (`PhysicalToCliquePartition`,
`SplitCompleteExactValue`), and four proofs of `ChordalCopy` taken from the registered Paper II
(PALOMAR-2026-10-29-000004), where the freeze used `grind` with library suggestions. In the
version 2 modules: module names under `PaperIVExt.`, the nibble and clique-tree imports and names
redirected to the registered entries, adaptations to the current Mathlib API (renamed lemmas,
`SimpleGraph` symmetry and irreflexivity as `Std.Symm`/`Std.Irrefl`, curried `Sym2.mk`, deprecated
`if_pos`/`push_neg` forms, `classical` for local decidability instances), and local proof
repairs where the new elaborator or kernel behaves differently
(`E19/GateBounds`: exponents kept symbolic for the kernel; `E34/Gavril`, `E34/L11Claim2`,
`E34/L11Main`, `BoundedCliqueGap/QChordalTree`, `BoundedCliqueGap/THMaster`: rewriting steps made
explicit). Lean
`v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```
lake exe cache get
lake build
```

No `sorry`; `#print axioms` gives only `propext`, `Classical.choice` and `Quot.sound` for the 21
theorems; the elaborated statements and definitions of `PaperIVChallenge.lean` and
`PaperIVSolution.lean` are identical (`pp.all`).
