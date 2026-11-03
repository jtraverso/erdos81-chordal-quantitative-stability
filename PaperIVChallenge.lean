/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Clique partitions of chordal graphs: quantitative stability and sharp eventual bounds

J. P. Traverso Gianini, *Clique partitions with rooted simplicial defect: quantitative stability and
sharp eventual bounds*, Erdős #81 series, Paper IV (preprint v1.24.1).

A *clique partition* of `G` (`CliquePartition`) is a finite family of cliques of `G` with at least
two vertices whose edge sets are pairwise disjoint and cover the edges of `G`; its *size* is the
number of pieces, and it has *order at most `r`* if every piece has at most `r` vertices. Put
`M(n) = ⌊n(n+1)/6⌋` (`targetSize`). Chordality (`IsChordal`) is the cycle-based definition of the
registered entry chordal-split-threshold-graphs (PALOMAR-2026-10-18-000006), copied verbatim.

Statements, in the namespace `ErdosPaperIV`:

* `theorem_A`: there is `b` such that every chordal graph on `n` vertices has a clique partition of
  order at most four with at most `M(n) + b` pieces (Theorem A);
* `theorem_B`: for `n` large, every chordal graph on `n` vertices has such a partition with at most
  `M(n)` pieces, and some chordal graph on `n` vertices has one with exactly `M(n)` pieces that is
  optimal among all clique partitions (Theorem B);
* `quadratic_constant_isLeast`: `1/6` is the least `c` with partitions of size `cn² + O(n)` for all
  large chordal graphs (optimality of the quadratic coefficient, §6.3);
* `theorem_3_1`: the uniform mixed rounding target: for every `ε > 0` and every large graph, every
  fractional packing of triangles and `K₄`'s with gains `2` and `5` is matched, up to `εn²`, by an
  edge-disjoint physical packing (Theorem 3.1);
* `theorem_6_1`: integral stability: a large chordal graph all of whose partitions of order at most
  four have at least `M(n) − δ` pieces, `0 ≤ δ ≤ γn²`, has a clique root `R` with
  `splitBaseline n |R| ≤ M(n)`, explicit bounds on its outside edges and missing incidences, and
  edit distance at most `16δ` to the complete-split graph with core `R` (Theorem 6.1);
* `corollary_6_1a`: one clique root satisfies all the conclusions of Theorem 6.1 and, for it,
  every clique partition with at most `M(n) + τ` pieces has at most `τ + 48δ` noncanonical pieces
  (Corollary 6.1a, same root);
* `identity_6_7b`: the root-defect identity `∑_K rootPieceDefect R K = |Q| − splitBaseline n |R|
  + missingIncidences + 3·|outside edges|` (identity (6.7b));
* `corollary_6_2`: for large `n`, a chordal graph has `cp(G) = M(n)` iff `c₄(G) = M(n)` iff it is a
  complete-split graph with a core of optimal size (Corollary 6.2).

Version 2 adds the fixed-defect results of §6.4–§6.7 and the bounded-clique-gap annex. A graph has
*rooted simplicial defect at most `s`* (`RootedDefectAt`) if for every vertex set `U` and every
clique `R ⊆ U` with `U \ R` nonempty, some vertex of `U \ R` has, inside `U`, a neighbourhood
containing a clique that omits at most `s` of its vertices. Put `Q_s(n) = M(n + s) − C(s + 1, 2)`
(`defectTarget`) and `A_s = 2·10⁴¹·(s + 1)⁸` (`stabilityConstant`). The extremal templates are the
graphs `(K_C ⊔ I_D) ∨ I_H` (`defSplitGraph`) with `|D| = s` and `|C| + s` nearest to
`(2(n + s) + 1)/6` (`IsAdmissibleExtremal`).

* `theorem_C`: for each `s` and large `n`, every graph with rooted simplicial defect at most `s`
  has a partition of order at most four with at most `Q_s(n)` pieces, and the bound is attained by
  an optimal partition of some such graph (Theorem C);
* `theorem_C_prime`: same-root stability: if every partition of order at most four has at least
  `Q_s(n) − δ` pieces, `0 ≤ δ ≤ γn²`, one root `(C, D, H)` has edit distance at most `A_s δ` to its
  template, baseline gap at most `(1 + 4A_s)δ`, and every partition with at most `Q_s(n) + τ`
  pieces has at most `τ + (1 + 7A_s)δ` noncanonical pieces carrying at most
  `10τ + 10(1 + 7A_s)δ` edges (Theorem C′);
* `corollary_6_3`: under the same hypotheses some extremal template `T` of optimal size has
  `d_E(G, T) ≤ A_s δ + n·√((1 + 4A_s)δ)` (Corollary 6.3, (6.17));
* `corollary_6_3_equality`: for large `n`, `cp(G) = Q_s(n)` iff `c₄(G) = Q_s(n)` iff `G` is an
  extremal template (Corollary 6.3, (6.18));
* `proposition_6_3a`, `proposition_6_3a_deficit_one`: graphs with `cp = c₄ = Q_s(n) − (d² +
  C(d, 2))` at edit distance at least `nd/4` and `n·√(d² + C(d, 2))/8` from every extremal
  template, and graphs with deficit one arbitrarily far from them (Proposition 6.3a);
* `proposition_6_4`, `proposition_6_4_integral`: the fractional bounds
  `F₄(G) ≤ M(n − s) + ns` and `F₄(G) ≤ M(n − s) + ns − C(s + 1, 2)` (`4s ≤ n`) for all orders, and
  their integral forms up to `εn²` with a threshold independent of `s` (Proposition 6.4);
* `theorem_6_5_partition_bound`, `theorem_6_5_stability`: for sequences with defect `o(n)`,
  partitions with `max(0, |Q| − n²/6) = o(n²)`, and a common root for all near-optimal partitions
  (Theorem 6.5);
* `corollary_6_6`, `corollary_6_6_sMax`: the bound of Theorem C holds at every order
  `n ≥ T(P(S))` for all `s ≤ S`, with `T` the tower of twos and `P(s) = c_T·(s + 1)¹⁶⁸⁰` explicit,
  and for all `s ≤ s_max(n)` (Corollary 6.6);
* `chordal_gap_linear_cliqueFree`: every fractional triangle packing of a chordal graph without
  `K_{d+2}` has value at most `ν₃(G) + (10 + d/2)·n` (bounded clique gap, annex G.1).
-/

@[expose] public section

namespace ErdosPaperIV

open Finset

/-! ### Chordal graphs (registered definition) -/

/-- A graph is **chordal** if every cycle of length `≥ 4` has a chord: an adjacency between two
vertices of the cycle whose edge is not one of the cycle's own edges. -/
def IsChordal {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ ⦃v : V⦄ (c : G.Walk v v), c.IsCycle → 4 ≤ c.length →
    ∃ x y : V, x ∈ c.support ∧ y ∈ c.support ∧ G.Adj x y ∧ s(x, y) ∉ c.edges

/-! ### Clique partitions -/

section Partitions

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The non-diagonal pairs of a vertex set. -/
def pairs (K : Finset V) : Finset (Sym2 V) := K.sym2.filter fun e => ¬ e.IsDiag

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A clique partition of the edges of `G`: nontrivial cliques whose edge sets are pairwise
disjoint and cover every edge. -/
structure CliquePartition where
  pieces : Finset (Finset V)
  isClique : ∀ K ∈ pieces, ∀ a ∈ K, ∀ b ∈ K, a ≠ b → G.Adj a b
  two_le_card : ∀ K ∈ pieces, 2 ≤ K.card
  edgeDisjoint : ∀ K ∈ pieces, ∀ L ∈ pieces, K ≠ L → Disjoint (pairs K) (pairs L)
  covers : pieces.biUnion pairs = G.edgeFinset

variable {G}

/-- The number of pieces. -/
def CliquePartition.size (Q : CliquePartition G) : ℕ := Q.pieces.card

/-- Every piece has at most `r` vertices. -/
def CliquePartition.OrderAtMost (Q : CliquePartition G) (r : ℕ) : Prop :=
  ∀ K ∈ Q.pieces, K.card ≤ r

end Partitions

/-- `M(n) = ⌊n(n+1)/6⌋`. -/
def targetSize (n : ℕ) : ℕ := n * (n + 1) / 6

/-! ### Roots, defects and complete-split graphs -/

section Roots

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The size `p(n − p) − p(p−1)/2` of the canonical partition of a complete-split graph with a core
of size `p`. -/
def splitBaseline (n p : ℚ) : ℚ := p * (n - p) - p * (p - 1) / 2

/-- The vertices outside a root. -/
def outsideVertices (P : Finset V) : Finset V := Finset.univ \ P

/-- The edges of `G` with both ends outside the root. -/
noncomputable def outsideEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter fun e => e.toFinset ⊆ outsideVertices P

/-- The outside vertices not adjacent to the root vertex `x`. -/
noncomputable def missingColumn (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) (x : V) : Finset V := by
  classical
  exact (outsideVertices P).filter fun y => ¬ G.Adj x y

/-- The number of missing root–outside incidences. -/
noncomputable def missingIncidences (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finset V) : ℕ :=
  ∑ x ∈ P, (missingColumn G P x).card

/-- The edit distance between two edge sets. -/
def editDist (A B : Finset (Sym2 V)) : ℕ := (symmDiff A B).card

/-- The edge set of a graph, with classical decidability. -/
noncomputable def graphEdgeSupport (X : SimpleGraph V) : Finset (Sym2 V) := by
  classical
  exact X.edgeSet.toFinset

/-- The complete-split graph with clique `Core` joined to the independent set `Hosts`. -/
def splitGraph (Core Hosts : Finset V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ((x ∈ Core ∧ y ∈ Core) ∨ (x ∈ Core ∧ y ∈ Hosts) ∨ (x ∈ Hosts ∧ y ∈ Core))
  symm := ⟨by
    rintro x y ⟨hne, h⟩
    exact ⟨hne.symm, by tauto⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- A piece is canonical at the root `R` if it has one outside vertex and one or two root
vertices. -/
def IsCanonicalAt (R K : Finset V) : Prop :=
  (K ∩ outsideVertices R).card = 1 ∧
    ((K ∩ R).card = 1 ∨ (K ∩ R).card = 2)

/-- The pieces of `Q` that are not canonical at `R`. -/
noncomputable def noncanonicalPieces {G : SimpleGraph V} [DecidableRel G.Adj] (R : Finset V)
    (Q : CliquePartition G) : Finset (Finset V) := by
  classical
  exact Q.pieces.filter fun K => ¬ IsCanonicalAt R K

/-- The defect `1 + C(a,2) + 3·C(b,2) − ab` of a piece with `a` root and `b` outside vertices. -/
def numericDefect (a b : ℕ) : ℚ :=
  1 + (a.choose 2 : ℚ) + 3 * (b.choose 2 : ℚ) - (a : ℚ) * b

/-- The defect of a piece relative to the root `R`. -/
def rootPieceDefect (R K : Finset V) : ℚ :=
  numericDefect (K ∩ R).card (K ∩ outsideVertices R).card

end Roots

/-- The stability window `γ = 10⁻¹⁶/4` of Theorem 6.1. -/
def gamma : ℚ := 1 / 10 ^ 16 / 4

/-- `k` is an optimal core size for `n` vertices. -/
def OptimalCore (n k : ℕ) : Prop :=
  k = (n + 1) / 3 ∨ (n % 3 = 1 ∧ k = (n + 1) / 3 + 1)

/-- `G` is the complete-split graph of a core of optimal size. -/
def IsOptimalCompleteSplit {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ R : Finset (Fin n), G = splitGraph R (Finset.univ \ R) ∧ OptimalCore n R.card

/-- `cp(G) = t`. -/
def CliqueCoverEq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (t : ℕ) : Prop :=
  (∀ Q : CliquePartition G, t ≤ Q.size) ∧ (∃ Q : CliquePartition G, Q.size = t)

/-- `c₄(G) = t`: the same over partitions of order at most four. -/
def CliqueCover4Eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (t : ℕ) : Prop :=
  (∀ Q : CliquePartition G, Q.OrderAtMost 4 → t ≤ Q.size) ∧
    (∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size = t)

/-! ### Mixed packings of triangles and `K₄`'s -/

section Mixed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An item is a copy of `K₃` or `K₄` in `G`. -/
def IsItem (G : SimpleGraph V) (K : Finset V) : Prop :=
  (∀ a ∈ K, ∀ b ∈ K, a ≠ b → G.Adj a b) ∧ (K.card = 3 ∨ K.card = 4)

instance (G : SimpleGraph V) [DecidableRel G.Adj] (K : Finset V) :
    Decidable (IsItem G K) := by unfold IsItem; infer_instance

/-- The items of `G`. -/
def items (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset V) :=
  Finset.univ.filter fun K => IsItem G K

/-- The gain `C(|K|,2) − 1` of an item: `2` for `K₃`, `5` for `K₄`. -/
def gainOf (K : Finset V) : ℕ := K.card.choose 2 - 1

/-- The gain in a field. -/
def gainF (F : Type*) [Field F] (K : Finset V) : F := (K.card.choose 2 : F) - 1

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A fractional packing: nonnegative weights on the items with load at most `1` on every edge. -/
structure FracPacking where
  weight : Finset V → ℚ
  weight_nonneg : ∀ K, 0 ≤ weight K
  capacity : ∀ e ∈ G.edgeFinset,
    ∑ K ∈ items G, (if e ∈ pairs K then weight K else 0) ≤ 1

variable {G}

/-- The value of a fractional packing. -/
def FracPacking.value (x : FracPacking G) : ℚ := ∑ K ∈ items G, gainF ℚ K * x.weight K

variable (G)

/-- A physical packing: edge-disjoint items. -/
structure Packing where
  pieces : Finset (Finset V)
  isItem : ∀ K ∈ pieces, IsItem G K
  edgeDisjoint : ∀ K ∈ pieces, ∀ L ∈ pieces, K ≠ L → Disjoint (pairs K) (pairs L)

variable {G}

/-- The gain of a physical packing. -/
def Packing.gain (P : Packing G) : ℕ := ∑ K ∈ P.pieces, gainOf K

end Mixed

/-- The uniform rounding target: for large graphs, every fractional mixed packing is matched up to
`ε n²` by a physical packing. -/
def UniformRoundingTarget (ε : ℚ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    ∀ x : FracPacking G, ∃ P : Packing G,
      x.value - (P.gain : ℚ) ≤ ε * (n : ℚ) ^ 2

/-! ### Rooted simplicial defect (version 2) -/

section Defect

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The neighbours of `v` inside `U`. -/
def neighborsIn (U : Finset V) (v : V) : Finset V :=
  U.filter (fun w => G.Adj v w)

/-- Inside `U`, the neighbourhood of `v` contains a clique omitting at most `s` of its vertices. -/
def DefectSimplicialOn (U : Finset V) (s : ℕ) (v : V) : Prop :=
  ∃ C : Finset V, C ⊆ neighborsIn G U v ∧ G.IsClique (C : Set V) ∧
    (neighborsIn G U v).card ≤ C.card + s

/-- **Rooted simplicial defect at most `s`** (Okechukwu): for every vertex set `U` and every clique
`R ⊆ U` with `U \ R` nonempty (the empty root is allowed), some vertex of `U \ R` is defect-`s`
simplicial in `U`. -/
def RootedDefectAt (s : ℕ) : Prop :=
  ∀ U R : Finset V, R ⊆ U → G.IsClique (R : Set V) →
    (U \ R).Nonempty → ∃ v ∈ U \ R, DefectSimplicialOn G U s v

variable {G}

/-- The defective complete-split graph `(K_C ⊔ I_D) ∨ I_H`: `C` is a clique, and every vertex of
`C ∪ D` is joined to every vertex of `H`. -/
def defSplitGraph (Core Def Hosts : Finset V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ((x ∈ Core ∧ y ∈ Core) ∨
    (x ∈ Core ∪ Def ∧ y ∈ Hosts) ∨ (x ∈ Hosts ∧ y ∈ Core ∪ Def))
  symm := ⟨by
    rintro x y ⟨hne, h⟩
    exact ⟨hne.symm, by tauto⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (Core Def Hosts : Finset V) : DecidableRel (defSplitGraph Core Def Hosts).Adj := by
  intro x y
  unfold defSplitGraph
  infer_instance

/-- A root of `G` at defect `s`: a clique `C`, exactly `s` vertices `D` and the rest `H`,
partitioning the vertex set, with `2 ≤ |C| ≤ |H|`. -/
structure IsDefectRoot (G : SimpleGraph V) (s : ℕ) (C D H : Finset V) : Prop where
  disjCD : Disjoint C D
  disjCH : Disjoint C H
  disjDH : Disjoint D H
  cover : ∀ x : V, x ∈ C ∨ x ∈ D ∨ x ∈ H
  clique : G.IsClique (C : Set V)
  card_def : D.card = s
  two_le : 2 ≤ C.card
  core_le_hosts : C.card ≤ H.card

/-- The edit distance from `G` to the template `defSplitGraph C D H`. -/
def rootEdit (G : SimpleGraph V) [DecidableRel G.Adj] (C D H : Finset V) : ℕ :=
  editDist G.edgeFinset (defSplitGraph C D H).edgeFinset

/-- The baseline `(|C| + |D|)·|H| − C(|C|,2)` of the template. -/
def rootBaseline (C D H : Finset V) : ℕ := (C.card + D.card) * H.card - C.card.choose 2

/-- The canonical pieces of the template: an edge between `C ∪ D` and `H`, or a triangle with two
vertices in `C` and one in `H`. -/
def IsCanonicalPiece (C D H K : Finset V) : Prop :=
  (∃ x ∈ C ∪ D, ∃ h ∈ H, x ≠ h ∧ K = {x, h}) ∨
  (∃ c ∈ C, ∃ c' ∈ C, ∃ h ∈ H, c ≠ c' ∧ K = {c, c', h})

/-- The number of edges in the noncanonical pieces of `Q`. -/
noncomputable def defectNoncanonicalEdgeMass {G : SimpleGraph V} [DecidableRel G.Adj]
    (C D H : Finset V) (Q : CliquePartition G) : ℕ := by
  classical
  exact ∑ K ∈ Q.pieces.filter (fun K => ¬ IsCanonicalPiece C D H K), K.card.choose 2

/-- `k` is an integer nearest to `(2m + 1)/6`. -/
def NearestCore (m k : ℕ) : Prop := |(6 * (k : ℤ)) - (2 * (m : ℤ) + 1)| ≤ 3

/-- `G` is, on its own vertex set, an extremal template of defect `s`: `G = defSplitGraph C D H`
with `|D| = s` and `|C| + s` an integer nearest to `(2(n + s) + 1)/6`. -/
def IsAdmissibleExtremal (G : SimpleGraph V) (s : ℕ) : Prop :=
  ∃ C D H : Finset V, Disjoint C D ∧ Disjoint C H ∧ Disjoint D H ∧
    (∀ x : V, x ∈ C ∨ x ∈ D ∨ x ∈ H) ∧ D.card = s ∧
    G = defSplitGraph C D H ∧ NearestCore (Fintype.card V + s) (C.card + s)

/-- The number of edges in the pieces of `Q` that are not canonical at the root `R`. -/
noncomputable def noncanonicalEdgeMass (R : Finset V) (Q : CliquePartition G) : ℕ :=
  ∑ K ∈ noncanonicalPieces R Q, K.card.choose 2

end Defect

/-- `Q_s(n) = M(n + s) − C(s + 1, 2)`. -/
def defectTarget (s n : ℕ) : ℕ := targetSize (n + s) - Nat.choose (s + 1) 2

/-- The stability constant `A_s = 2·10⁴¹·(s + 1)⁸` of Theorem C′. -/
def stabilityConstant (s : ℕ) : ℕ := 2 * 10 ^ 41 * (s + 1) ^ 8

/-- `d² + C(d,2) = (3d² − d)/2`, the deficit of Proposition 6.3a. -/
def displacementDeficit (d : ℕ) : ℕ := d * d + d.choose 2

/-! ### The tower threshold of Corollary 6.6 -/

/-- `T(0) = 1`, `T(j + 1) = 2^T(j)`. -/
def tower2 : ℕ → ℕ
  | 0 => 1
  | m + 1 => 2 ^ tower2 m

/-- `c_poly = 4·17664⁵·9000¹⁰⁵ + 3006`. -/
def cPoly : ℕ := 4 * 17664 ^ 5 * 9000 ^ 105 + 3006

/-- `c_far = c_poly·(128·10⁸²)¹⁰⁵`. -/
def cFar : ℕ := cPoly * (128 * 10 ^ 82) ^ 105

/-- The integer `h` of §6.3. -/
def hIter : ℕ := 4 * 8 ^ 5 * 2208 ^ 5 * 4500 ^ 105 * (2 * 10 ^ 16) ^ 105

/-- `c_T = h + c_far + 841780`. -/
def cT : ℕ := hIter + cFar + 841780

/-- `P(s) = c_T·(s + 1)¹⁶⁸⁰`. -/
def Ptower (s : ℕ) : ℕ := cT * (s + 1) ^ 1680

/-- `s_max(n)`: the largest `S ≤ n` with `T(P(S)) ≤ n` (`0` if there is none). -/
def sMaxT (n : ℕ) : ℕ := Nat.findGreatest (fun S => tower2 (Ptower S) ≤ n) n

/-! ### Fractional triangle packings (the bounded-clique-gap annex) -/

section Triangles

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `T` is a triangle of `G`. -/
def IsTriangle (G : SimpleGraph V) (T : Finset V) : Prop :=
  T.card = 3 ∧ ∀ u ∈ T, ∀ v ∈ T, u ≠ v → G.Adj u v

/-- An edge-disjoint family of triangles of `G`. -/
def IsTrianglePacking (G : SimpleGraph V) (P : Finset (Finset V)) : Prop :=
  (∀ T ∈ P, IsTriangle G T) ∧
  ∀ T ∈ P, ∀ T' ∈ P, T ≠ T' → Disjoint (pairs T) (pairs T')

/-- `ν₃(G)`: the maximum number of edge-disjoint triangles. -/
noncomputable def nu3 (G : SimpleGraph V) : ℕ :=
  sSup {n | ∃ P : Finset (Finset V), IsTrianglePacking G P ∧ P.card = n}

/-- A fractional triangle packing: nonnegative weights supported on triangles with load at most `1`
on every pair. -/
structure TriFracPacking (G : SimpleGraph V) where
  x : Finset V → ℚ
  nonneg : ∀ T, 0 ≤ x T
  supp : ∀ T, x T ≠ 0 → IsTriangle G T
  edge_le_one : ∀ e : Sym2 V, ¬ e.IsDiag →
    ∑ T ∈ Finset.univ.filter fun T => e ∈ pairs T ∧ x T ≠ 0, x T ≤ 1

/-- The total weight of a fractional triangle packing. -/
noncomputable def TriFracPacking.value {G : SimpleGraph V} (F : TriFracPacking G) : ℚ :=
  ∑ T ∈ Finset.univ.filter fun T => F.x T ≠ 0, F.x T

end Triangles

/-! ### Statements -/

/-- **Theorem A (bound for all orders).** There is `b` such that every chordal graph on `n`
vertices has a clique partition of order at most four with at most `M(n) + b` pieces. -/
theorem theorem_A :
    ∃ b : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      IsChordal G → ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize n + b := by
  sorry

/-- **Theorem B (sharp bound and eventual maximum).** For large `n`, every chordal graph on `n`
vertices has a clique partition of order at most four with at most `M(n)` pieces, and some chordal
graph on `n` vertices has one with exactly `M(n)` pieces that is optimal among all clique
partitions. -/
theorem theorem_B :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], IsChordal G →
          ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize n)
        ∧ (∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
            IsChordal G ∧
            ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
              Q.size = targetSize n ∧ ∀ R : CliquePartition G, Q.size ≤ R.size) := by
  sorry

/-- **Optimality of the quadratic coefficient.** `1/6` is the least `c` such that, for some `C`
and all large `n`, every chordal graph on `n` vertices has a clique partition with at most
`cn² + Cn` pieces. -/
theorem quadratic_constant_isLeast :
    IsLeast {c : ℚ | ∃ (C : ℚ) (N : ℕ), ∀ n : ℕ, N ≤ n →
      ∀ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), IsChordal G →
        ∃ Q : CliquePartition G, (Q.size : ℚ) ≤ c * (n : ℚ) ^ 2 + C * (n : ℚ)}
      (1 / 6) := by
  sorry

/-- **Theorem 3.1 (uniform mixed rounding).** For every `ε > 0`, the uniform rounding target
holds. -/
theorem theorem_3_1 (ε : ℚ) (hε : 0 < ε) : UniformRoundingTarget ε := by
  sorry

/-- **Theorem 6.1 (integral stability).** For large `n`, if `G` is chordal and every clique
partition of order at most four has at least `M(n) − δ` pieces, `0 ≤ δ ≤ γn²`, then `G` has a clique
root `R` with `2 ≤ |R| ≤ n − |R|`, `splitBaseline n |R| ≤ M(n)`, the stated bounds on its outside
edges and missing incidences, and edit distance at most `16δ` to the complete-split graph with core
`R`. -/
theorem theorem_6_1 :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      IsChordal G → ∀ δ : ℚ, 0 ≤ δ → δ ≤ gamma * (n : ℚ) ^ 2 →
        (∀ Q : CliquePartition G, Q.OrderAtMost 4 →
            (targetSize n : ℚ) - δ ≤ (Q.size : ℚ)) →
          ∃ R : Finset (Fin n), G.IsClique (R : Set (Fin n)) ∧
            2 ≤ R.card ∧ R.card ≤ (Finset.univ \ R).card ∧
            splitBaseline (n : ℚ) R.card ≤ (targetSize n : ℚ) ∧
            (117 : ℚ) / 1825 * ((outsideEdges G R).card : ℚ) +
              (12687 : ℚ) / 20000 * (missingIncidences G R : ℚ) ≤ δ ∧
            (targetSize n : ℚ) - splitBaseline (n : ℚ) R.card +
              ((outsideEdges G R).card : ℚ) / 16 + (missingIncidences G R : ℚ) / 2 ≤ δ ∧
            (editDist G.edgeFinset
                (graphEdgeSupport (splitGraph R (Finset.univ \ R))) : ℚ) ≤ 16 * δ := by
  sorry

/-- **Corollary 6.1a (stability of partitions), with the root of Theorem 6.1.** Under the
hypotheses of Theorem 6.1 there is one clique root `R` satisfying all the conclusions of Theorem 6.1
such that, moreover, every clique partition with at most `M(n) + τ` pieces has at most `τ + 48δ`
noncanonical pieces. -/
theorem corollary_6_1a :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], IsChordal G →
        ∀ δ : ℚ, 0 ≤ δ → δ ≤ gamma * (n : ℚ) ^ 2 →
          (∀ Q : CliquePartition G, Q.OrderAtMost 4 →
              (targetSize n : ℚ) - δ ≤ (Q.size : ℚ)) →
          ∃ R : Finset (Fin n), G.IsClique (R : Set (Fin n)) ∧
            2 ≤ R.card ∧ R.card ≤ (Finset.univ \ R).card ∧
            splitBaseline (n : ℚ) R.card ≤ (targetSize n : ℚ) ∧
            (117 : ℚ) / 1825 * ((outsideEdges G R).card : ℚ) +
              (12687 : ℚ) / 20000 * (missingIncidences G R : ℚ) ≤ δ ∧
            (targetSize n : ℚ) - splitBaseline (n : ℚ) R.card +
              ((outsideEdges G R).card : ℚ) / 16 + (missingIncidences G R : ℚ) / 2 ≤ δ ∧
            (editDist G.edgeFinset
                (graphEdgeSupport (splitGraph R (Finset.univ \ R))) : ℚ) ≤ 16 * δ ∧
            ∀ (Q : CliquePartition G) (τ : ℚ),
              (Q.size : ℚ) ≤ targetSize n + τ →
              ((noncanonicalPieces R Q).card : ℚ) ≤ τ + 48 * δ := by
  sorry

/-- **Identity (6.7b).** For a clique root `R` and a clique partition `Q`,
`∑_{K ∈ Q} rootPieceDefect R K = |Q| − splitBaseline n |R| + missingIncidences + 3·|outside
edges|`. -/
theorem identity_6_7b {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (R : Finset V) (hR : G.IsClique (R : Set V)) (Q : CliquePartition G) :
    ∑ K ∈ Q.pieces, rootPieceDefect R K =
      (Q.size : ℚ) - splitBaseline (Fintype.card V) R.card
        + missingIncidences G R + 3 * (outsideEdges G R).card := by
  sorry

/-- **Corollary 6.2 (eventual classification).** For large `n`, a chordal graph on `n` vertices
has `cp(G) = M(n)` iff `c₄(G) = M(n)` iff it is a complete-split graph with a core of optimal
size. -/
theorem corollary_6_2 :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      IsChordal G →
        (CliqueCoverEq G (targetSize n) ↔ CliqueCover4Eq G (targetSize n)) ∧
          (CliqueCover4Eq G (targetSize n) ↔ IsOptimalCompleteSplit G) := by
  sorry

/-! ### Fixed rooted simplicial defect (version 2) -/

/-- **Theorem C (fixed rooted simplicial defect).** For each `s`, for large `n` every graph on `n`
vertices with rooted simplicial defect at most `s` has a clique partition of order at most four with
at most `Q_s(n)` pieces, and some such graph has one with exactly `Q_s(n)` pieces that is optimal
among all clique partitions. -/
theorem theorem_C (s : ℕ) :
    ∃ N, ∀ n, N ≤ n →
      (∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], RootedDefectAt G s →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n) ∧
      (∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), RootedDefectAt G s ∧
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size = defectTarget s n ∧
          ∀ R : CliquePartition G, Q.size ≤ R.size) := by
  sorry

open Classical in
/-- **Theorem C′ (fixed-defect same-root stability).** For each `s` there are `N` and `γ > 0` such
that, for `n ≥ N`, if `G` has rooted simplicial defect at most `s` and every clique partition of
order at most four has at least `Q_s(n) − δ` pieces, `0 ≤ δ ≤ γn²`, then one root `(C, D, H)`
satisfies `d_E(G, T) ≤ A_s δ` and `0 ≤ Q_s(n) − baseline ≤ (1 + 4A_s)δ`, and every clique partition
with at most `Q_s(n) + τ` pieces has at most `τ + (1 + 7A_s)δ` noncanonical pieces, with at most
`10τ + 10(1 + 7A_s)δ` edges in them; `A_s = 2·10⁴¹·(s + 1)⁸`. -/
theorem theorem_C_prime (s : ℕ) :
    ∃ N : ℕ, ∃ γ : ℚ, 0 < γ ∧ ∀ n : ℕ, N ≤ n →
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], RootedDefectAt G s →
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ (γ : ℝ) * (n : ℝ) ^ 2 →
          (∀ Q : CliquePartition G, Q.OrderAtMost 4 → (defectTarget s n : ℝ) - δ ≤ Q.size) →
          ∃ C D H : Finset (Fin n), IsDefectRoot G s C D H ∧
            (rootEdit G C D H : ℝ) ≤ (stabilityConstant s : ℝ) * δ ∧
            0 ≤ (defectTarget s n : ℝ) - rootBaseline C D H ∧
            (defectTarget s n : ℝ) - rootBaseline C D H ≤
              (1 + 4 * (stabilityConstant s : ℝ)) * δ ∧
            ∀ (Q : CliquePartition G) (τ : ℝ), (Q.size : ℝ) ≤ defectTarget s n + τ →
              ((Q.pieces.filter fun K => ¬ IsCanonicalPiece C D H K).card : ℝ) ≤
                τ + (1 + 7 * (stabilityConstant s : ℝ)) * δ ∧
              (defectNoncanonicalEdgeMass C D H Q : ℝ) ≤
                10 * τ + 10 * (1 + 7 * (stabilityConstant s : ℝ)) * δ := by
  sorry

/-- **Corollary 6.3, (6.17) (optimal-size comparison).** Under the hypotheses of Theorem C′, some
extremal template `T_*` of optimal size satisfies
`d_E(G, T_*) ≤ A_s δ + n·√((1 + 4A_s)δ)`. -/
theorem corollary_6_3 (s : ℕ) :
    ∃ N : ℕ, ∃ γ : ℚ, 0 < γ ∧ ∀ n : ℕ, N ≤ n →
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], RootedDefectAt G s →
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ (γ : ℝ) * (n : ℝ) ^ 2 →
          (∀ Q : CliquePartition G, Q.OrderAtMost 4 → (defectTarget s n : ℝ) - δ ≤ Q.size) →
          ∃ (T : SimpleGraph (Fin n)) (_ : DecidableRel T.Adj), IsAdmissibleExtremal T s ∧
            (editDist G.edgeFinset T.edgeFinset : ℝ) ≤
              (stabilityConstant s : ℝ) * δ +
                (n : ℝ) * Real.sqrt ((1 + 4 * (stabilityConstant s : ℝ)) * δ) := by
  sorry

/-- **Corollary 6.3, (6.18) (equality).** For each `s` and large `n`, a graph with rooted simplicial
defect at most `s` has `cp(G) = Q_s(n)` iff `c₄(G) = Q_s(n)` iff it is an extremal template. -/
theorem corollary_6_3_equality (s : ℕ) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      RootedDefectAt G s →
        (CliqueCoverEq G (defectTarget s n) ↔ CliqueCover4Eq G (defectTarget s n)) ∧
        (CliqueCover4Eq G (defectTarget s n) ↔ IsAdmissibleExtremal G s) := by
  sorry

/-- **Proposition 6.3a (a square-root obstruction).** If `n + s = 3q`, `2s + 2 ≤ q` and
`1 ≤ d ≤ q/2`, some graph on `n` vertices with rooted simplicial defect at most `s` has
`cp = c₄ = Q_s(n) − (d² + C(d,2))`, and its edit distance to every extremal template of optimal size
is at least `nd/4` and at least `n·√(d² + C(d,2))/8`. -/
theorem proposition_6_3a (n s q d : ℕ) (hn : n + s = 3 * q) (hq : 2 * s + 2 ≤ q)
    (hd1 : 1 ≤ d) (hd : 2 * d ≤ q) :
    ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      RootedDefectAt G s ∧
      ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
        Q.size + displacementDeficit d = defectTarget s n ∧
        (∀ R : CliquePartition G, Q.size ≤ R.size) ∧
        ∀ (T : SimpleGraph (Fin n)) [DecidableRel T.Adj], IsAdmissibleExtremal T s →
          n * d ≤ 4 * editDist G.edgeFinset T.edgeFinset ∧
          (n : ℝ) * Real.sqrt (displacementDeficit d) / 8 ≤
            (editDist G.edgeFinset T.edgeFinset : ℝ) := by
  sorry

/-- **Proposition 6.3a, deficit one.** No bound linear in the deficit holds towards the optimal
templates: for every `A` and `N` some graph of order `n ≥ N` with rooted simplicial defect at most
`s` and `cp = c₄ = Q_s(n) − 1` is at edit distance more than `A` from every extremal template of
optimal size. -/
theorem proposition_6_3a_deficit_one (s A N : ℕ) :
    ∃ n, N ≤ n ∧ ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      RootedDefectAt G s ∧
      ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
        Q.size + 1 = defectTarget s n ∧
        (∀ R : CliquePartition G, Q.size ≤ R.size) ∧
        ∀ (T : SimpleGraph (Fin n)) [DecidableRel T.Adj], IsAdmissibleExtremal T s →
          A < editDist G.edgeFinset T.edgeFinset := by
  sorry

/-! ### Uniform bounds and sublinear defect (§6.7) -/

/-- **Proposition 6.4 (finite fractional bounds).** If `G` has rooted simplicial defect at most
`s ≤ n` and `w` is the maximum value of a fractional packing (so `F₄(G) = e(G) − w`), then
`F₄(G) ≤ M(n − s) + ns`, and `F₄(G) ≤ M(n − s) + ns − C(s + 1, 2)` when `4s ≤ n`. -/
theorem proposition_6_4 {n s : ℕ} (hs : s ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : RootedDefectAt G s) {w : ℚ} (hw : IsGreatest (Set.range (FracPacking.value (G := G))) w) :
    (G.edgeFinset.card : ℚ) - w ≤ (targetSize (n - s) : ℚ) + (n : ℚ) * s ∧
      (4 * s ≤ n → (G.edgeFinset.card : ℚ) - w ≤
        (targetSize (n - s) : ℚ) + (n : ℚ) * s - ((s + 1).choose 2 : ℚ)) := by
  sorry

/-- **Proposition 6.4, integral form.** For every `ε > 0` one threshold `N`, independent of `s`,
gives clique partitions of order at most four with at most `M(n − s) + ns + εn²` pieces (`s ≤ n`)
and at most `M(n − s) + ns − C(s + 1, 2) + εn²` pieces (`4s ≤ n`). -/
theorem proposition_6_4_integral (ε : ℚ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n s : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      RootedDefectAt G s →
        (s ≤ n → ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
          (Q.size : ℚ) ≤ (targetSize (n - s) : ℚ) + (n : ℚ) * s + ε * (n : ℚ) ^ 2) ∧
        (4 * s ≤ n → ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
          (Q.size : ℚ) ≤ (targetSize (n - s) : ℚ) + (n : ℚ) * s - ((s + 1).choose 2 : ℚ) +
            ε * (n : ℚ) ^ 2) := by
  sorry

open Filter Asymptotics in
/-- **Theorem 6.5, (6.24).** For graphs of orders tending to infinity with rooted simplicial defect
`o(n)`, there are partitions of order at most four with `max(0, |Q| − n²/6) = o(n²)`. -/
theorem theorem_6_5_partition_bound
    (order : ℕ → ℕ) (horder : Tendsto order atTop atTop)
    (G : ∀ n : ℕ, SimpleGraph (Fin (order n))) [∀ n, DecidableRel (G n).Adj]
    (s : ℕ → ℕ) (hG : ∀ n, RootedDefectAt (G n) (s n))
    (hs : (fun n => (s n : ℝ)) =o[atTop] (fun n => (order n : ℝ))) :
    ∃ Q : ∀ n, CliquePartition (G n), (∀ n, (Q n).OrderAtMost 4) ∧
      (fun n => max 0 (((Q n).size : ℝ) - (order n : ℝ) ^ 2 / 6))
        =o[atTop] (fun n => (order n : ℝ) ^ 2) := by
  sorry

open Filter Asymptotics in
/-- **Theorem 6.5, (6.25)–(6.26) (a root for all partitions).** If moreover eventually every
partition of order at most four has at least `n²/6 − δ` pieces with `δ = o(n²)`, there are cliques
`R` of the graphs and errors `e = o(n²)`, `e ≥ 0`, with `|R| − n/3 = o(n)`, missing incidences plus
outside edges `o(n²)`, and, for every partition `Q` with at most `M(n) + τ` pieces, at most `τ + e`
noncanonical pieces carrying at most `10τ + 10e` edges. -/
theorem theorem_6_5_stability
    (order : ℕ → ℕ) (horder : Tendsto order atTop atTop)
    (G : ∀ n : ℕ, SimpleGraph (Fin (order n))) [∀ n, DecidableRel (G n).Adj]
    (s : ℕ → ℕ) (δ : ℕ → ℚ)
    (hG : ∀ n, RootedDefectAt (G n) (s n))
    (hs : (fun n => (s n : ℝ)) =o[atTop] (fun n => (order n : ℝ)))
    (hδ : (fun n => (δ n : ℝ)) =o[atTop] (fun n => (order n : ℝ) ^ 2))
    (hnear : ∀ᶠ n in atTop, ∀ Q : CliquePartition (G n), Q.OrderAtMost 4 →
      (order n : ℚ) ^ 2 / 6 - δ n ≤ Q.size) :
    ∃ R : ∀ n, Finset (Fin (order n)), (∀ n, (G n).IsClique (R n : Set (Fin (order n)))) ∧
      (fun n => ((R n).card : ℝ) - (order n : ℝ) / 3) =o[atTop] (fun n => (order n : ℝ)) ∧
      (fun n => (missingIncidences (G n) (R n) : ℝ) + (outsideEdges (G n) (R n)).card)
        =o[atTop] (fun n => (order n : ℝ) ^ 2) ∧
      ∃ e : ℕ → ℚ, (∀ n, 0 ≤ e n) ∧
        (fun n => (e n : ℝ)) =o[atTop] (fun n => (order n : ℝ) ^ 2) ∧
        (∀ n (Q : CliquePartition (G n)) (τ : ℚ), (Q.size : ℚ) ≤ targetSize (order n) + τ →
          ((noncanonicalPieces (R n) Q).card : ℚ) ≤ τ + e n) ∧
        (∀ n (Q : CliquePartition (G n)) (τ : ℚ), (Q.size : ℚ) ≤ targetSize (order n) + τ →
          (noncanonicalEdgeMass (R n) Q : ℚ) ≤ 10 * τ + 10 * e n) := by
  sorry

/-- **Corollary 6.6 (exact bound, uniform in the defect).** If `T(P(S)) ≤ n`, then every graph on
`n` vertices with rooted simplicial defect at most `s ≤ S` has a clique partition of order at most
four with at most `Q_s(n)` pieces. -/
theorem corollary_6_6 (n S : ℕ) (hn : tower2 (Ptower S) ≤ n) :
    ∀ s : ℕ, s ≤ S → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      RootedDefectAt G s →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n := by
  sorry

/-- **Corollary 6.6, (6.29).** If `T(P(0)) ≤ n`, then `T(P(s_max(n))) ≤ n`, and the bound of
Theorem C holds at order `n` for every `s ≤ s_max(n)`. -/
theorem corollary_6_6_sMax (n : ℕ) (h0 : tower2 (Ptower 0) ≤ n) :
    tower2 (Ptower (sMaxT n)) ≤ n ∧
    ∀ s : ℕ, s ≤ sMaxT n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      RootedDefectAt G s →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ defectTarget s n := by
  sorry

/-! ### Bounded-clique-gap annex -/

/-- **Bounded clique gap (G.1).** If `G` is chordal and has no clique on `d + 2` vertices, every
fractional triangle packing has value at most `ν₃(G) + (10 + d/2)·n`. -/
theorem chordal_gap_linear_cliqueFree {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {d : ℕ} (hc : IsChordal G) (hk : G.CliqueFree (d + 2))
    (F : TriFracPacking G) :
    F.value ≤ (nu3 G : ℚ) + (10 + (d : ℚ) / 2) * (Fintype.card V : ℚ) := by
  sorry

end ErdosPaperIV
