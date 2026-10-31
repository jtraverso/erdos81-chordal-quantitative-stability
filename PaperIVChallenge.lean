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
* `corollary_6_1a`: for that root, every clique partition with at most `M(n) + τ` pieces has at
  most `τ + 48δ` noncanonical pieces (Corollary 6.1a);
* `identity_6_7b`: the root-defect identity `∑_K rootPieceDefect R K = |Q| − splitBaseline n |R|
  + missingIncidences + 3·|outside edges|` (identity (6.7b));
* `corollary_6_2`: for large `n`, a chordal graph has `cp(G) = M(n)` iff `c₄(G) = M(n)` iff it is a
  complete-split graph with a core of optimal size (Corollary 6.2).
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

/-- **Corollary 6.1a (stability of partitions).** Under the hypotheses of Theorem 6.1 there is a
clique root `R` such that every clique partition with at most `M(n) + τ` pieces has at most
`τ + 48δ` noncanonical pieces. -/
theorem corollary_6_1a :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], IsChordal G →
        ∀ δ : ℚ, 0 ≤ δ → δ ≤ gamma * (n : ℚ) ^ 2 →
          (∀ Q : CliquePartition G, Q.OrderAtMost 4 →
              (targetSize n : ℚ) - δ ≤ (Q.size : ℚ)) →
          ∃ R : Finset (Fin n), G.IsClique (R : Set (Fin n)) ∧
            2 ≤ R.card ∧ R.card ≤ (Finset.univ \ R).card ∧
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

end ErdosPaperIV
