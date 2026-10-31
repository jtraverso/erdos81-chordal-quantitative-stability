/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Data.Rat.Star
public import Mathlib.Tactic.Positivity

/-!
# Deficit propagation along a nondecreasing copy path

The copy construction is responsible for proving monotonicity and the upper
envelope.  Once supplied, this module records the exact deficit consequence:
every later state is at least as close to the envelope as the initial state.
-/

@[expose] public section

namespace PaperIV

theorem deficit_along_nondecreasing_path
    {Q initial current δ : ℚ}
    (hupper : current ≤ Q)
    (hmono : initial ≤ current)
    (hnear : Q - initial ≤ δ) :
    0 ≤ Q - current ∧ Q - current ≤ δ := by
  constructor <;> linarith

theorem terminal_near_of_initial_near
    {Q initial terminal δ : ℚ}
    (hupper : terminal ≤ Q)
    (hmono : initial ≤ terminal)
    (hnear : Q - initial ≤ δ) :
    Q - δ ≤ terminal := by
  have := deficit_along_nondecreasing_path hupper hmono hnear
  linarith

end PaperIV
