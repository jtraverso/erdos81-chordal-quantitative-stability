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
# The sharp quadratic envelope

This is the scalar identity used to turn a paid terminal partition into local stability. We work over rationals first; graph cardinalities will later be cast into this statement.
-/

@[expose] public section

namespace PaperIV

def sharpEnvelope (n : ℚ) : ℚ := (2 * n + 1) ^ 2 / 24

def splitBaseline (n p : ℚ) : ℚ := p * (n - p) - p * (p - 1) / 2

theorem sharpEnvelope_sub_splitBaseline (n p : ℚ) :
    sharpEnvelope n - splitBaseline n p = (6 * p - 2 * n - 1) ^ 2 / 24 := by
  simp only [sharpEnvelope, splitBaseline]
  ring

theorem splitBaseline_le_sharpEnvelope (n p : ℚ) :
    splitBaseline n p ≤ sharpEnvelope n := by
  rw [← sub_nonneg]
  rw [sharpEnvelope_sub_splitBaseline]
  positivity

end PaperIV
