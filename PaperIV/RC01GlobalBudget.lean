/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Tactic.Positivity

/-!
# RC01: final normalized error ledger

Lean transcription of the exact Farkas certificate
`certificates/rc01_global_error_budget.json` (Certo certificate
`b80d1aabb9939400`).
-/

@[expose] public section

namespace PaperIV.RC01GlobalBudget

/-- The six post-cleanup loss accounts fit in half of the requested error.
The remaining half is reserved for the high/low triangle bridge. -/
theorem six_accounts_le_half {ε δ d ζ u v invk light : ℚ}
    (hε : 0 < ε)
    (hδ : 15 * δ ≤ ε / 100)
    (hd : 5 * d ≤ ε / 10)
    (hζ : ζ ≤ ε / 10)
    (huv : (5 / 6 : ℚ) * (u + v) ≤ ε / 10)
    (hinvk : invk ≤ ε / 10)
    (hlight : light ≤ ε / 20) :
    15 * δ + 5 * d + ζ + (5 / 6 : ℚ) * (u + v) + invk + light ≤ ε / 2 := by
  linarith

end PaperIV.RC01GlobalBudget
