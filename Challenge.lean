module

public import Init.Data.Nat.Gcd

/-!
# OEIS A260194 has a missing positive difference

Lean index zero is the first OEIS term. This is the recurrence used by
DeepMind Formal Conjectures at revision 2f91d251c07fbbaf9435166d47c11e884a08a6cf.
The advertised result negates the entire positive-difference assertion.
-/

@[expose] public section

namespace JumpResearch

/-- The three-one sequence with the gcd of the current and twice-preceding terms added. -/
def a : Nat → Nat
  | 0 | 1 | 2 => 1
  | n+3 => a (n+2) + Nat.gcd (a (n+2)) (a n)

/-- Some positive integer never occurs as an adjacent difference. -/
theorem refutesCatalogueStatement :
    ¬ (∀ d : Nat, d > 0 → ∃ n : Nat, a (n+1) = a n+d) := by
  sorry

end JumpResearch
