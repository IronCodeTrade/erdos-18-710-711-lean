/-
  CAUTION: this file uses `native_decide` for the final bitset evaluation of h(11!).
  That trusts the Lean compiler and the compiled C code, not the kernel tactic `decide`.
  The supporting lemmas (prime factorization, completeness of the divisor list, and
  correctness of the bitset DP) are still kernel-checked. See the README.
-/

import R6E18Core

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace R6E18

def ps11 : List (ℕ × ℕ) := [(2, 8), (3, 4), (5, 2), (7, 1), (11, 1)]
theorem ps11_prime : ∀ x ∈ ps11, x.1.Prime := by
  intro x hx; simp only [ps11, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl <;> norm_num
theorem fact11 : Nat.factorial 11 = fprod ps11 := by decide +kernel
theorem nd11 : (gen ps11).Nodup := by decide +kernel
/-- h(11!) ≤ 7 -/
theorem h11_le : PracticalWith (Nat.factorial 11) 7 := by
  rw [fact11]; exact practical_of_check ps11 ps11_prime nd11 7 (by native_decide)
/-- h(11!) > 6: liczby 29749079 nie da się zapisać jako sumy ≤ 6 różnych dzielników 11! -/
theorem h11_not : ¬ PracticalWith (Nat.factorial 11) 6 := by
  rw [fact11]
  exact not_practical_of_check ps11 ps11_prime nd11 6 29749079 (by norm_num) (by decide +kernel) (by native_decide)
/-- h(11!) = 7 -/
theorem h11_eq : PracticalWith (Nat.factorial 11) 7 ∧ ¬ PracticalWith (Nat.factorial 11) 6 := ⟨h11_le, h11_not⟩

end R6E18
#print axioms R6E18.h11_eq
