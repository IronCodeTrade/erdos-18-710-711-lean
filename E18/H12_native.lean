/-
  CAUTION: this file uses `native_decide` for the final bitset evaluation of h(12!).
  It was NOT successfully checked on the original machine (the run was stopped for
  lack of memory). The file is included so that the claim can be re-checked on a
  machine with enough RAM. Independent C and Python programs in `computations/e18/`
  both give h(12!)=8 with first witness k=475785157. See the README.
-/

import R6E18Core

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace R6E18

def ps12 : List (ℕ × ℕ) := [(2, 10), (3, 5), (5, 2), (7, 1), (11, 1)]
theorem ps12_prime : ∀ x ∈ ps12, x.1.Prime := by
  intro x hx; simp only [ps12, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl <;> norm_num
theorem fact12 : Nat.factorial 12 = fprod ps12 := by decide +kernel
theorem nd12 : (gen ps12).Nodup := by decide +kernel
/-- h(12!) ≤ 8 -/
theorem h12_le : PracticalWith (Nat.factorial 12) 8 := by
  rw [fact12]; exact practical_of_check ps12 ps12_prime nd12 8 (by native_decide)
/-- h(12!) > 7: liczby 475785157 nie da się zapisać jako sumy ≤ 7 różnych dzielników 12! -/
theorem h12_not : ¬ PracticalWith (Nat.factorial 12) 7 := by
  rw [fact12]
  exact not_practical_of_check ps12 ps12_prime nd12 7 475785157 (by norm_num) (by decide +kernel) (by native_decide)
/-- h(12!) = 8 -/
theorem h12_eq : PracticalWith (Nat.factorial 12) 8 ∧ ¬ PracticalWith (Nat.factorial 12) 7 := ⟨h12_le, h12_not⟩

end R6E18
#print axioms R6E18.h12_eq
