import R6E18Core

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace R6E18

def ps9 : List (ℕ × ℕ) := [(2, 7), (3, 4), (5, 1), (7, 1)]
theorem ps9_prime : ∀ x ∈ ps9, x.1.Prime := by
  intro x hx; simp only [ps9, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl <;> norm_num
theorem fact9 : Nat.factorial 9 = fprod ps9 := by decide +kernel
theorem nd9 : (gen ps9).Nodup := by decide +kernel
/-- h(9!) ≤ 7 -/
theorem h9_le : PracticalWith (Nat.factorial 9) 7 := by
  rw [fact9]; exact practical_of_check ps9 ps9_prime nd9 7 (by decide +kernel)
/-- h(9!) > 6: liczby 362783 nie da się zapisać jako sumy ≤ 6 różnych dzielników 9! -/
theorem h9_not : ¬ PracticalWith (Nat.factorial 9) 6 := by
  rw [fact9]
  exact not_practical_of_check ps9 ps9_prime nd9 6 362783 (by norm_num) (by decide +kernel) (by decide +kernel)
/-- h(9!) = 7 -/
theorem h9_eq : PracticalWith (Nat.factorial 9) 7 ∧ ¬ PracticalWith (Nat.factorial 9) 6 := ⟨h9_le, h9_not⟩

def ps10 : List (ℕ × ℕ) := [(2, 8), (3, 4), (5, 2), (7, 1)]
theorem ps10_prime : ∀ x ∈ ps10, x.1.Prime := by
  intro x hx; simp only [ps10, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl <;> norm_num
theorem fact10 : Nat.factorial 10 = fprod ps10 := by decide +kernel
theorem nd10 : (gen ps10).Nodup := by decide +kernel
/-- h(10!) ≤ 7 -/
theorem h10_le : PracticalWith (Nat.factorial 10) 7 := by
  rw [fact10]; exact practical_of_check ps10 ps10_prime nd10 7 (by decide +kernel)
/-- h(10!) > 6: liczby 2979161 nie da się zapisać jako sumy ≤ 6 różnych dzielników 10! -/
theorem h10_not : ¬ PracticalWith (Nat.factorial 10) 6 := by
  rw [fact10]
  exact not_practical_of_check ps10 ps10_prime nd10 6 2979161 (by norm_num) (by decide +kernel) (by decide +kernel)
/-- h(10!) = 7 -/
theorem h10_eq : PracticalWith (Nat.factorial 10) 7 ∧ ¬ PracticalWith (Nat.factorial 10) 6 := ⟨h10_le, h10_not⟩

end R6E18
#print axioms R6E18.h9_eq
#print axioms R6E18.h10_eq
