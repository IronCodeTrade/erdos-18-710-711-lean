import R6E18Core

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace R6E18

def ps3 : List (ℕ × ℕ) := [(2, 1), (3, 1)]
theorem ps3_prime : ∀ x ∈ ps3, x.1.Prime := by
  intro x hx; simp only [ps3, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl <;> norm_num
theorem fact3 : Nat.factorial 3 = fprod ps3 := by decide +kernel
theorem nd3 : (gen ps3).Nodup := by decide +kernel
/-- h(3!) ≤ 2 -/
theorem h3_le : PracticalWith (Nat.factorial 3) 2 := by
  rw [fact3]; exact practical_of_check ps3 ps3_prime nd3 2 (by decide +kernel)
/-- h(3!) > 1: liczby 4 nie da się zapisać jako sumy ≤ 1 różnych dzielników 3! -/
theorem h3_not : ¬ PracticalWith (Nat.factorial 3) 1 := by
  rw [fact3]
  exact not_practical_of_check ps3 ps3_prime nd3 1 4 (by norm_num) (by decide +kernel) (by decide +kernel)
/-- h(3!) = 2 -/
theorem h3_eq : PracticalWith (Nat.factorial 3) 2 ∧ ¬ PracticalWith (Nat.factorial 3) 1 := ⟨h3_le, h3_not⟩

def ps4 : List (ℕ × ℕ) := [(2, 3), (3, 1)]
theorem ps4_prime : ∀ x ∈ ps4, x.1.Prime := by
  intro x hx; simp only [ps4, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl <;> norm_num
theorem fact4 : Nat.factorial 4 = fprod ps4 := by decide +kernel
theorem nd4 : (gen ps4).Nodup := by decide +kernel
/-- h(4!) ≤ 3 -/
theorem h4_le : PracticalWith (Nat.factorial 4) 3 := by
  rw [fact4]; exact practical_of_check ps4 ps4_prime nd4 3 (by decide +kernel)
/-- h(4!) > 2: liczby 17 nie da się zapisać jako sumy ≤ 2 różnych dzielników 4! -/
theorem h4_not : ¬ PracticalWith (Nat.factorial 4) 2 := by
  rw [fact4]
  exact not_practical_of_check ps4 ps4_prime nd4 2 17 (by norm_num) (by decide +kernel) (by decide +kernel)
/-- h(4!) = 3 -/
theorem h4_eq : PracticalWith (Nat.factorial 4) 3 ∧ ¬ PracticalWith (Nat.factorial 4) 2 := ⟨h4_le, h4_not⟩

def ps5 : List (ℕ × ℕ) := [(2, 3), (3, 1), (5, 1)]
theorem ps5_prime : ∀ x ∈ ps5, x.1.Prime := by
  intro x hx; simp only [ps5, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl|rfl <;> norm_num
theorem fact5 : Nat.factorial 5 = fprod ps5 := by decide +kernel
theorem nd5 : (gen ps5).Nodup := by decide +kernel
/-- h(5!) ≤ 4 -/
theorem h5_le : PracticalWith (Nat.factorial 5) 4 := by
  rw [fact5]; exact practical_of_check ps5 ps5_prime nd5 4 (by decide +kernel)
/-- h(5!) > 3: liczby 97 nie da się zapisać jako sumy ≤ 3 różnych dzielników 5! -/
theorem h5_not : ¬ PracticalWith (Nat.factorial 5) 3 := by
  rw [fact5]
  exact not_practical_of_check ps5 ps5_prime nd5 3 97 (by norm_num) (by decide +kernel) (by decide +kernel)
/-- h(5!) = 4 -/
theorem h5_eq : PracticalWith (Nat.factorial 5) 4 ∧ ¬ PracticalWith (Nat.factorial 5) 3 := ⟨h5_le, h5_not⟩

def ps6 : List (ℕ × ℕ) := [(2, 4), (3, 2), (5, 1)]
theorem ps6_prime : ∀ x ∈ ps6, x.1.Prime := by
  intro x hx; simp only [ps6, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl|rfl <;> norm_num
theorem fact6 : Nat.factorial 6 = fprod ps6 := by decide +kernel
theorem nd6 : (gen ps6).Nodup := by decide +kernel
/-- h(6!) ≤ 5 -/
theorem h6_le : PracticalWith (Nat.factorial 6) 5 := by
  rw [fact6]; exact practical_of_check ps6 ps6_prime nd6 5 (by decide +kernel)
/-- h(6!) > 4: liczby 659 nie da się zapisać jako sumy ≤ 4 różnych dzielników 6! -/
theorem h6_not : ¬ PracticalWith (Nat.factorial 6) 4 := by
  rw [fact6]
  exact not_practical_of_check ps6 ps6_prime nd6 4 659 (by norm_num) (by decide +kernel) (by decide +kernel)
/-- h(6!) = 5 -/
theorem h6_eq : PracticalWith (Nat.factorial 6) 5 ∧ ¬ PracticalWith (Nat.factorial 6) 4 := ⟨h6_le, h6_not⟩

def ps7 : List (ℕ × ℕ) := [(2, 4), (3, 2), (5, 1), (7, 1)]
theorem ps7_prime : ∀ x ∈ ps7, x.1.Prime := by
  intro x hx; simp only [ps7, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl <;> norm_num
theorem fact7 : Nat.factorial 7 = fprod ps7 := by decide +kernel
theorem nd7 : (gen ps7).Nodup := by decide +kernel
/-- h(7!) ≤ 5 -/
theorem h7_le : PracticalWith (Nat.factorial 7) 5 := by
  rw [fact7]; exact practical_of_check ps7 ps7_prime nd7 5 (by decide +kernel)
/-- h(7!) > 4: liczby 3733 nie da się zapisać jako sumy ≤ 4 różnych dzielników 7! -/
theorem h7_not : ¬ PracticalWith (Nat.factorial 7) 4 := by
  rw [fact7]
  exact not_practical_of_check ps7 ps7_prime nd7 4 3733 (by norm_num) (by decide +kernel) (by decide +kernel)
/-- h(7!) = 5 -/
theorem h7_eq : PracticalWith (Nat.factorial 7) 5 ∧ ¬ PracticalWith (Nat.factorial 7) 4 := ⟨h7_le, h7_not⟩

def ps8 : List (ℕ × ℕ) := [(2, 7), (3, 2), (5, 1), (7, 1)]
theorem ps8_prime : ∀ x ∈ ps8, x.1.Prime := by
  intro x hx; simp only [ps8, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl <;> norm_num
theorem fact8 : Nat.factorial 8 = fprod ps8 := by decide +kernel
theorem nd8 : (gen ps8).Nodup := by decide +kernel
/-- h(8!) ≤ 6 -/
theorem h8_le : PracticalWith (Nat.factorial 8) 6 := by
  rw [fact8]; exact practical_of_check ps8 ps8_prime nd8 6 (by decide +kernel)
/-- h(8!) > 5: liczby 33473 nie da się zapisać jako sumy ≤ 5 różnych dzielników 8! -/
theorem h8_not : ¬ PracticalWith (Nat.factorial 8) 5 := by
  rw [fact8]
  exact not_practical_of_check ps8 ps8_prime nd8 5 33473 (by norm_num) (by decide +kernel) (by decide +kernel)
/-- h(8!) = 6 -/
theorem h8_eq : PracticalWith (Nat.factorial 8) 6 ∧ ¬ PracticalWith (Nat.factorial 8) 5 := ⟨h8_le, h8_not⟩

end R6E18
#print axioms R6E18.h3_eq
#print axioms R6E18.h4_eq
#print axioms R6E18.h5_eq
#print axioms R6E18.h6_eq
#print axioms R6E18.h7_eq
#print axioms R6E18.h8_eq
