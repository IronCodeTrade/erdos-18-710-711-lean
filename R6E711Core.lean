import Mathlib

/-! Erdős #711: f(n,m) – okresowość, ogólne dolne ograniczenie, certyfikaty. -/

namespace R6E711
open Finset

/-- W przedziale `(m, m+K)` istnieją różne `b 1, …, b n` z `i ∣ b i`. -/
def Good (n m K : ℕ) : Prop :=
  ∃ b : ℕ → ℕ, (∀ i ∈ Icc 1 n, m < b i ∧ b i < m + K ∧ i ∣ b i) ∧ Set.InjOn b (Icc 1 n)

theorem good_mono {n m K K' : ℕ} (h : K ≤ K') : Good n m K → Good n m K' := by
  rintro ⟨b, hb, hi⟩
  exact ⟨b, fun i hi' => ⟨(hb i hi').1, by have := (hb i hi').2.1; omega, (hb i hi').2.2⟩, hi⟩

theorem exists_good (n m : ℕ) : ∃ K, Good n m K := by
  refine ⟨(m + 1) * n + 1, fun i => i * (m + 1), fun i hi => ?_, ?_⟩
  · simp only [mem_Icc] at hi
    refine ⟨?_, ?_, Dvd.intro _ rfl⟩
    · nlinarith
    · nlinarith
  · intro i _ j _ h
    simp only at h
    exact Nat.eq_of_mul_eq_mul_right (by omega) h

/-- f(n,m) z problemu Erdősa #711 -/
noncomputable def f (n m : ℕ) : ℕ := by classical exact Nat.find (exists_good n m)

theorem good_f (n m : ℕ) : Good n m (f n m) := by
  classical unfold f; exact Nat.find_spec (exists_good n m)

theorem f_le_of {n m K : ℕ} (h : Good n m K) : f n m ≤ K := by
  classical unfold f; exact Nat.find_min' _ h

theorem le_f_of {n m K : ℕ} (h : ¬ Good n m (K - 1)) (hK : 1 ≤ K) : K ≤ f n m := by
  by_contra hc
  exact h (good_mono (by omega) (good_f n m))

/-- Okresowość: przesunięcie o `P` podzielne przez 1..n nie zmienia problemu. -/
theorem good_shift {n m K P : ℕ} (hP : ∀ i ∈ Icc 1 n, i ∣ P) :
    Good n (m + P) K ↔ Good n m K := by
  constructor
  · rintro ⟨b, hb, hi⟩
    refine ⟨fun i => b i - P, fun i h => ?_, ?_⟩
    · obtain ⟨h1, h2, h3⟩ := hb i h
      refine ⟨?_, ?_, Nat.dvd_sub h3 (hP i h)⟩ <;> simp only <;> omega
    · intro x hx y hy hxy
      have := (hb x hx).1; have := (hb y hy).1
      exact hi hx hy (by simp only at hxy; omega)
  · rintro ⟨b, hb, hi⟩
    refine ⟨fun i => b i + P, fun i h => ?_, ?_⟩
    · obtain ⟨h1, h2, h3⟩ := hb i h
      refine ⟨?_, ?_, Nat.dvd_add h3 (hP i h)⟩ <;> simp only <;> omega
    · intro x hx y hy hxy
      exact hi hx hy (by simp only at hxy; omega)

theorem good_mod {n m K P : ℕ} (hP : ∀ i ∈ Icc 1 n, i ∣ P) :
    Good n m K ↔ Good n (m % P) K := by
  conv_lhs => rw [← Nat.mod_add_div m P]
  induction m / P with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc, good_shift hP, ih]

/-- Ogólne dolne ograniczenie: dla n ≥ 2, f(n,(n-1)²) ≥ 2n-1
(liczby n-1 i n mają w przedziale tylko jedną wspólną wielokrotność n(n-1)). -/
theorem f_sq_ge (n : ℕ) (hn : 2 ≤ n) : 2 * n - 1 ≤ f n ((n - 1) ^ 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  apply le_f_of _ (by omega)
  have e1 : k + 2 - 1 = k + 1 := by omega
  have e2 : 2 * (k + 2) - 1 - 1 = 2 * k + 2 := by omega
  rw [e1, e2]
  rintro ⟨b, hb, hi⟩
  have hA : b (k + 1) = (k + 1) * (k + 2) := by
    obtain ⟨h1, h2, ⟨c, hc⟩⟩ := hb (k + 1) (by simp only [mem_Icc]; omega)
    rw [hc] at h1 h2 ⊢
    have c1 : k + 1 < c := Nat.lt_of_mul_lt_mul_left (a := k + 1) (by nlinarith)
    have c2 : c < k + 3 := Nat.lt_of_mul_lt_mul_left (a := k + 1) (by nlinarith)
    have : c = k + 2 := by omega
    rw [this]
  have hB : b (k + 2) = (k + 1) * (k + 2) := by
    obtain ⟨h1, h2, ⟨c, hc⟩⟩ := hb (k + 2) (by simp only [mem_Icc]; omega)
    rw [hc] at h1 h2 ⊢
    have c1 : k < c := Nat.lt_of_mul_lt_mul_left (a := k + 2) (by nlinarith)
    have c2 : c < k + 2 := Nat.lt_of_mul_lt_mul_left (a := k + 2) (by nlinarith)
    have : c = k + 1 := by omega
    rw [this, Nat.mul_comm]
  have := hi (by simp only [coe_Icc, Set.mem_Icc]; omega)
    (by simp only [coe_Icc, Set.mem_Icc]; omega) (hA.trans hB.symm)
  omega

/-! Certyfikaty -/

def upperOK (n m K : ℕ) (bs : List ℕ) : Bool :=
  bs.length == n && decide bs.Nodup &&
  (List.range n).all fun j => decide (m < bs.getD j 0) && decide (bs.getD j 0 < m + K) &&
    bs.getD j 0 % (j + 1) == 0

theorem good_of_upperOK {n m K : ℕ} {bs : List ℕ} (h : upperOK n m K bs = true) :
    Good n m K := by
  simp only [upperOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨hlen, hnd⟩, hall⟩ := h
  refine ⟨fun i => bs.getD (i - 1) 0, fun i hi => ?_, ?_⟩
  · simp only [mem_Icc] at hi
    obtain ⟨⟨h1, h2⟩, h3⟩ := hall (i - 1) (by omega)
    have : i - 1 + 1 = i := by omega
    rw [this] at h3
    exact ⟨h1, h2, Nat.dvd_of_mod_eq_zero h3⟩
  · intro i hi j hj hij
    simp only [coe_Icc, Set.mem_Icc] at hi hj
    simp only [List.getD_eq_getElem?_getD] at hij
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hij
    simp only [Option.getD_some] at hij
    have := (hnd.getElem_inj_iff).mp hij
    omega

def hallOK (n m K : ℕ) (S T : List ℕ) : Bool :=
  decide S.Nodup && decide (T.length < S.length) &&
  S.all (fun i => decide (1 ≤ i) && decide (i ≤ n)) &&
  S.all fun i => (List.range' (m + 1) (K - 1)).all fun a => a % i != 0 || T.contains a

theorem not_good_of_hallOK {n m K : ℕ} {S T : List ℕ} (h : hallOK n m K S T = true) :
    ¬ Good n m K := by
  classical
  simp only [hallOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, bne_iff_ne, ne_eq, List.contains_iff_mem, List.mem_range'_1] at h
  obtain ⟨⟨⟨hnd, hlt⟩, hS⟩, hcov⟩ := h
  rintro ⟨b, hb, hinj⟩
  have hsub : S.toFinset.image b ⊆ T.toFinset := by
    intro y hy
    simp only [mem_image, List.mem_toFinset] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    have hi' := hS i hi
    have hbi := hb i (by simp only [mem_Icc]; exact hi')
    rw [List.mem_toFinset]
    rcases hcov i hi (b i) ⟨by omega, by omega⟩ with h | h
    · exact absurd (Nat.mod_eq_zero_of_dvd hbi.2.2) h
    · exact h
  have hinj' : Set.InjOn b S.toFinset := by
    intro x hx y hy hxy
    simp only [List.coe_toFinset, Set.mem_ofPred_eq] at hx hy
    exact hinj (by simp only [coe_Icc, Set.mem_Icc]; exact hS x hx)
      (by simp only [coe_Icc, Set.mem_Icc]; exact hS y hy) hxy
  have h1 := card_le_card hsub
  rw [card_image_of_injOn hinj', List.toFinset_card_of_nodup hnd] at h1
  have h2 := List.toFinset_card_le T
  omega

/-- wszystkie reszty `r0, r0+1, …` mają certyfikat -/
def allOK (n K : ℕ) : List (List ℕ) → ℕ → Bool
  | [], _ => true
  | c :: cs, r => upperOK n r K c && allOK n K cs (r + 1)

theorem allOK_sound (n K : ℕ) : ∀ (cs : List (List ℕ)) (r0 : ℕ), allOK n K cs r0 = true →
    ∀ r, r0 ≤ r → r < r0 + cs.length → Good n r K
  | [], _, _, r, h1, h2 => by simp at h2; omega
  | c :: cs, r0, h, r, h1, h2 => by
      simp only [allOK, Bool.and_eq_true] at h
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · exact good_of_upperOK h.1
      · exact allOK_sound n K cs (r0 + 1) h.2 r (by omega) (by simp at h2; omega)

/-- Jeśli wszystkie reszty modulo `P` mają certyfikat, to `f(n,m) ≤ K` dla każdego `m`. -/
theorem f_le_all {n K P : ℕ} (hP0 : 0 < P) (hP : ∀ i ∈ Icc 1 n, i ∣ P)
    (cs : List (List ℕ)) (hlen : cs.length = P) (h : allOK n K cs 0 = true) (m : ℕ) :
    f n m ≤ K := by
  apply f_le_of
  rw [good_mod hP]
  exact allOK_sound n K cs 0 h _ (Nat.zero_le _) (by rw [hlen, Nat.zero_add]; exact Nat.mod_lt _ hP0)

end R6E711
