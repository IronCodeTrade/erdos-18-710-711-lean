import Mathlib

/-! Erdős #710: dokładne wartości f(n) z certyfikatami (dopasowanie + zbiór Halla). -/

namespace R6E710
open Finset

/-- W przedziale `(n, n+K)` istnieją różne liczby `b 1, …, b n` z `i ∣ b i`. -/
def Good (n K : ℕ) : Prop :=
  ∃ b : ℕ → ℕ, (∀ i ∈ Icc 1 n, n < b i ∧ b i < n + K ∧ i ∣ b i) ∧ Set.InjOn b (Icc 1 n)

theorem good_mono {n K K' : ℕ} (h : K ≤ K') : Good n K → Good n K' := by
  rintro ⟨b, hb, hi⟩
  exact ⟨b, fun i hi' => ⟨(hb i hi').1, by have := (hb i hi').2.1; omega, (hb i hi').2.2⟩, hi⟩

theorem exists_good (n : ℕ) : ∃ K, Good n K := by
  refine ⟨n * n + 1, fun i => i * (n + 1), fun i hi => ?_, ?_⟩
  · simp only [mem_Icc] at hi
    refine ⟨?_, ?_, Dvd.intro _ rfl⟩
    · nlinarith
    · nlinarith
  · intro i _ j _ h
    simp only at h
    exact Nat.eq_of_mul_eq_mul_right (by omega) h

/-- f(n) z problemu Erdősa #710 -/
noncomputable def f (n : ℕ) : ℕ := by classical exact Nat.find (exists_good n)

theorem f_eq_of {n K : ℕ} (h1 : Good n K) (h2 : ¬ Good n (K - 1)) : f n = K := by
  classical
  unfold f
  rw [Nat.find_eq_iff]
  refine ⟨h1, fun k hk hg => h2 (good_mono (by omega) hg)⟩

/-- sprawdzenie jawnego przyporządkowania -/
def upperOK (n K : ℕ) (bs : List ℕ) : Bool :=
  bs.length == n && decide bs.Nodup &&
  (List.range n).all fun j => decide (n < bs.getD j 0) && decide (bs.getD j 0 < n + K) &&
    bs.getD j 0 % (j + 1) == 0

theorem good_of_upperOK {n K : ℕ} {bs : List ℕ} (h : upperOK n K bs = true) : Good n K := by
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

/-- certyfikat Halla: zbiór `S` indeksów, których wszystkie wielokrotności w przedziale
leżą w `T`, przy czym `|T| < |S|` -/
def hallOK (n K : ℕ) (S T : List ℕ) : Bool :=
  decide S.Nodup && decide (T.length < S.length) &&
  S.all (fun i => decide (1 ≤ i) && decide (i ≤ n)) &&
  S.all fun i => (List.range' (n + 1) (K - 1)).all fun a => a % i != 0 || T.contains a

theorem not_good_of_hallOK {n K : ℕ} {S T : List ℕ} (h : hallOK n K S T = true) :
    ¬ Good n K := by
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

theorem f_eq_of_certs {n K : ℕ} {bs S T : List ℕ} (h1 : upperOK n K bs = true)
    (h2 : hallOK n (K - 1) S T = true) : f n = K :=
  f_eq_of (good_of_upperOK h1) (not_good_of_hallOK h2)

/-! Uwaga o OEIS A390246 i A219787: wersja z przedziałem domkniętym `[n+1, H]`. -/

def GoodC (n H : ℕ) : Prop :=
  ∃ b : ℕ → ℕ, (∀ i ∈ Icc 1 n, n + 1 ≤ b i ∧ b i ≤ H ∧ i ∣ b i) ∧ Set.InjOn b (Icc 1 n)

theorem goodC_iff (n K : ℕ) (hK : 1 ≤ K) : GoodC n (n + K - 1) ↔ Good n K := by
  constructor
  · rintro ⟨b, hb, hi⟩
    exact ⟨b, fun i h => ⟨by have := (hb i h).1; omega, by have := (hb i h).2.1; omega,
      (hb i h).2.2⟩, hi⟩
  · rintro ⟨b, hb, hi⟩
    exact ⟨b, fun i h => ⟨by have := (hb i h).1; omega, by have := (hb i h).2.1; omega,
      (hb i h).2.2⟩, hi⟩

theorem exists_goodC (n : ℕ) : ∃ H, GoodC n H := by
  obtain ⟨K, hK⟩ := exists_good (n := n)
  exact ⟨n + (K + 1) - 1, (goodC_iff n (K + 1) (by omega)).mpr (good_mono (by omega) hK)⟩

/-- A219787(n) -/
noncomputable def g (n : ℕ) : ℕ := by classical exact Nat.find (exists_goodC n)

/-- Hipoteza z OEIS A390246 („a(n) = A219787(n) − (n−1)”) jest prawdziwa dla każdego n ≥ 1. -/
theorem f_eq_g_sub (n : ℕ) (hn : 1 ≤ n) : f n = g n - (n - 1) := by
  classical
  have hf : Good n (f n) := by unfold f; exact Nat.find_spec (exists_good n)
  have hg : GoodC n (g n) := by unfold g; exact Nat.find_spec (exists_goodC n)
  -- f n ≥ 1 i g n ≥ n + 1
  have hf1 : 1 ≤ f n := by
    obtain ⟨b, hb, -⟩ := hf
    have := hb 1 (by simp only [mem_Icc]; omega); omega
  have hg1 : n + 1 ≤ g n := by
    obtain ⟨b, hb, -⟩ := hg
    have := hb 1 (by simp only [mem_Icc]; omega); omega
  have e1 : g n ≤ n + f n - 1 := by
    unfold g; exact Nat.find_min' _ ((goodC_iff n (f n) hf1).mpr hf)
  have e2 : f n ≤ g n - n + 1 := by
    unfold f; apply Nat.find_min'
    have := (goodC_iff n (g n - n + 1) (by omega)).mp
    apply this
    have h' : n + (g n - n + 1) - 1 = g n := by omega
    rw [h']; exact hg
  omega

end R6E710
