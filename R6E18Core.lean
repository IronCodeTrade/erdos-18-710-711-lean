import Mathlib

/-! Erdős #18: dokładne wartości h(n!) – weryfikowalny w jądrze Lean algorytm
(programowanie dynamiczne na bitach) wraz z dowodem poprawności. -/

namespace R6E18
open Finset

/-- `k` jest sumą co najwyżej `c` różnych dzielników `m`. -/
def SumOfDivs (m c k : ℕ) : Prop :=
  ∃ S ⊆ Nat.divisors m, S.card ≤ c ∧ S.sum id = k

/-- `h(m) ≤ c`: każde `1 ≤ k < m` jest sumą ≤ c różnych dzielników `m`. -/
def PracticalWith (m c : ℕ) : Prop := ∀ k, 1 ≤ k → k < m → SumOfDivs m c k

/-- sumy podlist listy `P` złożonych z co najwyżej `j` elementów -/
def LReach (P : List ℕ) (j s : ℕ) : Prop := ∃ l : List ℕ, l.Sublist P ∧ l.length ≤ j ∧ l.sum = s

def upd (M d : ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | p, x :: xs => (x ||| ((p <<< d) &&& M)) :: upd M d x xs

def run (M : ℕ) (init : List ℕ) : List ℕ → List ℕ
  | [] => init
  | d :: ds => upd M d 0 (run M init ds)

theorem length_upd (M d p : ℕ) (ls : List ℕ) : (upd M d p ls).length = ls.length := by
  induction ls generalizing p with
  | nil => rfl
  | cons x xs ih => simp [upd, ih]

theorem length_run (M : ℕ) (init ds : List ℕ) : (run M init ds).length = init.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [run, length_upd, ih]

theorem get_upd (M d : ℕ) : ∀ (ls : List ℕ) (p j : ℕ) (hj : j < ls.length),
    (upd M d p ls)[j]'(by rw [length_upd]; exact hj) =
      ls[j] ||| ((((p :: ls)[j]'(by simp; omega)) <<< d) &&& M)
  | [], _, _, hj => by simp at hj
  | x :: xs, p, 0, _ => by simp [upd]
  | x :: xs, p, j+1, hj => by
      simp only [upd, List.getElem_cons_succ]
      exact get_upd M d xs x j (by simpa using hj)

theorem lreach_nil (j s : ℕ) : LReach [] j s ↔ s = 0 := by
  constructor
  · rintro ⟨l, hl, -, rfl⟩; rw [List.sublist_nil.mp hl]; rfl
  · rintro rfl; exact ⟨[], List.Sublist.slnil, by simp, rfl⟩

theorem lreach_cons (d : ℕ) (P : List ℕ) (j s : ℕ) :
    LReach (d :: P) j s ↔ LReach P j s ∨ (0 < j ∧ d ≤ s ∧ LReach P (j-1) (s-d)) := by
  constructor
  · rintro ⟨l, hl, hlen, rfl⟩
    rcases List.sublist_cons_iff.mp hl with h | ⟨r, rfl, hr⟩
    · exact Or.inl ⟨l, h, hlen, rfl⟩
    · right
      simp only [List.length_cons, List.sum_cons] at hlen ⊢
      exact ⟨by omega, by omega, r, hr, by omega, by omega⟩
  · rintro (⟨l, hl, hlen, rfl⟩ | ⟨hj, hds, r, hr, hlen, hs⟩)
    · exact ⟨l, hl.cons d, hlen, rfl⟩
    · refine ⟨d :: r, hr.cons_cons d, ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · simp only [List.sum_cons]; omega

/-- niezmiennik: bit `s` warstwy `j` ⇔ `s < m` i `s` jest sumą ≤ j elementów `P` -/
def Good (m : ℕ) (P : List ℕ) (ls : List ℕ) : Prop :=
  ∀ j (hj : j < ls.length) s, (ls[j]).testBit s = true ↔ (s < m ∧ LReach P j s)

theorem good_upd (m M d : ℕ) (hM : ∀ s, M.testBit s = decide (s < m)) (P ls : List ℕ)
    (h : Good m P ls) : Good m (d :: P) (upd M d 0 ls) := by
  intro j hj s
  rw [length_upd] at hj
  rw [get_upd M d ls 0 j hj, lreach_cons]
  simp only [Nat.testBit_lor, Nat.testBit_land, Nat.testBit_shiftLeft, hM, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, h j hj s]
  cases j with
  | zero => simp
  | succ j =>
    simp only [List.getElem_cons_succ, h j (by omega) (s - d)]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨⟨h1, h2, h3⟩, h4⟩)
      · exact ⟨h1, Or.inl h2⟩
      · exact ⟨h4, Or.inr ⟨by omega, h1, by simpa using h3⟩⟩
    · rintro ⟨h1, h2 | ⟨-, h3, h4⟩⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨⟨h3, by omega, by simpa using h4⟩, h1⟩

theorem good_run (m M : ℕ) (hm : 0 < m) (hM : ∀ s, M.testBit s = decide (s < m)) (c : ℕ) :
    ∀ D : List ℕ, Good m D (run M (List.replicate (c+1) 1) D)
  | [] => by
      intro j hj s
      simp only [run, List.getElem_replicate, lreach_nil]
      rw [Nat.testBit_one_eq_true_iff_self_eq_zero]
      constructor
      · rintro rfl; exact ⟨hm, rfl⟩
      · exact fun h => h.2
  | d :: D => good_upd m M d hM D _ (good_run m M hm hM c D)

theorem mask_spec (m s : ℕ) : ((1 <<< m) - 1).testBit s = decide (s < m) := by
  rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow_sub_one]

/-! Lista dzielników z rozkładu na czynniki pierwsze. -/

def gen : List (ℕ × ℕ) → List ℕ
  | [] => [1]
  | (p, e) :: ps => (List.range (e+1)).flatMap fun i => (gen ps).map (p^i * ·)

def fprod : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (p, e) :: ps => p^e * fprod ps

theorem mem_gen_of_dvd : ∀ (ps : List (ℕ × ℕ)), (∀ x ∈ ps, x.1.Prime) →
    ∀ d, d ∣ fprod ps → d ∈ gen ps
  | [], _, d, hd => by simp [fprod] at hd; simp [gen, hd]
  | (p, e) :: ps, hp, d, hd => by
      obtain ⟨k1, k2, h1, h2, rfl⟩ := Nat.dvd_mul.mp hd
      obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow (hp (p, e) (by simp))).mp h1
      have := mem_gen_of_dvd ps (fun x hx => hp x (by simp [hx])) k2 h2
      simp only [gen, List.mem_flatMap, List.mem_range, List.mem_map]
      exact ⟨i, by omega, k2, this, rfl⟩

theorem dvd_of_mem_gen : ∀ (ps : List (ℕ × ℕ)) d, d ∈ gen ps → d ∣ fprod ps
  | [], d, hd => by simp [gen] at hd; simp [fprod, hd]
  | (p, e) :: ps, d, hd => by
      simp only [gen, List.mem_flatMap, List.mem_range, List.mem_map] at hd
      obtain ⟨i, hi, y, hy, rfl⟩ := hd
      exact mul_dvd_mul (pow_dvd_pow p (by omega)) (dvd_of_mem_gen ps y hy)

theorem fprod_pos : ∀ (ps : List (ℕ × ℕ)), (∀ x ∈ ps, x.1.Prime) → 0 < fprod ps
  | [], _ => by simp [fprod]
  | (p, e) :: ps, hp => by
      have h1 := (hp (p, e) (by simp)).pos
      have h2 := fprod_pos ps (fun x hx => hp x (by simp [hx]))
      simp only [fprod]; positivity

/-! Od listy do zbiorów dzielników. -/

theorem sumOfDivs_of_lreach (m c k : ℕ) (hm : m ≠ 0) (D : List ℕ) (hnd : D.Nodup)
    (hD : ∀ d ∈ D, d ∣ m) (h : LReach D c k) : SumOfDivs m c k := by
  obtain ⟨l, hl, hlen, rfl⟩ := h
  have hnl : l.Nodup := hnd.sublist hl
  refine ⟨l.toFinset, ?_, ?_, ?_⟩
  · intro x hx
    rw [List.mem_toFinset] at hx
    exact Nat.mem_divisors.mpr ⟨hD x (hl.subset hx), hm⟩
  · rw [List.toFinset_card_of_nodup hnl]; exact hlen
  · rw [List.sum_toFinset _ hnl, List.map_id]

theorem lreach_of_sumOfDivs (m c k : ℕ) (D : List ℕ) (hnd : D.Nodup)
    (hD : ∀ d, d ∣ m → d ∈ D) (h : SumOfDivs m c k) : LReach D c k := by
  obtain ⟨S, hS, hc, rfl⟩ := h
  let l := D.filter (fun x => decide (x ∈ S))
  have hnl : l.Nodup := hnd.filter _
  have hlS : l.toFinset = S := by
    ext x
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hD x (Nat.dvd_of_mem_divisors (hS h)), h⟩⟩
  refine ⟨l, List.filter_sublist, ?_, ?_⟩
  · rw [← List.toFinset_card_of_nodup hnl, hlS]; exact hc
  · rw [← hlS, List.sum_toFinset _ hnl, List.map_id]

/-- Górne ograniczenie z pełnej warstwy `c`. -/
theorem practical_of_check (ps : List (ℕ × ℕ)) (hp : ∀ x ∈ ps, x.1.Prime)
    (hnd : (gen ps).Nodup) (c : ℕ)
    (hc : (run ((1 <<< fprod ps) - 1) (List.replicate (c+1) 1) (gen ps)).getD c 0
            = (1 <<< fprod ps) - 1) :
    PracticalWith (fprod ps) c := by
  set m := fprod ps
  have hm0 : 0 < m := fprod_pos ps hp
  intro k hk1 hkm
  have hG := good_run m _ hm0 (mask_spec m) c (gen ps)
  have hlen : c < (run ((1 <<< m) - 1) (List.replicate (c+1) 1) (gen ps)).length := by
    rw [length_run]; simp
  have hb := (hG c hlen k).mp (by
    rw [List.getD_eq_getElem _ _ hlen] at hc
    rw [hc, mask_spec]; simpa using hkm)
  exact sumOfDivs_of_lreach m c k hm0.ne' (gen ps) hnd (dvd_of_mem_gen ps) hb.2

/-- Dolne ograniczenie: `k0` nie jest sumą ≤ c różnych dzielników. -/
theorem not_practical_of_check (ps : List (ℕ × ℕ)) (hp : ∀ x ∈ ps, x.1.Prime)
    (hnd : (gen ps).Nodup) (c k0 : ℕ) (hk1 : 1 ≤ k0) (hk : k0 < fprod ps)
    (hc : ((run ((1 <<< fprod ps) - 1) (List.replicate (c+1) 1) (gen ps)).getD c 0).testBit k0
            = false) :
    ¬ PracticalWith (fprod ps) c := by
  set m := fprod ps
  intro hP
  have hG := good_run m _ (by omega) (mask_spec m) c (gen ps)
  have hlen : c < (run ((1 <<< m) - 1) (List.replicate (c+1) 1) (gen ps)).length := by
    rw [length_run]; simp
  have hr := lreach_of_sumOfDivs m c k0 (gen ps) hnd (mem_gen_of_dvd ps hp) (hP k0 hk1 hk)
  have := (hG c hlen k0).mpr ⟨hk, hr⟩
  rw [List.getD_eq_getElem _ _ hlen] at hc
  rw [hc] at this; exact absurd this (by simp)

end R6E18
