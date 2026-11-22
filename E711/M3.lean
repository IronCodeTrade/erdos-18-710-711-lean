import R6E711Core
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace R6E711
def cs3 : List (List ℕ) := [[1,2,3],[2,4,3],[3,4,6],[5,4,6],[5,8,6],[6,8,9]]
theorem up3 (m : ℕ) : f 3 m ≤ 5 :=
  f_le_all (P := 6) (by norm_num) (by decide +kernel) cs3 (by decide +kernel) (by decide +kernel) m
/-- max_m f(3,m) = 5 = 2·3-1 -/
theorem max3 : (∀ m, f 3 m ≤ 5) ∧ f 3 4 = 5 :=
  ⟨up3, le_antisymm (up3 _) (f_sq_ge 3 (by norm_num))⟩
end R6E711
#print axioms R6E711.max3
