import R6E711Core
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace R6E711
def cs4 : List (List ℕ) := [[1,2,3,4],[2,6,3,4],[3,4,6,8],[4,6,9,8],[5,6,9,8],[6,10,9,8],[7,8,9,12],[8,10,9,12],[10,14,9,12],[10,14,15,12],[11,12,15,16],[12,14,15,16]]
theorem up4 (m : ℕ) : f 4 m ≤ 7 :=
  f_le_all (P := 12) (by norm_num) (by decide +kernel) cs4 (by decide +kernel) (by decide +kernel) m
/-- max_m f(4,m) = 7 = 2·4-1 -/
theorem max4 : (∀ m, f 4 m ≤ 7) ∧ f 4 9 = 7 :=
  ⟨up4, le_antisymm (up4 _) (f_sq_ge 4 (by norm_num))⟩
end R6E711
#print axioms R6E711.max4
