import R6E711Core
set_option maxRecDepth 1000000
namespace R6E711
/-- f(17, 485749) = 34 > 2·17-1: wzorzec max_m f(n,m) = 2n-1 łamie się przy n = 17 -/
theorem f17 : f 17 485749 = 34 :=
  le_antisymm (f_le_of (good_of_upperOK (bs := [485750, 485752, 485751, 485756, 485755, 485754, 485765, 485768, 485757, 485770, 485782, 485760, 485771, 485772, 485775, 485776, 485758]) (by decide +kernel)))
    (le_f_of (not_good_of_hallOK (S := [11, 12, 13, 14, 15, 17]) (T := [485758, 485760, 485771, 485772, 485775]) (by decide +kernel)) (by norm_num))
theorem f17_gt : ∃ m, 2 * 17 - 1 < f 17 m := ⟨485749, by rw [f17]; norm_num⟩
end R6E711
#print axioms R6E711.f17
#print axioms R6E711.f17_gt
