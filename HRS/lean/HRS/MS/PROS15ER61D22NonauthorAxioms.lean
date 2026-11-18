import HRS.MS.PROS15ERecenterActualD22

/-! Independent nonauthor exact-type review of the five D22 declarations.
Only the Hilbert--Schmidt spectral assertion is checked, not frozen S15e. -/
set_option autoImplicit false
noncomputable section
namespace HRS.MS.R26T3

theorem d22_review_scalar_bound :
    type_of% @HRS.MS.R26T3.s15e_recenter_scalar_abs_bound := by
  exact s15e_recenter_scalar_abs_bound
theorem d22_review_scalar_summable :
    type_of% @HRS.MS.R26T3.s15e_recenter_scalar_summable := by
  exact s15e_recenter_scalar_summable
theorem d22_review_finite_wick :
    type_of% @HRS.MS.R26T3.s15e_finite_wick_recentering := by
  exact s15e_finite_wick_recentering
theorem d22_review_L2_convergence :
    type_of% @HRS.MS.R26T3.s15e_recenter_L2_convergence := by
  exact s15e_recenter_L2_convergence
theorem d22_review_actual_HS :
    type_of% @HRS.MS.R26T3.s15e_hs_recentered_tilted_L2 := by
  exact s15e_hs_recentered_tilted_L2

#print axioms s15e_recenter_scalar_abs_bound
#print axioms s15e_recenter_scalar_summable
#print axioms s15e_finite_wick_recentering
#print axioms s15e_recenter_L2_convergence
#print axioms s15e_hs_recentered_tilted_L2
#print axioms d22_review_scalar_bound
#print axioms d22_review_scalar_summable
#print axioms d22_review_finite_wick
#print axioms d22_review_L2_convergence
#print axioms d22_review_actual_HS
end HRS.MS.R26T3
