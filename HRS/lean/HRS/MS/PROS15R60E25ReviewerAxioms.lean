import HRS.MS.PROS15dRieszSmoothTestsE25
import HRS.MS.PROS15dActualAllTestGaussianE25

/-!
Independent nonauthor exact-type consumers for the five E25 declarations.
No original S15d or S2.1(iii) closure is claimed.
-/
set_option autoImplicit false
noncomputable section
namespace HRS.MS.R26T3

theorem e25_review_spatial_exact :
    type_of% @HRS.MS.R26T3.s15d_physical_hilbert_spatial_projection_L2 := by
  exact s15d_physical_hilbert_spatial_projection_L2
theorem e25_review_centered_classes_exact :
    type_of% @HRS.MS.R26T3.s15d_physical_riesz_all_centered_L2_gaussian := by
  exact s15d_physical_riesz_all_centered_L2_gaussian
theorem e25_review_centered_reps_exact :
    type_of% @HRS.MS.R26T3.s15d_hilbert_spectral_tilted_centered_test_gaussian := by
  exact s15d_hilbert_spectral_tilted_centered_test_gaussian
theorem e25_review_actual_centered_exact :
    type_of% @HRS.MS.R26T3.s15d_physical_riesz_every_centered_test_gaussian := by
  exact s15d_physical_riesz_every_centered_test_gaussian
theorem e25_review_smooth_original_exact :
    type_of% @HRS.MS.R26T3.s15d_physical_riesz_all_R2_tests_gaussian := by
  exact s15d_physical_riesz_all_R2_tests_gaussian

#print axioms s15d_physical_hilbert_spatial_projection_L2
#print axioms s15d_physical_riesz_all_centered_L2_gaussian
#print axioms s15d_hilbert_spectral_tilted_centered_test_gaussian
#print axioms s15d_physical_riesz_every_centered_test_gaussian
#print axioms s15d_physical_riesz_all_R2_tests_gaussian
#print axioms e25_review_spatial_exact
#print axioms e25_review_centered_classes_exact
#print axioms e25_review_centered_reps_exact
#print axioms e25_review_actual_centered_exact
#print axioms e25_review_smooth_original_exact

end HRS.MS.R26T3
