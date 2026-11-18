import HRS.MS.PROS15dRieszPhysicalSpanCovF26
import HRS.MS.PROS15dPhysicalFiniteCovF26

/-!
# Independent nonauthor review of physical S15d finite covariance F26

The four exact-type consumers do not strengthen or weaken the authored
declarations. No frozen S15d or S2.1(iii) theorem is claimed.
-/
set_option autoImplicit false
noncomputable section
namespace HRS.MS.R26T3

theorem r61_f26_scalar_exact :
    type_of% @HRS.MS.R26T3.s15d_finite_spectral_scalar_covariance := by
  exact s15d_finite_spectral_scalar_covariance

theorem r61_f26_physical_coordinates_exact :
    type_of% @HRS.MS.R26T3.s15d_physical_riesz_finite_scalar_covariance := by
  exact s15d_physical_riesz_finite_scalar_covariance

theorem r61_f26_spatial_span_exact :
    type_of% @HRS.MS.R26T3.s15d_physical_finite_span_scalar_covariance := by
  exact s15d_physical_finite_span_scalar_covariance

theorem r61_f26_riesz_span_exact :
    type_of% @HRS.MS.R26T3.s15d_physical_riesz_spatial_span_covariance := by
  exact s15d_physical_riesz_spatial_span_covariance

#print axioms s15d_finite_spectral_scalar_covariance
#print axioms s15d_physical_riesz_finite_scalar_covariance
#print axioms s15d_physical_finite_span_scalar_covariance
#print axioms s15d_physical_riesz_spatial_span_covariance
#print axioms r61_f26_scalar_exact
#print axioms r61_f26_physical_coordinates_exact
#print axioms r61_f26_spatial_span_exact
#print axioms r61_f26_riesz_span_exact

end HRS.MS.R26T3
