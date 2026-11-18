import HRS.MS.PROS15dPhysicalRieszCovIndependent

/-! Independent exact-type and axiom consumer of the Round54 reviewer's
physical spectral covariance theorem.  This proof uses no extra hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace HRS.MS.R26T3

theorem a12_r54_exact_type :
    type_of% @HRS.MS.R26T3.r54_physical_riesz_tilt_spectral_covariance := by
  exact r54_physical_riesz_tilt_spectral_covariance

#print axioms HRS.MS.R26T3.r54_physical_riesz_tilt_spectral_covariance
#print axioms HRS.MS.R26T3.a12_r54_exact_type
end HRS.MS.R26T3
