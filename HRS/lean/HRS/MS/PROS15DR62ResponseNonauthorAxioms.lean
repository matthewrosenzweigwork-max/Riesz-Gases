import HRS.MS.PROS15dCenteredResponseSeriesR60
import HRS.MS.PROS15dSusceptibilityEigenR60

/-! Independent review consumers for original-resolvent spectral series. -/
set_option autoImplicit false
noncomputable section
namespace HRS.MS.R26T3
theorem r62_review_eigenvector :
    type_of% @HRS.MS.R26T3.s15d_positive_resolvent_eigenvector := by
  exact s15d_positive_resolvent_eigenvector
theorem r62_review_eigenfamily :
    type_of% @HRS.MS.R26T3.s15d_positive_resolvent_eigenfamily_covariance := by
  exact s15d_positive_resolvent_eigenfamily_covariance
theorem r62_review_physical_eigen :
    type_of% @HRS.MS.R26T3.s15d_susceptibility_on_physical_eigenfunctions := by
  exact s15d_susceptibility_on_physical_eigenfunctions
theorem r62_review_series :
    type_of% @HRS.MS.R26T3.s15d_positive_resolvent_alltest_spectral_series := by
  exact s15d_positive_resolvent_alltest_spectral_series
theorem r62_review_centered_series :
    type_of% @HRS.MS.R26T3.s15d_susceptibility_alltest_centered_eigenbasis_series := by
  exact s15d_susceptibility_alltest_centered_eigenbasis_series

#print axioms s15d_positive_resolvent_eigenvector
#print axioms s15d_positive_resolvent_eigenfamily_covariance
#print axioms s15d_susceptibility_on_physical_eigenfunctions
#print axioms s15d_positive_resolvent_alltest_spectral_series
#print axioms s15d_susceptibility_alltest_centered_eigenbasis_series
#print axioms r62_review_eigenvector
#print axioms r62_review_eigenfamily
#print axioms r62_review_physical_eigen
#print axioms r62_review_series
#print axioms r62_review_centered_series
end HRS.MS.R26T3
