import HRS.MS.PROS15dFiniteLinearGaussian
import HRS.MS.PROS15dPhysicalLinearSpectral
import HRS.MS.PROS15dGaussianLimitB18

/-! Root acceptance: R56 A10/B18 type/axiom closure receipts. -/
set_option autoImplicit false
noncomputable section
open HRS.MS.R26T3

#check @s15d_finite_spectral_linear_gaussian
#check @s15d_physical_riesz_linear_spectral_gaussian
#check @s15d_centered_gaussian_in_measure_limit
#check @s15d_centered_gaussian_L2_limit
#print axioms s15d_finite_spectral_linear_gaussian
#print axioms s15d_physical_riesz_linear_spectral_gaussian
#print axioms s15d_centered_gaussian_in_measure_limit
#print axioms s15d_centered_gaussian_L2_limit

end
