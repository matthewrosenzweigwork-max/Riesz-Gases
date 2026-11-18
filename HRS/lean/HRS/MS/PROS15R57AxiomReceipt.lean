import HRS.MS.PROS15dSpectralGaussianTransferR56
import HRS.MS.PROS15dTestGaussianBridgeC19

/-!
Round57 root-side exact-type and axiom acceptance receipt.
Both mathematics declarations were independently reviewed by NONAUTHORS.
Does not assert the original frozen S15d, S15e, or S2.1(iii).
-/
set_option autoImplicit false
noncomputable section
namespace HRS.MS.R26T3

theorem r57_spectral_L2_exact_type :
    type_of% @HRS.MS.R26T3.s15d_physical_riesz_finite_spectral_L2_gaussian := by
  exact s15d_physical_riesz_finite_spectral_L2_gaussian

theorem r57_spatial_L2_exact_type :
    type_of% @HRS.MS.R26T3.s15d_physical_tilted_gaussian_of_spatial_approximation := by
  exact s15d_physical_tilted_gaussian_of_spatial_approximation

#print axioms HRS.MS.R26T3.s15d_physical_riesz_finite_spectral_L2_gaussian
#print axioms HRS.MS.R26T3.s15d_physical_tilted_gaussian_of_spatial_approximation
#print axioms HRS.MS.R26T3.r57_spectral_L2_exact_type
#print axioms HRS.MS.R26T3.r57_spatial_L2_exact_type
end HRS.MS.R26T3
