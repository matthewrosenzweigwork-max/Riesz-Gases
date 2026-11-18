import HRS.MS.PROS15dPhysicalTiltConvergence
import HRS.MS.PROS15dActualGaussian

/-! Separate nonauthor check of the *supporting* spectral and physical Gaussian-tilt lemmas.
No part of the frozen S15d susceptibility theorem is asserted here. -/
set_option autoImplicit false
noncomputable section

#print axioms HRS.MS.R26T3.s15d_pi_gaussian_coord_second
#print axioms HRS.MS.R26T3.s15d_pi_gaussian_covariance
#print axioms HRS.MS.R26T3.s15d_actual_spectral_covariance
#print axioms HRS.MS.R26T3.s15d_actual_tilt_square_integrable
#print axioms HRS.MS.R26T3.s15d_weighted_square_integrable
#print axioms HRS.MS.R26T3.s15d_L4_to_tilted_L2
#print axioms HRS.MS.R26T3.s15d_tilted_second_moment_bound
#print axioms HRS.MS.R26T3.s15d_tilted_L2_tendsto_of_L4
#print axioms HRS.MS.R26T3.s15d_centered_gaussian_product
#print axioms HRS.MS.R26T3.s15d_actual_tilt_finite_spectral_gaussian
#print axioms HRS.MS.R26T3.s15d_physical_first_chaos_L4
#print axioms HRS.MS.R26T3.s15d_physical_first_chaos_tilt_L2
#print axioms HRS.MS.R26T3.s15d_physical_centered_gaussian_law
#print axioms HRS.MS.R26T3.s15d_physical_fourth_eq_three_sq_second
#print axioms HRS.MS.R26T3.s15d_physical_fourth_le_three_spatial_second_sq
#print axioms HRS.MS.R26T3.s15d_physical_tilted_second_bound
#print axioms HRS.MS.R26T3.s15d_physical_tilted_second_tendsto_of_spatial_second
