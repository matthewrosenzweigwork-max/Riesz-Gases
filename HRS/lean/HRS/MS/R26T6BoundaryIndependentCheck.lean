import HRS.MS.R26T6BoundaryCheck

/-! Independent reviewer: exact D00–D03 structure/definition family, not existence of thermal fields. -/
set_option autoImplicit false
noncomputable section
open HRS.MS.R26T6

example (d : ℕ) : r26t6_coreOrder d = 2 * d + 8 := rfl
example (d : ℕ) : r26t6_coreWeight d = (d : ℝ) + 2 := rfl

#print axioms r26t6_thermalCoeff
#print axioms r26t6_clock
#print axioms r26t6_unitTrace
#print axioms r26t6_wickFinite
#print axioms r26t6_screenedForcing
#print axioms r26t6_centeredSquare
#print axioms r26t6_dirichlet
#print axioms r26t6_weightedL
#print axioms r26t6_testSpace
#print axioms r26t6_ResponseForm
#print axioms r26t6_ShiftedJValue
#print axioms r26t6_WeightedChart
#print axioms r26t6_ChartedOrbits
#print axioms r26t6_obs
#print axioms r26t6_driftInsertion
#print axioms r26t6_SourceContractions
#print axioms r26t6_hermiteSection
#print axioms r26t6_OscOrbitApprox
#print axioms r26t6_AllDriftCoordinates
#print axioms r26t6_AllShiftedJValue
#print axioms r26t6_PhysicalChartFields
#print axioms r26t6_TimeCoeff
#print axioms r26t6_coefficientField
#print axioms r26t6_IntervalOperators
#print axioms r26t6_timeCoeffOf
#print axioms r26t6_randomDrift
#print axioms r26t6_randomCovariance
#print axioms r26t6_pairedProcess
#print axioms r26t6_preparation
#print axioms r26t6_SharedThermalLaw
#print axioms r26t6_coreOrder
#print axioms r26t6_coreWeight
#print axioms r26t6_InitialCoordinates
