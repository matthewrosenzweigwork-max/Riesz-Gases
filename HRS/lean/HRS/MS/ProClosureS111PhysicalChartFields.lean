import HRS.MS.ProClosureS111ChartMass
import HRS.MS.ProClosureS111SharedThermalLaw
import HRS.MS.ProClosureS111WeightedChart
import HRS.MS.R2ChaosAux42

/-!
An actual producer of all seven fields of the frozen PhysicalChartFields
structure. The raw jointly measurable coefficient fields and their product
L2 moments are constructed from the thermal traces and physical Gaussian
law. The constant-test argument proves their zero mass almost everywhere;
orthogonal projection then gives the exact all-point mass field without
changing their vector L2 classes or any almost-everywhere-time coordinate.

The final theorem also constructs the chart, native compact zero-mean
basis, and shared-noise path-pair probability measure from physical data.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.R2Chaos HRS.MS.S111T

variable {d r : ℕ} {Pw : ℝ}

theorem coeff_field_sections_memLp {Time Omega : Type*}
    [MeasurableSpace Time] [MeasurableSpace Omega]
    (dt : Measure Time) [SFinite dt] (P : Measure Omega) [SFinite P]
    (q : Time × Omega → r26t6_Coeff) (hqm : Measurable q)
    (hq : MemLp q 2 (dt.prod P)) :
    ∀ᵐ t ∂dt, MemLp (fun w => q (t,w)) 2 P := by
  letI : TopologicalSpace.SeparableSpace r26t6_Coeff :=
    HRS.StaticLimitAux.separable_lp (ι := ℕ)
  letI : SecondCountableTopology r26t6_Coeff :=
    UniformSpace.secondCountable_of_separable r26t6_Coeff
  have hi : Integrable (fun p => ‖q p‖ ^ 2) (dt.prod P) :=
    (memLp_two_iff_integrable_sq_norm hq.aestronglyMeasurable).1 hq
  filter_upwards [hi.prod_right_ae] with t ht
  exact (memLp_two_iff_integrable_sq_norm
    (hqm.comp (measurable_prodMk_left (x := t))).aestronglyMeasurable).2 ht

/-- Exact D02 fields for any actual physical Gaussian realization and
any valid frozen weighted chart. No field, trace, centering, or L2 bound
is assumed beyond the physical law and joint measurability of that law. -/
theorem physical_chart_fields_for_evolution (hd : 2 ≤ d)
    (s a beta gamma H : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hgamma : 0 ≤ gamma)
    (hr : (2 : ℝ) + (d : ℝ) / 2 < r) (hP : (d : ℝ) < 2 * Pw)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d s a beta rho)
    (Omega : Type) [MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (Z : ℝ → Omega → OscDual d (wholeSpaceIndex d))
    (hZ : IsLinearGaussianEvolutionW P (r26t6_thermalCoeff d s a beta rho)
      (wholeSpaceIndex d) beta⁻¹ H
      (HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal rho) gamma) Z)
    (hZm : Measurable (fun p : ℝ × Omega => Z p.1 p.2))
    (E : r26t6_WeightedChart d r Pw) (basis : ℕ → Euc d → ℝ)
    (hbasis : IsR2ZeroMeanONB (HRS.Whole.withDensityReal rho) basis) :
    ∃ qLin qQuad : ℝ × Omega → r26t6_Coeff,
      r26t6_PhysicalChartFields P rho s H E basis Z qLin qQuad := by
  letI : TopologicalSpace.SeparableSpace r26t6_Coeff :=
    HRS.StaticLimitAux.separable_lp (ι := ℕ)
  letI : SecondCountableTopology r26t6_Coeff :=
    UniformSpace.secondCountable_of_separable r26t6_Coeff
  let dt : Measure ℝ := volume.restrict (Icc (0 : ℝ) H)
  obtain ⟨qL, qQ, hLm, hQm, hL2, hQ2, hLcoord, hQcoord⟩ :=
    physical_chart_coordinate_fields hd s a beta gamma H hs0 hs ha hbeta hgamma
      hr hP rho hrho Omega P Z hZ hZm E basis hbasis
  let c : r26t6_Coeff := E.encode (fun _ => 1)
  have hLmass : ∀ᵐ p ∂dt.prod P, inner ℝ (qL p) c = 0 := by
    have hm : Measurable (fun p => inner ℝ (qL p) c) := hLm.inner measurable_const
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hm measurable_const)).2
    filter_upwards [coeff_field_sections_memLp dt P qL hLm hL2, hLcoord,
      ae_restrict_mem measurableSet_Icc] with t hLt hcoords ht
    exact physical_chart_linear_mass_zero hd s a beta gamma H hs0 hs ha hbeta hgamma
      hr hP rho hrho Omega P Z hZ E t ht (fun w => qL (t,w)) hLt hcoords
  have hQmass : ∀ᵐ p ∂dt.prod P, inner ℝ (qQ p) c = 0 := by
    have hm : Measurable (fun p => inner ℝ (qQ p) c) := hQm.inner measurable_const
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hm measurable_const)).2
    filter_upwards [coeff_field_sections_memLp dt P qQ hQm hQ2, hQcoord,
      ae_restrict_mem measurableSet_Icc] with t hQt hcoords ht
    exact physical_chart_quadratic_mass_zero hd s a beta gamma H hs0 hs ha hbeta hgamma
      hr hP rho hrho Omega P Z hZ E t ht basis hbasis (fun w => qQ (t,w)) hQt hcoords
  obtain ⟨qLin, hLinm, hLin2, hLin0, heL⟩ :=
    exists_exact_zero_mass_field (dt.prod P) qL hLm hL2 c hLmass
  obtain ⟨qQuad, hQuadm, hQuad2, hQuad0, heQ⟩ :=
    exists_exact_zero_mass_field (dt.prod P) qQ hQm hQ2 c hQmass
  refine ⟨qLin, qQuad, {
    linear_measurable := hLinm
    quadratic_measurable := hQuadm
    linear_moment := hLin2
    quadratic_moment := hQuad2
    mass_zero := fun p => ⟨hLin0 p, hQuad0 p⟩
    linear_coordinates := ?_
    wick_coordinates := ?_
  }⟩
  · filter_upwards [Measure.ae_ae_of_ae_prod heL, hLcoord] with t ht hcoord j
    filter_upwards [ht, hcoord j] with w hw hc
    rw [hw]
    exact hc
  · filter_upwards [Measure.ae_ae_of_ae_prod heQ, hQcoord] with t ht hcoord j
    apply wick_congr_ae (hcoord j)
    filter_upwards [ht] with w hw
    rw [hw]

/-- Actual paired physical fields, on the same constructed path-pair
probability space with independent preparations and common noise. The
chart may be fixed before density, preparation, or horizon. -/
theorem physical_shared_chart_fields (hd : 2 ≤ d)
    (s a beta gamma H : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hgamma : 0 ≤ gamma) (hH : 0 < H)
    (hr : (2 : ℝ) + (d : ℝ) / 2 < r) (hP : (d : ℝ) < 2 * Pw)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d s a beta rho)
    (E : r26t6_WeightedChart d r Pw) :
    ∃ P : Measure (PathPair d (wholeSpaceIndex d) H), ∃ hprob : IsProbabilityMeasure P,
      r26t6_SharedThermalLaw P s a beta gamma H rho
        (pairedProcess d (wholeSpaceIndex d) H hH.le) ∧
      ∃ basis : ℕ → Euc d → ℝ, IsR2ZeroMeanONB (HRS.Whole.withDensityReal rho) basis ∧
      ∃ qLin qQuad : Fin 2 → ℝ × PathPair d (wholeSpaceIndex d) H → r26t6_Coeff,
        ∀ i, @r26t6_PhysicalChartFields d r Pw (PathPair d (wholeSpaceIndex d) H) _
          P hprob rho s H E basis (pairedProcess d (wholeSpaceIndex d) H hH.le i)
          (qLin i) (qQuad i) := by
  obtain ⟨P, hprob, hZ⟩ := physical_shared_thermal_law hd s a beta gamma H
    hs0 hs ha hbeta hgamma hH rho hrho
  letI : IsProbabilityMeasure P := hprob
  obtain ⟨M, L, c, hR, hG⟩ := HRS.MS.R2S11.s11_thermal_round2 hd hs0 hs ha hbeta hrho
  obtain ⟨basis, hbasis⟩ := s94_exists_onb hd hR
  have hfields : ∀ i : Fin 2, ∃ qLin qQuad : ℝ × PathPair d (wholeSpaceIndex d) H → r26t6_Coeff,
      r26t6_PhysicalChartFields P rho s H E basis
        (pairedProcess d (wholeSpaceIndex d) H hH.le i) qLin qQuad := by
    intro i
    have hp : 0 ≤ r26t6_preparation beta gamma i := by
      unfold r26t6_preparation
      split_ifs
      · exact hgamma
      · exact hbeta.le
    exact physical_chart_fields_for_evolution hd s a beta (r26t6_preparation beta gamma i) H
      hs0 hs ha hbeta hp hr hP rho hrho (PathPair d (wholeSpaceIndex d) H) P
      (pairedProcess d (wholeSpaceIndex d) H hH.le i) (hZ.evolution i)
      (pairedProcess_joint_continuous d (wholeSpaceIndex d) H hH.le i).measurable
      E basis hbasis
  choose qLin qQuad hfields using hfields
  exact ⟨P, hprob, hZ, basis, hbasis, qLin, qQuad, hfields⟩

/-- A fully physical existence theorem: the frozen chart, common path
probability space, native spatial basis, and both normalized field pairs
are all constructed. -/
theorem physical_weighted_chart_fields (hd : 2 ≤ d)
    (s a beta gamma H : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hgamma : 0 ≤ gamma) (hH : 0 < H)
    (hr : (2 : ℝ) + (d : ℝ) / 2 < r) (hP : (d : ℝ) < 2 * Pw)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d s a beta rho) :
    ∃ E : r26t6_WeightedChart d r Pw,
    ∃ P : Measure (PathPair d (wholeSpaceIndex d) H), ∃ hprob : IsProbabilityMeasure P,
      r26t6_SharedThermalLaw P s a beta gamma H rho
        (pairedProcess d (wholeSpaceIndex d) H hH.le) ∧
      ∃ basis : ℕ → Euc d → ℝ, IsR2ZeroMeanONB (HRS.Whole.withDensityReal rho) basis ∧
      ∃ qLin qQuad : Fin 2 → ℝ × PathPair d (wholeSpaceIndex d) H → r26t6_Coeff,
        ∀ i, @r26t6_PhysicalChartFields d r Pw (PathPair d (wholeSpaceIndex d) H) _
          P hprob rho s H E basis (pairedProcess d (wholeSpaceIndex d) H hH.le i)
          (qLin i) (qQuad i) := by
  obtain ⟨E⟩ := physical_weighted_chart (r := r) (by omega : 0 < d) hP
  exact ⟨E, physical_shared_chart_fields hd s a beta gamma H hs0 hs ha hbeta hgamma hH
    hr hP rho hrho E⟩

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.physical_chart_fields_for_evolution
#print axioms HRS.MS.ProClosureS111.physical_shared_chart_fields
#print axioms HRS.MS.ProClosureS111.physical_weighted_chart_fields
