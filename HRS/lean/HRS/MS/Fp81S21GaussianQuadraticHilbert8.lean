import HRS.MS.Fp81S21GaussianQuadraticHilbert7

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal BigOperators RealInnerProductSpace
open HRS HRS.MC.E213U13 HRS.MS.R26T6
namespace HRS.Fp81.S21

local instance fp81s21_GaussianQuadraticHilbert8_inst1 (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance fp81s21_GaussianQuadraticHilbert8_inst2 (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- A bounded measurable time test yields a second-chaos scalar coordinate
of the retained time-L² representative. -/
theorem fp81s21_TimeL2Rep_InQ2_bounded_test
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ)
    (q : ℝ → Ω → r26t6_Coeff) (M a H : ℝ) (ha : 0 ≤ a) (hH : 0 ≤ H)
    (U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hq : Measurable (Function.uncurry q))
    (hrep : fp81s21_TimeL2Rep P q M a H U)
    (hcoord : ∀ u, 0 ≤ u → MemLp (q u) 2 P ∧ ∀ j, InQ2 hξ (fun ω => q u ω j))
    (v : ℝ → r26t6_Coeff) (hv : Measurable v)
    (hv2 : MemLp v 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (C : ℝ) (hC : 0 ≤ C) (hvbound : ∀ t, ‖v t‖ ≤ C) :
    InQ2 hξ (fun ω => inner ℝ (hv2.toLp v) (U ω)) := by
  let dt : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) H)
  let ℓ : ℝ → r26t6_Coeff →L[ℝ] ℝ := fun t => innerSL ℝ (v t)
  have hnorm : ∀ t, ‖ℓ t‖ ≤ C := fun t => (innerSL_apply_norm ℝ (v t)).le.trans (hvbound t)
  have hmeas : Measurable (fun p : ℝ × r26t6_Coeff => ℓ p.1 p.2) := by
    exact (hv.comp measurable_fst).inner measurable_snd
  have hZ : MemLp (fun ω => inner ℝ (hv2.toLp v) (U ω)) 2 P :=
    hrep.2.1.continuousLinearMap_comp (innerSL ℝ (hv2.toLp v))
  apply fp81s21_TimeL2Rep_InQ2_integral hξ q M a H ha hH U hq hrep hcoord
    ℓ C hC hnorm hmeas hZ
  filter_upwards [hrep.2.2.2] with ω hω
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hv2, hω.2] with t ht hu
  simp [ℓ, ht, hu]

#print axioms fp81s21_TimeL2Rep_InQ2_bounded_test
end HRS.Fp81.S21
end
