import HRS.MS.S111K4Q1

/-!
# S11.1 / T03 (S11K4): continuity estimate for the triple integral, bounds along a classical orbit, bound of the forcing
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4

open HRS HRS.Whole
open HRS.MS.S111X1 (KData Wf kA kG_measurable prod_integrable_kernel)

section Trip

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

theorem k4_toL_norm_le {f : X → ℝ} {B : ℝ} (hB0 : 0 ≤ B) (hf : MemLp f 2 μ) (hB : ∀ᵐ x ∂μ, |f x| ≤ B) :
    ‖k4_toL μ f‖ ≤ B := by
  rw [k4_toL_eq hf, Lp.norm_toLp]
  have h1 : eLpNorm f 2 μ ≤ ENNReal.ofReal B := by
    have := eLpNorm_le_of_ae_bound (p := 2) (μ := μ) (f := f) (C := B) hf.aestronglyMeasurable
      (hB.mono fun x hx => by simpa [Real.norm_eq_abs] using hx)
    simpa using this
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rwa [ENNReal.toReal_ofReal hB0] at this

/-- `|∫ a'b'c' - ∫ abc| ≤ B² (‖a'-a‖₂ + ‖b'-b‖₂ + ‖c'-c‖₂)` for bounded `L²` functions. -/
theorem k4_trip_diff {a a' b b' c c' : X → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (ha : MemLp a 2 μ) (ha' : MemLp a' 2 μ) (hb : MemLp b 2 μ) (hb' : MemLp b' 2 μ)
    (hc : MemLp c 2 μ) (hc' : MemLp c' 2 μ)
    (hBa : ∀ᵐ x ∂μ, |a x| ≤ B) (hBb : ∀ᵐ x ∂μ, |b x| ≤ B) (hBb' : ∀ᵐ x ∂μ, |b' x| ≤ B)
    (hBc' : ∀ᵐ x ∂μ, |c' x| ≤ B) :
    |(∫ x, a' x * b' x * c' x ∂μ) - ∫ x, a x * b x * c x ∂μ| ≤
      B ^ 2 * (‖k4_toL μ a' - k4_toL μ a‖ + ‖k4_toL μ b' - k4_toL μ b‖ + ‖k4_toL μ c' - k4_toL μ c‖) := by
  have hB2 : 0 ≤ B ^ 2 := sq_nonneg _
  have hda : MemLp (fun x => a' x - a x) 2 μ := ha'.sub ha
  have hdb : MemLp (fun x => b' x - b x) 2 μ := hb'.sub hb
  have hdc : MemLp (fun x => c' x - c x) 2 μ := hc'.sub hc
  have m1 : MemLp (fun x => b' x * c' x) 2 μ := k4_mul_memLp hc' hb'.aestronglyMeasurable hBb'
  have m2 : MemLp (fun x => a x * c' x) 2 μ := k4_mul_memLp hc' ha.aestronglyMeasurable hBa
  have m3 : MemLp (fun x => a x * b x) 2 μ := k4_mul_memLp hb ha.aestronglyMeasurable hBa
  have b1 : ∀ᵐ x ∂μ, |b' x * c' x| ≤ B ^ 2 := by
    filter_upwards [hBb', hBc'] with x h1 h2
    rw [abs_mul, sq]; exact mul_le_mul h1 h2 (abs_nonneg _) hB0
  have b2 : ∀ᵐ x ∂μ, |a x * c' x| ≤ B ^ 2 := by
    filter_upwards [hBa, hBc'] with x h1 h2
    rw [abs_mul, sq]; exact mul_le_mul h1 h2 (abs_nonneg _) hB0
  have b3 : ∀ᵐ x ∂μ, |a x * b x| ≤ B ^ 2 := by
    filter_upwards [hBa, hBb] with x h1 h2
    rw [abs_mul, sq]; exact mul_le_mul h1 h2 (abs_nonneg _) hB0
  have n1 := k4_toL_norm_le hB2 m1 b1
  have n2 := k4_toL_norm_le hB2 m2 b2
  have n3 := k4_toL_norm_le hB2 m3 b3
  have i1 : Integrable (fun x => (a' x - a x) * (b' x * c' x)) μ := hda.integrable_mul m1
  have i2 : Integrable (fun x => (b' x - b x) * (a x * c' x)) μ := hdb.integrable_mul m2
  have i3 : Integrable (fun x => (c' x - c x) * (a x * b x)) μ := hdc.integrable_mul m3
  have iF1 : Integrable (fun x => a' x * b' x * c' x) μ :=
    (ha'.integrable_mul m1).congr (Filter.Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
  have iF2 : Integrable (fun x => a x * b x * c x) μ :=
    (hc.integrable_mul m3).congr (Filter.Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
  have iAB : Integrable (fun x => (a' x - a x) * (b' x * c' x) + (b' x - b x) * (a x * c' x)) μ := i1.add i2
  have e : (∫ x, a' x * b' x * c' x ∂μ) - ∫ x, a x * b x * c x ∂μ =
      (∫ x, (a' x - a x) * (b' x * c' x) ∂μ) + (∫ x, (b' x - b x) * (a x * c' x) ∂μ) +
        ∫ x, (c' x - c x) * (a x * b x) ∂μ := by
    rw [← integral_sub iF1 iF2, ← integral_add i1 i2, ← integral_add iAB i3]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [e, ← k4_inner_toL hda m1, ← k4_inner_toL hdb m2, ← k4_inner_toL hdc m3, k4_toL_sub ha' ha,
    k4_toL_sub hb' hb, k4_toL_sub hc' hc]
  have c1 := abs_real_inner_le_norm (k4_toL μ a' - k4_toL μ a) (k4_toL μ (fun x => b' x * c' x))
  have c2 := abs_real_inner_le_norm (k4_toL μ b' - k4_toL μ b) (k4_toL μ (fun x => a x * c' x))
  have c3 := abs_real_inner_le_norm (k4_toL μ c' - k4_toL μ c) (k4_toL μ (fun x => a x * b x))
  calc _ ≤ _ := abs_add_three _ _ _
    _ ≤ ‖k4_toL μ a' - k4_toL μ a‖ * B ^ 2 + ‖k4_toL μ b' - k4_toL μ b‖ * B ^ 2 +
        ‖k4_toL μ c' - k4_toL μ c‖ * B ^ 2 := by
        refine add_le_add (add_le_add (c1.trans ?_) (c2.trans ?_)) (c3.trans ?_)
        · exact mul_le_mul_of_nonneg_left n1 (norm_nonneg _)
        · exact mul_le_mul_of_nonneg_left n2 (norm_nonneg _)
        · exact mul_le_mul_of_nonneg_left n3 (norm_nonneg _)
    _ = _ := by ring

end Trip

end HRS.MS.S111K4
