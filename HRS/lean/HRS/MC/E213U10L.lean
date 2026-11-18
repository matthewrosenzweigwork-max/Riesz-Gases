import HRS.MC.E213U10K
import HRS.MC.S7FCH4B
import HRS.MC.S7UCZ

/-!
# Packet e213u10, part L: continuity of the pair-space functionals and the coupling bounds

`𝔅 = 𝒳_{r,L} × L²([0,L];E_r)`.  `u10_FD_cont`, `u10_FJ_cont`: continuity; `u10_FD_coupling`, `u10_GJ_coupling`: the bounds
`|∫F dμ₁ - ∫G dμ₂| ≲ W₂` along a coupling `π` using only moments of the first marginal; `u10_abs_integral_le`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U10

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ}

theorem u10_continuous_of_lip {E : Type*} [NormedAddCommGroup E] (f : E → ℝ) (K : E → ℝ)
    (h : ∀ x x', |f x - f x'| ≤ K x * ‖x - x'‖) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x' => ?_
  refine Metric.continuousAt_iff.2 fun ε hε => ?_
  have hK : 0 < |K x'| + 1 := by positivity
  refine ⟨ε / (|K x'| + 1), by positivity, fun x hx => ?_⟩
  rw [dist_eq_norm] at hx
  rw [Real.dist_eq]
  have h1 := h x' x
  rw [abs_sub_comm] at h1
  calc |f x - f x'| ≤ K x' * ‖x' - x‖ := by rw [abs_sub_comm]; exact h x' x
    _ ≤ |K x'| * ‖x - x'‖ := by
        rw [norm_sub_rev]
        exact mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    _ ≤ (|K x'| + 1) * ‖x - x'‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (|K x'| + 1) * (ε / (|K x'| + 1)) := mul_lt_mul_of_pos_left hx hK
    _ = ε := by field_simp

theorem u10_abs_integral_le {B : Type*} [MeasurableSpace B] (μ : Measure B) [IsProbabilityMeasure μ] (f ν : B → ℝ)
    (hf : Measurable f) (hν : Measurable ν) (hν0 : ∀ x, 0 ≤ ν x) (k M : ℝ) (hk : 0 ≤ k) (hM : 0 ≤ M)
    (hbd : ∀ x, |f x| ≤ k * ν x) (hν2 : MemLp ν 2 μ) (hM2 : ∫ x, ν x ^ 2 ∂μ ≤ M ^ 2) :
    |∫ x, f x ∂μ| ≤ k * M := by
  have hint : Integrable ν μ := hν2.integrable (by norm_num)
  have h1 : |∫ x, f x ∂μ| ≤ ∫ x, k * ν x ∂μ := by
    rw [← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le (hint.const_mul k) (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hbd x)
  have h2 : ∫ x, ν x ∂μ ≤ M := by
    have := u10_cs μ ν (fun _ => 1) hν0 (fun _ => zero_le_one) hν2 (by exact memLp_const 1) M 1 hM zero_le_one hM2
      (by simp)
    simpa using this
  rw [integral_const_mul] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hk)

section PairSpace

variable (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ)
  (hΦ : MemCb 5 Φ) (hcb : cbNorm 5 Φ ≤ 1) (b L : ℝ) (hb : 0 ≤ b) (hL : 0 ≤ L) (hH : a + T ≤ b + L)

include hT hΦ hcb hb in
theorem u10_FD_cont (CD CY : ℝ) (hCD0 : 0 ≤ CD) (hCY0 : 0 ≤ CY) (hCD : U10_DriftNear hE T a ha b CD)
    (hCY : U10_PredBound hE T a ha CY) :
    Continuous (u10_FD hE T a ha Φ b L hL hH) := by
  refine u10_continuous_of_lip _ (fun x => CD * CY * Real.sqrt L * ‖x.2‖ + CD * Real.sqrt L) (fun x x' => ?_)
  refine (u10_FD_lip_core hE T hT a ha Φ hΦ hcb b L hL hH CD CY hCD0 hCY0 hCD hCY x x').trans ?_
  have h1 : ‖x.1 - x'.1‖ ≤ ‖x - x'‖ := by simpa using norm_fst_le (x - x')
  have h2 : ‖x.2 - x'.2‖ ≤ ‖x - x'‖ := by simpa using norm_snd_le (x - x')
  have hs := Real.sqrt_nonneg L
  have e : (CD * CY * Real.sqrt L * ‖x.2‖ + CD * Real.sqrt L) * ‖x - x'‖ =
      CD * CY * Real.sqrt L * ‖x.2‖ * ‖x - x'‖ + CD * Real.sqrt L * ‖x - x'‖ := by ring
  rw [e]
  refine add_le_add ?_ ?_
  · have : 0 ≤ CD * CY * Real.sqrt L * ‖x.2‖ := by positivity
    calc CD * CY * Real.sqrt L * ‖x.1 - x'.1‖ * ‖x.2‖ = CD * CY * Real.sqrt L * ‖x.2‖ * ‖x.1 - x'.1‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 this
  · exact mul_le_mul_of_nonneg_left h2 (by positivity)

include hT hΦ hcb hb in
theorem u10_FJ_cont (CJ CY : ℝ) (hCJ0 : 0 ≤ CJ) (hCY0 : 0 ≤ CY) (hJ : U10_JNear hE T a ha b CJ)
    (hCY : U10_PredBound hE T a ha CY) :
    Continuous (u10_FJ hE T a ha Φ b L hL hH) := by
  refine u10_continuous_of_lip _ (fun x => CJ * L * (CY * ‖x.2‖ + 1)) (fun x x' => ?_)
  refine (u10_FJ_lip_core hE T hT a ha Φ hΦ hcb b L hb hL hH CJ CY hCJ0 hCY0 hJ hCY x x').trans ?_
  have h1 : ‖x.1 - x'.1‖ ≤ ‖x - x'‖ := by simpa using norm_fst_le (x - x')
  have h2 : ‖x.2 - x'.2‖ ≤ ‖x - x'‖ := by simpa using norm_snd_le (x - x')
  have hCJL : 0 ≤ CJ * L := mul_nonneg hCJ0 hL
  have e : CJ * L * (CY * ‖x.2‖ + 1) * ‖x - x'‖ =
      CJ * L * (CY * ‖x.2‖ * ‖x - x'‖ + ‖x - x'‖) := by ring
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ hCJL
  have : CY * ‖x.1 - x'.1‖ * ‖x.2‖ ≤ CY * ‖x.2‖ * ‖x - x'‖ := by
    calc CY * ‖x.1 - x'.1‖ * ‖x.2‖ = CY * ‖x.2‖ * ‖x.1 - x'.1‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
  linarith

end PairSpace

end HRS.MC.E213U10

end
