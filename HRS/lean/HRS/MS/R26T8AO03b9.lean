import HRS.MS.R26T8AO03b8

/-!
# S8.2 T8A O03b (part 9): linearity of `aSource`; integrable gaussians and the truncated pole
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U HRS.MS.S82W HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_o03b_gauss_int {b : ℝ} (hb : 0 < b) : Integrable (fun v : Euc d => Real.exp (-b * ‖v‖ ^ 2)) := by
  have := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Euc d)
    (b := (b : ℂ)) (by simpa using hb) 0 0
  have h2 := this.norm
  refine h2.congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [zero_mul, add_zero]
  rw [Complex.norm_exp]
  have : (-(b : ℂ) * (‖v‖ : ℂ) ^ 2).re = -b * ‖v‖ ^ 2 := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [this]

theorem r26t8a_o03b_ind_int (hd : 2 ≤ d) {s : ℝ} (hsd : s < d) :
    Integrable ((Metric.ball (0 : Euc d) 1).indicator (fun z : Euc d => ‖z‖ ^ (-s))) := by
  have hd1 : 1 ≤ d := by omega
  have hfin : 1 ≤ Module.finrank ℝ (Euc d) := by
    rw [finrank_euclideanSpace_fin]; exact hd1
  have hα : s < (Module.finrank ℝ (Euc d) : ℝ) := by
    rw [finrank_euclideanSpace_fin]; exact hsd
  have hmeas : AEStronglyMeasurable (fun z : Euc d => ‖z‖ ^ (-s)) volume :=
    ((measurable_norm.pow_const (-s))).aestronglyMeasurable
  have hon : IntegrableOn (fun z : Euc d => ‖z‖ ^ (-s)) (Metric.ball (0 : Euc d) 1) volume :=
    integrableOn_ball_of_norm_le_rpow hfin hα
      (Filter.Eventually.of_forall fun x => by
        rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)])
      hmeas
  exact (integrable_indicator_iff measurableSet_ball).2 hon

theorem r26t8a_o03b_aSource_add (mu : Measure (Euc d)) {f g : Euc d → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hif : ∀ x, Integrable (hSource f x) mu) (hig : ∀ x, Integrable (hSource g x) mu) :
    aSource mu (f + g) = aSource mu f + aSource mu g := by
  funext x
  unfold aSource
  have : hSource (f + g) x = hSource f x + hSource g x := funext fun y => r26t8a_o03b_hs_add hf hg x y
  simp only [Pi.add_apply]
  rw [this]
  simp only [Pi.add_apply]
  rw [integral_add (hif x) (hig x)]
  ring

theorem r26t8a_o03b_aSource_smul (mu : Measure (Euc d)) (c : ℝ) {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) :
    aSource mu (c • f) = c • aSource mu f := by
  funext x
  unfold aSource
  have : hSource (c • f) x = fun y => c * hSource f x y := funext fun y => r26t8a_o03b_hs_smul c hf x y
  rw [this, integral_const_mul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end HRS.MS.R26T8A
