import HRS.MS.PsdHeatAux1
import HRS.MS.WrFeat

/-!
# S8.2 R01A (S82R): smoothness of the heat tail `kTau`
`kTau d s tau x = G_0(|x|^2)` with `G_k(v) = int_{t > tau} W(t) (-1/(4t))^k exp(-v/(4t)) dt`, `W(t) = psd3_F d s t 0`.
Differentiation under the integral gives `G_k' = G_{k+1}`; hence `kTau` is `C^infty`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82R
open HRS HRS.MS.Psd

variable {d : ℕ}

/-- `G_k(v)`. -/
def s82r_G (d : ℕ) (s tau : ℝ) (k : ℕ) (v : ℝ) : ℝ :=
  ∫ t in Set.Ioi tau, psd3_F d s t (0 : Euc d) * (-(1 / (4 * t))) ^ k * Real.exp (-(1 / (4 * t)) * v)

lemma s82r_G_bound {s tau : ℝ} (hs : 0 < s) (htau : 0 < tau) (k : ℕ) (v x : ℝ)
    (hx : x ∈ Metric.ball v 1) {t : ℝ} (ht : t ∈ Set.Ioi tau) :
    ‖psd3_F d s t (0 : Euc d) * (-(1 / (4 * t))) ^ k * Real.exp (-(1 / (4 * t)) * x)‖ ≤
      psd3_F d s t (0 : Euc d) * ((1 / (4 * tau)) ^ k * Real.exp ((1 / (4 * tau)) * (|v| + 1))) := by
  have ht' : tau < t := ht
  have ht0 : 0 < t := lt_trans htau ht'
  have hW := psd3_F_nonneg (d := d) hs ht0.le 0
  have hc0 : 0 < 1 / (4 * t) := by positivity
  have hc1 : 1 / (4 * t) ≤ 1 / (4 * tau) := by
    apply one_div_le_one_div_of_le (by positivity); nlinarith
  rw [Metric.mem_ball, Real.dist_eq] at hx
  have hxv : |x| ≤ |v| + 1 := by
    have := abs_sub_abs_le_abs_sub x v
    linarith
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hW, abs_pow, abs_neg, abs_of_pos hc0, abs_of_pos (Real.exp_pos _)]
  have h1 : (1 / (4 * t)) ^ k ≤ (1 / (4 * tau)) ^ k := pow_le_pow_left₀ hc0.le hc1 k
  have h2 : Real.exp (-(1 / (4 * t)) * x) ≤ Real.exp ((1 / (4 * tau)) * (|v| + 1)) := by
    refine Real.exp_le_exp.2 ?_
    have h3 : -(1 / (4 * t)) * x ≤ (1 / (4 * t)) * |x| := by
      have := neg_abs_le x
      nlinarith
    have h4 : (1 / (4 * t)) * |x| ≤ (1 / (4 * tau)) * (|v| + 1) := by
      apply mul_le_mul hc1 hxv (abs_nonneg _) (by positivity)
    linarith
  calc psd3_F d s t (0 : Euc d) * (1 / (4 * t)) ^ k * Real.exp (-(1 / (4 * t)) * x)
      ≤ psd3_F d s t (0 : Euc d) * ((1 / (4 * tau)) ^ k) * Real.exp ((1 / (4 * tau)) * (|v| + 1)) := by
        gcongr
    _ = _ := by ring

lemma s82r_G_hasDerivAt {s tau : ℝ} (hs : 0 < s) (htau : 0 < tau) (k : ℕ) (v : ℝ) :
    HasDerivAt (s82r_G d s tau k) (s82r_G d s tau (k + 1) v) v := by
  have hint := psd3_F_zero_integrableOn (d := d) hs htau
  have hmeasW : Measurable (fun t : ℝ => psd3_F d s t (0 : Euc d)) := psd3_F_meas_t (d := d) s 0
  have hmeas : ∀ (j : ℕ) (x : ℝ), Measurable (fun t : ℝ =>
      psd3_F d s t (0 : Euc d) * (-(1 / (4 * t))) ^ j * Real.exp (-(1 / (4 * t)) * x)) := by
    intro j x
    refine (hmeasW.mul ?_).mul ?_
    · exact (measurable_const.div (measurable_const.mul measurable_id)).neg.pow_const j
    · exact Real.measurable_exp.comp ((measurable_const.div (measurable_const.mul measurable_id)).neg.mul_const x)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ).restrict (Set.Ioi tau))
    (F := fun x t => psd3_F d s t (0 : Euc d) * (-(1 / (4 * t))) ^ k * Real.exp (-(1 / (4 * t)) * x))
    (F' := fun x t => psd3_F d s t (0 : Euc d) * (-(1 / (4 * t))) ^ (k + 1) * Real.exp (-(1 / (4 * t)) * x))
    (x₀ := v)
    (bound := fun t => psd3_F d s t (0 : Euc d) *
      ((1 / (4 * tau)) ^ (k + 1) * Real.exp ((1 / (4 * tau)) * (|v| + 1))))
    (s := Metric.ball v 1) (Metric.ball_mem_nhds v one_pos)
    (Filter.Eventually.of_forall fun x => (hmeas k x).aestronglyMeasurable)
    (by
      refine Integrable.mono' (hint.mul_const ((1 / (4 * tau)) ^ k * Real.exp ((1 / (4 * tau)) * (|v| + 1))))
        (hmeas k v).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact s82r_G_bound hs htau k v v (Metric.mem_ball_self one_pos) ht)
    (hmeas (k + 1) v).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht x hx
      exact s82r_G_bound hs htau (k + 1) v x hx ht)
    (hint.mul_const _)
    (by
      refine Filter.Eventually.of_forall fun t x _ => ?_
      have h1 : HasDerivAt (fun y : ℝ => -(1 / (4 * t)) * y) (-(1 / (4 * t))) x := by
        simpa using (hasDerivAt_id x).const_mul (-(1 / (4 * t)))
      refine (h1.exp.const_mul (psd3_F d s t (0 : Euc d) * (-(1 / (4 * t))) ^ k)).congr_deriv ?_
      · ring)
  exact key.2

lemma s82r_G_contDiff {s tau : ℝ} (hs : 0 < s) (htau : 0 < tau) :
    ∀ (n k : ℕ), ContDiff ℝ (n : WithTop ℕ∞) (s82r_G d s tau k)
  | 0, k => by
      rw [Nat.cast_zero, contDiff_zero]
      exact continuous_iff_continuousAt.2 fun v => (s82r_G_hasDerivAt hs htau k v).continuousAt
  | n + 1, k => by
      rw [Nat.cast_succ, contDiff_succ_iff_deriv]
      refine ⟨fun v => (s82r_G_hasDerivAt hs htau k v).differentiableAt, by simp, ?_⟩
      have : deriv (s82r_G d s tau k) = s82r_G d s tau (k + 1) :=
        funext fun v => (s82r_G_hasDerivAt hs htau k v).deriv
      rw [this]
      exact s82r_G_contDiff hs htau n (k + 1)

lemma s82r_kTau_eq {s tau : ℝ} (hs : 0 < s) (htau : 0 < tau) (x : Euc d) :
    kTau d s tau x = s82r_G d s tau 0 (‖x‖ ^ 2) := by
  unfold kTau s82r_G
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := lt_trans htau ht
  rw [psd3_F_eq_gauss ht0 x]
  simp

theorem s82r_kTau_contDiff {s tau : ℝ} (hs : 0 < s) (htau : 0 < tau) :
    ContDiff ℝ ∞ (kTau d s tau) := by
  have h : kTau d s tau = fun x : Euc d => s82r_G d s tau 0 (‖x‖ ^ 2) :=
    funext fun x => s82r_kTau_eq hs htau x
  rw [h]
  exact (contDiff_infty.2 fun n => s82r_G_contDiff hs htau n 0).comp (contDiff_norm_sq ℝ)

end HRS.MS.S82R

end
