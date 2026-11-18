import HRS.MS.ThCorrRespAux2
import HRS.MS.ThCorrFarAux2
import HRS.MS.S81G_Sing
import HRS.MS.S21F_D02

/-!
# S21F, packet R26-T3.S14: Hilbert-Schmidt interaction and determinant control

(i) `g(x-y) ∈ L²(μ⊗μ)` for `μ = ρ dx` with `ρ ≤ M`, finite second moment, `0 ≤ s < d/2`:
near the diagonal `g² ≤ C ‖z‖^{-2a}` (`a = s` for `s > 0`, `a = 1/4` for `s = 0`, `2a < d`) is integrable on the unit ball and
`ρ ≤ M`; away from it `g² ≤ ‖z‖² ≤ 2‖x‖²+2‖y‖²`.  (ii) `0 ≤ x - log(1+x) ≤ x²`, `x ≥ 0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.R26T3
open HRS HRS.Whole

theorem s21f_log_sq_near {r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    Real.log r ^ 2 ≤ 16 * r ^ (-(1 / 2 : ℝ)) := by
  set t := r ^ (-(1 / 4 : ℝ)) with ht
  have htp : 0 < t := Real.rpow_pos_of_pos h0 _
  have hl : Real.log t = -(1 / 4) * Real.log r := by rw [ht, Real.log_rpow h0]
  have hlt := Real.log_le_sub_one_of_pos htp
  have hneg : Real.log r < 0 := Real.log_neg h0 h1
  have h2 : -Real.log r ≤ 4 * t := by nlinarith
  have h3 : t ^ 2 = r ^ (-(1 / 2 : ℝ)) := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul h0.le]; norm_num
  calc Real.log r ^ 2 = (-Real.log r) ^ 2 := by ring
    _ ≤ (4 * t) ^ 2 := by gcongr; linarith
    _ = 16 * r ^ (-(1 / 2 : ℝ)) := by rw [← h3]; ring

theorem s21f_riesz_sq_far {d : ℕ} {s : ℝ} (hs0 : 0 ≤ s) (z : Euc d) (hz : 1 ≤ ‖z‖) :
    rieszKernel d s z ^ 2 ≤ ‖z‖ ^ 2 := by
  unfold rieszKernel
  by_cases h : s = 0
  · simp only [h, if_true, neg_sq]
    have h0 : 0 ≤ Real.log ‖z‖ := Real.log_nonneg hz
    have h1 : Real.log ‖z‖ ≤ ‖z‖ := by linarith [Real.log_le_sub_one_of_pos (lt_of_lt_of_le one_pos hz)]
    exact pow_le_pow_left₀ h0 h1 2
  · simp only [h, if_false]
    have h1 : ‖z‖ ^ (-s) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hz (by linarith [lt_of_le_of_ne hs0 (Ne.symm h)])
    have h2 : 0 ≤ ‖z‖ ^ (-s) := by positivity
    nlinarith [sq_nonneg ‖z‖]

theorem s21f_riesz_sq_ball {d : ℕ} (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) :
    IntegrableOn (fun z : Euc d => rieszKernel d s z ^ 2) (ball 0 1) volume := by
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hfr : Module.finrank ℝ (Euc d) = d := by simp
  have hmeas : Measurable (fun z : Euc d => rieszKernel d s z ^ 2) :=
    (HRS.MS.S81G.s81g_riesz_meas s).pow_const 2
  by_cases h : s = 0
  · refine integrableOn_ball_of_norm_le_rpow (C := 16) (α := 1 / 2) (by rw [hfr]; omega) ?_ ?_
      hmeas.aestronglyMeasurable
    · rw [hfr]; linarith
    · rw [ae_restrict_iff' measurableSet_ball]
      haveI : Nontrivial (Euc d) := by
        rw [← Module.finrank_pos_iff (R := ℝ), hfr]; omega
      have hne : ∀ᵐ z : Euc d ∂(volume : Measure (Euc d)), z ≠ 0 := by
        rw [ae_iff]; simpa using measure_singleton (0 : Euc d)
      filter_upwards [hne] with z hz hzb
      have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
      have hz1 : ‖z‖ < 1 := by simpa using hzb
      have := s21f_log_sq_near hzn hz1
      unfold rieszKernel
      simp only [h, if_true, neg_sq, norm_pow, Real.norm_eq_abs, sq_abs]
      simpa [neg_div] using this
  · have hsp : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h)
    refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := 2 * s) (by rw [hfr]; omega) ?_ ?_
      hmeas.aestronglyMeasurable
    · rw [hfr]; linarith
    · refine Eventually.of_forall fun z => ?_
      unfold rieszKernel
      simp only [h, if_false, Real.norm_eq_abs, one_mul]
      rw [abs_of_nonneg (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
      apply le_of_eq; congr 1; push_cast; ring

theorem s21f_hs_kernel {d : ℕ} (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M)
    (hm2 : Integrable (fun y : Euc d => ‖y‖ ^ 2) (HRS.Whole.withDensityReal ρ)) :
    MemLp (fun z : Euc d × Euc d => rieszKernel d s (z.1 - z.2)) 2
      ((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) := by
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hgm : Measurable (fun z : Euc d × Euc d => rieszKernel d s (z.1 - z.2)) :=
    (HRS.MS.S81G.s81g_riesz_meas s).comp (measurable_fst.sub measurable_snd)
  rw [memLp_two_iff_integrable_sq hgm.aestronglyMeasurable]
  refine ⟨(hgm.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => sq_nonneg _)]
  set N : Euc d → ℝ≥0∞ := (ball (0 : Euc d) 1).indicator (fun z => ENNReal.ofReal (rieszKernel d s z ^ 2))
    with hN
  have hGm : Measurable (fun z : Euc d => rieszKernel d s z ^ 2) :=
    (HRS.MS.S81G.s81g_riesz_meas s).pow_const 2
  have hNm : Measurable N :=
    (ENNReal.measurable_ofReal.comp hGm).indicator measurableSet_ball
  have hJ : ∫⁻ z, N z < ⊤ := by
    rw [hN, lintegral_indicator measurableSet_ball]
    exact (s21f_riesz_sq_ball hd hs0 hs).lintegral_lt_top
  have hpt : ∀ x y : Euc d, ENNReal.ofReal (rieszKernel d s (x - y) ^ 2) ≤
      N (x - y) + ENNReal.ofReal (2 * ‖x‖ ^ 2) + ENNReal.ofReal (2 * ‖y‖ ^ 2) := by
    intro x y
    by_cases hz : ‖x - y‖ < 1
    · have : N (x - y) = ENNReal.ofReal (rieszKernel d s (x - y) ^ 2) := by
        rw [hN]; exact indicator_of_mem (by simpa using hz) _
      rw [this, add_assoc]; exact le_self_add
    · have h1 := s21f_riesz_sq_far hs0 (x - y) (not_lt.1 hz)
      have h2 : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
        nlinarith [norm_sub_le x y, sq_nonneg (‖x‖ - ‖y‖), norm_nonneg x, norm_nonneg y]
      calc ENNReal.ofReal (rieszKernel d s (x - y) ^ 2) ≤ ENNReal.ofReal (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) :=
            ENNReal.ofReal_le_ofReal (h1.trans h2)
        _ = ENNReal.ofReal (2 * ‖x‖ ^ 2) + ENNReal.ofReal (2 * ‖y‖ ^ 2) :=
            ENNReal.ofReal_add (by positivity) (by positivity)
        _ ≤ N (x - y) + ENNReal.ofReal (2 * ‖x‖ ^ 2) + ENNReal.ofReal (2 * ‖y‖ ^ 2) := by
            gcongr
            exact (le_add_self : ENNReal.ofReal (2 * ‖x‖ ^ 2) ≤ N (x - y) + ENNReal.ofReal (2 * ‖x‖ ^ 2))
  have hNs : Measurable (fun p : Euc d × Euc d => N (p.1 - p.2)) :=
    hNm.comp (measurable_fst.sub measurable_snd)
  have h1m : Measurable (fun p : Euc d × Euc d => ENNReal.ofReal (2 * ‖p.1‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp (((measurable_norm.comp measurable_fst).pow_const 2).const_mul 2)
  have h2m : Measurable (fun p : Euc d × Euc d => ENNReal.ofReal (2 * ‖p.2‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp (((measurable_norm.comp measurable_snd).pow_const 2).const_mul 2)
  have hc : ∫⁻ y, ENNReal.ofReal (2 * ‖y‖ ^ 2) ∂μ < ⊤ := (hm2.const_mul 2).lintegral_lt_top
  have hA : ∫⁻ p, N (p.1 - p.2) ∂(μ.prod μ) < ⊤ := by
    rw [lintegral_prod _ hNs.aemeasurable]
    have hin : ∀ x : Euc d, ∫⁻ y, N (x - y) ∂μ ≤ ENNReal.ofReal M * (∫⁻ z, N z) := by
      intro x
      have hf : Measurable (fun y : Euc d => N (x - y)) := hNm.comp (measurable_const.sub measurable_id)
      rw [hμ, HRS.Whole.withDensityReal, lintegral_withDensity_eq_lintegral_mul _
        (f := fun x => ENNReal.ofReal (ρ x)) (ENNReal.measurable_ofReal.comp hρ.measurable) hf]
      calc ∫⁻ y, ((fun x => ENNReal.ofReal (ρ x)) * fun y => N (x - y)) y
          ≤ ∫⁻ y, ENNReal.ofReal M * N (x - y) := lintegral_mono fun y => by
            exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hM y)) _
        _ = ENNReal.ofReal M * ∫⁻ y, N (x - y) := lintegral_const_mul _ hf
        _ = _ := by
            rw [(volume : Measure (Euc d)).measurePreserving_sub_left x |>.lintegral_comp hNm]
    calc ∫⁻ x, ∫⁻ y, N (x - y) ∂μ ∂μ ≤ ∫⁻ x, ENNReal.ofReal M * (∫⁻ z, N z) ∂μ := lintegral_mono hin
      _ < ⊤ := by
        rw [lintegral_const, measure_univ, mul_one]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hJ
  have hB : ∫⁻ p, ENNReal.ofReal (2 * ‖p.1‖ ^ 2) ∂(μ.prod μ) < ⊤ := by
    rw [lintegral_prod _ h1m.aemeasurable]
    simpa using hc
  have hC : ∫⁻ p, ENNReal.ofReal (2 * ‖p.2‖ ^ 2) ∂(μ.prod μ) < ⊤ := by
    rw [lintegral_prod _ h2m.aemeasurable]
    simpa using hc
  calc ∫⁻ p, ENNReal.ofReal (rieszKernel d s (p.1 - p.2) ^ 2) ∂(μ.prod μ)
      ≤ ∫⁻ p, (N (p.1 - p.2) + ENNReal.ofReal (2 * ‖p.1‖ ^ 2) + ENNReal.ofReal (2 * ‖p.2‖ ^ 2)) ∂(μ.prod μ) :=
        lintegral_mono fun p => hpt p.1 p.2
    _ = _ := by rw [lintegral_add_right _ h2m, lintegral_add_right _ h1m]
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨hA, hB⟩, hC⟩

theorem s21f_log_sub_summable {γ : ℝ} (hγ : 0 ≤ γ) (l : ℕ → ℝ) (hl : ∀ j, 0 ≤ l j)
    (hs : Summable fun j => l j ^ 2) : Summable fun j => γ * l j - Real.log (1 + γ * l j) := by
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) (hs.mul_left (γ ^ 2))
  · have hx : 0 ≤ γ * l j := mul_nonneg hγ (hl j)
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + γ * l j by linarith)
    linarith
  · have hx : 0 ≤ γ * l j := mul_nonneg hγ (hl j)
    have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + γ * l j by linarith)
    set x := γ * l j with hxd
    have h2 : x - Real.log (1 + x) ≤ x - (1 - (1 + x)⁻¹) := by linarith
    have h3 : x - (1 - (1 + x)⁻¹) = x ^ 2 / (1 + x) := by field_simp; ring
    have h4 : x ^ 2 / (1 + x) ≤ x ^ 2 := div_le_self (sq_nonneg _) (by linarith)
    calc x - Real.log (1 + x) ≤ x ^ 2 := h2.trans (h3 ▸ h4)
      _ = γ ^ 2 * l j ^ 2 := by rw [hxd]; ring

theorem r26t3_interaction_hs {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) :
    MemLp (fun z : Euc p.d × Euc p.d => rieszKernel p.d p.s (z.1 - z.2)) 2
      ((r26t3_mu R 0).prod (r26t3_mu R 0)) ∧
    ∀ l : ℕ → ℝ, (∀ j, 0 ≤ l j) → Summable (fun j => l j ^ 2) →
      Summable (fun j => p.γ * l j - Real.log (1 + p.γ * l j)) := by
  refine ⟨?_, fun l hl hs => s21f_log_sub_summable p.hγ l hl hs⟩
  obtain ⟨-, -, -, href⟩ := r26t3_reference_data p δ hδ hδh R
  obtain ⟨M₀, c, S, hc, hTc⟩ := href 0
  refine s21f_hs_kernel p.hd p.hs0 p.hs hTc.prob (M := |M₀|) (fun x => ?_)
    (HRS.MS.TcF.tc4_sq_integrable hTc hc)
  calc R.ρ 0 x ≤ M₀ * Real.exp (-c * ‖x‖ ^ 2) := hTc.gauss x
    _ ≤ |M₀| * Real.exp (-c * ‖x‖ ^ 2) := mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
    _ ≤ |M₀| * 1 := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖])) (abs_nonneg _)
    _ = |M₀| := mul_one _

end HRS.MS.R26T3
