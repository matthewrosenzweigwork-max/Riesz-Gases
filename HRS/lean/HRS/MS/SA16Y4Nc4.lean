import HRS.MS.SA16Y4Tl2

/-!
# S.A.16 (SA16Y4) Nc4: dominated convergence in `L^q` for functions with a common power decay

`sa16y4_Lq_dominated`: continuous `f_n → g` pointwise with `|f_n|, |g| ≤ K (1+‖x‖)^{-r}`, `d < r`, `q` finite with `1 ≤ q.toReal`:
`‖f_n - g‖_{L^q} → 0`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R

section Nc4
variable {d : ℕ}

theorem sa16y4_Lq_dominated {q : ℝ≥0∞} (hq : q ≠ ⊤) (hq1 : 1 ≤ q.toReal) {K r : ℝ} (hr : (d : ℝ) < r)
    (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : ∀ n, Continuous (f n)) (hg : Continuous g)
    (hfb : ∀ n x, |f n x| ≤ K * (1 + ‖x‖) ^ (-r)) (hgb : ∀ x, |g x| ≤ K * (1 + ‖x‖) ^ (-r))
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => (eLpNorm (fun x => f n x - g x) q volume).toReal) atTop (𝓝 0) := by
  set q' := q.toReal with hq'
  have hq'0 : 0 < q' := by linarith
  have hq0 : q ≠ 0 := by intro h; rw [hq'] at hq'0; simp [h] at hq'0
  have hK : 0 ≤ K := by
    have := (abs_nonneg (g 0)).trans (hgb 0)
    have h1 : 0 < (1 + ‖(0 : EuclideanSpace ℝ (Fin d))‖) ^ (-r) := by simp
    by_contra hneg
    push_neg at hneg
    nlinarith
  have hr0 : 0 < r := lt_of_le_of_lt (Nat.cast_nonneg d) hr
  have hint : Integrable (fun x : EuclideanSpace ℝ (Fin d) => (1 + ‖x‖) ^ (-(r * q'))) := by
    refine integrable_one_add_norm (E := EuclideanSpace ℝ (Fin d)) (μ := volume) ?_
    rw [finrank_euclideanSpace_fin]
    nlinarith
  set c : ℝ := 2 * K with hc
  have hc0 : 0 ≤ c := by positivity
  have hdom : ∀ n x, ‖f n x - g x‖ ^ q' ≤ c ^ q' * (1 + ‖x‖) ^ (-(r * q')) := by
    intro n x
    have h1 : ‖f n x - g x‖ ≤ c * (1 + ‖x‖) ^ (-r) := by
      rw [Real.norm_eq_abs]
      calc |f n x - g x| ≤ |f n x| + |g x| := abs_sub _ _
        _ ≤ 2 * K * (1 + ‖x‖) ^ (-r) := by linarith [hfb n x, hgb x]
    have hx1 : 0 ≤ (1 + ‖x‖) := by positivity
    calc ‖f n x - g x‖ ^ q' ≤ (c * (1 + ‖x‖) ^ (-r)) ^ q' := Real.rpow_le_rpow (norm_nonneg _) h1 hq'0.le
      _ = c ^ q' * (1 + ‖x‖) ^ (-(r * q')) := by
        rw [Real.mul_rpow hc0 (Real.rpow_nonneg hx1 _), ← Real.rpow_mul hx1]
        congr 2; ring
  have hI : Tendsto (fun n => ∫ x, ‖f n x - g x‖ ^ q') atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
      (F := fun n x => ‖f n x - g x‖ ^ q') (f := fun _ => (0 : ℝ))
      (fun x => c ^ q' * (1 + ‖x‖) ^ (-(r * q')))
      (fun n => ((((hf n).sub hg).norm).rpow_const (fun _ => Or.inr hq'0.le)).aestronglyMeasurable)
      (hint.const_mul _)
      (fun n => Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]; exact hdom n x)
      (Eventually.of_forall fun x => by
        have h0 : Tendsto (fun n => ‖f n x - g x‖) atTop (𝓝 0) := by
          have := ((hlim x).sub_const (g x)).norm
          simpa using this
        have := h0.rpow_const (p := q') (Or.inr hq'0.le)
        simpa [Real.zero_rpow hq'0.ne'] using this)
    simpa using this
  have hfin : ∀ n, eLpNorm (fun x => f n x - g x) q volume =
      ENNReal.ofReal ((∫ x, ‖f n x - g x‖ ^ q') ^ (1 / q')) := by
    intro n
    have hI1 : Integrable (fun x => ‖f n x - g x‖ ^ q') :=
      (hint.const_mul (c ^ q')).mono' ((((hf n).sub hg).norm.rpow_const (fun _ => Or.inr hq'0.le)).aestronglyMeasurable)
        (Eventually.of_forall fun x => by
          rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]; exact hdom n x)
    have e1 : ∫⁻ x, ‖f n x - g x‖ₑ ^ q' = ∫⁻ x, ENNReal.ofReal (‖f n x - g x‖ ^ q') :=
      lintegral_congr fun x => by
        rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq'0.le]
    have hmeas : AEStronglyMeasurable (fun x => f n x - g x) volume := ((hf n).sub hg).aestronglyMeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq hmeas, e1,
      ← ofReal_integral_eq_lintegral_ofReal hI1 (Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _),
      ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _)
        (by positivity), one_div]
  simp_rw [hfin]
  have h2 := hI.rpow_const (p := 1 / q') (Or.inr (by positivity))
  rw [Real.zero_rpow (by positivity)] at h2
  refine h2.congr fun n => ?_
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _)]

end Nc4

end HRS.Whole.AppendixA.Phase2SA16R
