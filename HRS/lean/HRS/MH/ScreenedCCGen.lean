import HRS.MH.ScreenedA1
import HRS.MH.ScreenedA7
import HRS.MH.ScreenedK3Aux1

/-!
# Generic near-field estimate for the cutoff commutators (helpers of `cc_near1`, `cc_near2`)

`cc_gen`: a kernel `g x y` with `‖g x y‖ ≤ M · 1_{|x-y| ≤ R} |x-y|^{-p} · G y` for `x ∈ T` gives the
`L²` bound of `x ↦ ∫ g x y dy` on `T` by Young (`young_l1_l2_proof`) and `lintegral_ball_rpow_le_proof`,
and a.e. integrability of `g x ·` once the right side is finite.
`cc_cover`: a set `S` covered by cells `Q i` with weights `w i ≥ 1` on the cover gives
`∫⁻ 1_S f ≤ ∑' w i ∫⁻ 1_{Q i} f`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

/-- Cover estimate: a set covered by the cells with weight `≥ 1` (`w i`). -/
lemma cc_cover {ι : Type*} [Countable ι] (S : Set (Euc d)) (Q : ι → Set (Euc d))
    (hQm : ∀ i, MeasurableSet (Q i)) (w : ι → ℝ≥0∞) (f : Euc d → ℝ≥0∞) (hf : Measurable f)
    (hcov : ∀ y ∈ S, ∃ i, 1 ≤ w i ∧ y ∈ Q i) :
    ∫⁻ y, S.indicator f y ≤ ∑' i, w i * ∫⁻ y, (Q i).indicator f y := by
  calc ∫⁻ y, S.indicator f y ≤ ∫⁻ y, ∑' i, w i * (Q i).indicator f y := by
        apply lintegral_mono
        intro y
        by_cases hy : y ∈ S
        · obtain ⟨i, hi1, hiy⟩ := hcov y hy
          rw [indicator_of_mem hy]
          calc f y ≤ w i * f y := le_mul_of_one_le_left zero_le hi1
            _ = w i * (Q i).indicator f y := by rw [indicator_of_mem hiy]
            _ ≤ ∑' j, w j * (Q j).indicator f y := ENNReal.le_tsum (f := fun j => w j * (Q j).indicator f y) i
        · rw [indicator_of_notMem hy]
          exact zero_le
    _ = ∑' i, ∫⁻ y, w i * (Q i).indicator f y := by
        apply lintegral_tsum
        intro i
        exact (measurable_const.mul (hf.indicator (hQm i))).aemeasurable
    _ = ∑' i, w i * ∫⁻ y, (Q i).indicator f y := by
        congr 1
        funext i
        exact lintegral_const_mul _ (hf.indicator (hQm i))

/-- The square of the `enorm` of an indicator is the indicator of the square. -/
lemma cc_sq_indicator (Q : Set (Euc d)) (f : Euc d → ℝ) (y : Euc d) :
    ‖Q.indicator f y‖ₑ ^ 2 = Q.indicator (fun y => ‖f y‖ₑ ^ 2) y := by
  by_cases hy : y ∈ Q
  · rw [indicator_of_mem hy, indicator_of_mem hy]
  · rw [indicator_of_notMem hy, indicator_of_notMem hy]
    simp

/-- The Young-type `L²` estimate for kernels bounded by `M 1_{|u| ≤ R} |u|^{-p}` (generic form). -/
theorem cc_gen (hd : 1 ≤ d) {p : ℝ} (hp : p < d) :
    ∃ CK : ℝ, 0 < CK ∧ ∀ (T : Set (Euc d)) (g : Euc d → Euc d → ℝ) (G : Euc d → ℝ≥0∞) (M R : ℝ),
      0 ≤ M → 0 < R → Measurable G → Measurable (fun q : Euc d × Euc d => g q.1 q.2) →
      (∀ x ∈ T, ∀ y, y ≠ x → ‖g x y‖ₑ ≤ ENNReal.ofReal M *
          (Metric.closedBall (0 : Euc d) R).indicator (fun u => ENNReal.ofReal (‖u‖ ^ (-p))) (x - y) * G y) →
      (∫⁻ x, (T.indicator (fun _ => (1 : ℝ≥0∞)) x * ‖∫ y, g x y‖ₑ) ^ 2) ≤
          (ENNReal.ofReal (M * CK * R ^ ((d : ℝ) - p))) ^ 2 * ∫⁻ y, G y ^ 2 ∧
      ((ENNReal.ofReal (M * CK * R ^ ((d : ℝ) - p))) ^ 2 * ∫⁻ y, G y ^ 2 < ⊤ →
        ∀ᵐ x ∂(volume : Measure (Euc d)), x ∈ T → Integrable (fun y => g x y)) := by
  obtain ⟨CK0, hCK0, hCKb⟩ := lintegral_ball_rpow_le_proof hd hp
  refine ⟨max CK0 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro T g G M R hM hR hGm hgm hbd
  set e : ℝ := (d : ℝ) - p with he
  set CK : ℝ := max CK0 1 with hCKdef
  set K : Euc d → ℝ≥0∞ := (Metric.closedBall (0 : Euc d) R).indicator
    (fun u => ENNReal.ofReal (‖u‖ ^ (-p))) with hKdef
  have hKm : Measurable K :=
    (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)).indicator measurableSet_closedBall
  have hKint : ∫⁻ u, K u ≤ ENNReal.ofReal (CK0 * R ^ e) := by
    rw [hKdef, lintegral_indicator measurableSet_closedBall]
    exact hCKb R hR
  have hKle : ∫⁻ u, K u ≤ ENNReal.ofReal (CK * R ^ e) := by
    refine hKint.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hR.le _)
  have hKfin : ∫⁻ u, K u ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKle
  -- the right-hand side as a function of x
  set J : Euc d → ℝ≥0∞ := fun x => ∫⁻ y, K (x - y) * G y with hJdef
  have hY : ∫⁻ x, (J x) ^ 2 ≤ (∫⁻ u, K u) ^ 2 * ∫⁻ y, G y ^ 2 :=
    young_l1_l2_proof K G hKm hGm hKfin
  -- pointwise bound of the integral by `M J`
  have hnorm : ∀ x ∈ T, ‖∫ y, g x y‖ₑ ≤ ENNReal.ofReal M * J x := by
    intro x hx
    calc ‖∫ y, g x y‖ₑ ≤ ∫⁻ y, ‖g x y‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ y, ENNReal.ofReal M * (K (x - y) * G y) := by
          apply lintegral_mono_ae
          filter_upwards [k3_ae_ne hd x] with y hy
          rw [← mul_assoc]
          exact hbd x hx y hy
      _ = ENNReal.ofReal M * J x := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hJm : Measurable J := by
    have hF : Measurable (fun q : Euc d × Euc d => K (q.1 - q.2) * G q.2) :=
      (hKm.comp (measurable_fst.sub measurable_snd)).mul (hGm.comp measurable_snd)
    exact hF.lintegral_prod_right'
  have hpt : ∀ x, (T.indicator (fun _ => (1 : ℝ≥0∞)) x * ‖∫ y, g x y‖ₑ) ^ 2 ≤
      (ENNReal.ofReal M) ^ 2 * (J x) ^ 2 := by
    intro x
    by_cases hx : x ∈ T
    · rw [indicator_of_mem hx, one_mul, ← mul_pow]
      exact pow_le_pow_left₀ zero_le (hnorm x hx) 2
    · rw [indicator_of_notMem hx]
      simp
  refine ⟨?_, ?_⟩
  · calc ∫⁻ x, (T.indicator (fun _ => (1 : ℝ≥0∞)) x * ‖∫ y, g x y‖ₑ) ^ 2
          ≤ ∫⁻ x, (ENNReal.ofReal M) ^ 2 * (J x) ^ 2 := lintegral_mono hpt
        _ = (ENNReal.ofReal M) ^ 2 * ∫⁻ x, (J x) ^ 2 :=
          lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
        _ ≤ (ENNReal.ofReal M) ^ 2 * ((∫⁻ u, K u) ^ 2 * ∫⁻ y, G y ^ 2) :=
          mul_le_mul_of_nonneg_left hY zero_le
        _ ≤ (ENNReal.ofReal M) ^ 2 * ((ENNReal.ofReal (CK * R ^ e)) ^ 2 * ∫⁻ y, G y ^ 2) := by
          gcongr
        _ = (ENNReal.ofReal (M * CK * R ^ e)) ^ 2 * ∫⁻ y, G y ^ 2 := by
          rw [← mul_assoc, ← mul_pow, ← ENNReal.ofReal_mul hM]
          congr 2
          rw [mul_assoc]
  · intro hP
    by_cases hM0 : M = 0
    · refine ae_of_all _ (fun x hx => ?_)
      have hz : ∀ᵐ y ∂(volume : Measure (Euc d)), g x y = 0 := by
        filter_upwards [k3_ae_ne hd x] with y hy
        have h1 := hbd x hx y hy
        rw [hM0, ENNReal.ofReal_zero, zero_mul, zero_mul] at h1
        exact enorm_eq_zero.1 (le_antisymm h1 zero_le)
      exact (integrable_zero (Euc d) ℝ volume).congr (hz.mono fun y hy => hy.symm)
    · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
      have hc : 0 < ENNReal.ofReal (M * CK * R ^ e) :=
        ENNReal.ofReal_pos.2 (by positivity)
      have hG2 : ∫⁻ y, G y ^ 2 < ⊤ := by
        by_contra h
        rw [not_lt, top_le_iff] at h
        have htop : (ENNReal.ofReal (M * CK * R ^ e)) ^ 2 * ∫⁻ y, G y ^ 2 = ⊤ := by
          rw [h]
          exact ENNReal.mul_top (pow_ne_zero 2 hc.ne')
        exact hP.ne htop
      have hJ2 : ∫⁻ x, (J x) ^ 2 < ⊤ := by
        refine lt_of_le_of_lt hY (ENNReal.mul_lt_top ?_ hG2)
        exact ENNReal.pow_lt_top (lt_of_le_of_lt hKle ENNReal.ofReal_lt_top)
      filter_upwards [ae_lt_top (hJm.pow_const 2) hJ2.ne] with x hxJ hx
      have hJx : J x < ⊤ := by
        by_contra h
        rw [not_lt, top_le_iff] at h
        simp [h] at hxJ
      have hmeas : Measurable (fun y => g x y) := hgm.comp measurable_prodMk_left
      refine ⟨hmeas.aestronglyMeasurable, ?_⟩
      have hle : ∫⁻ y, ‖g x y‖ₑ ≤ ∫⁻ y, ENNReal.ofReal M * (K (x - y) * G y) := by
        apply lintegral_mono_ae
        filter_upwards [k3_ae_ne hd x] with y hy
        rw [← mul_assoc]
        exact hbd x hx y hy
      have hfin : ∫⁻ y, ‖g x y‖ₑ < ⊤ := by
        refine lt_of_le_of_lt hle ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hJx
      exact hfin

end HRS.MH.Screened
