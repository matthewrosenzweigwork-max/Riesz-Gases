import HRS.Commutator.Whole.XNRSAux26

/-!
# Packet X-NRS, part 27: `L¹` bounds for the approximation error
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

lemma xconv_integrable {f g : Euc d → ℝ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun x => ∫ y, f y * g (x - y)) :=
  (xconv_int hf hg).integral_prod_left

/-- Translation estimate for `Λ_n`. -/
lemma xΛn_trans :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℝ}, 0 < n → ∀ w : Euc d,
      ∫ x, |xΛn n (x - w) - xΛn n x| ≤ C * (n⁻¹ * ‖w‖) := by
  obtain ⟨C, hC0, hC⟩ := xtrans_le (xΦS d)
  refine ⟨C, hC0, fun {n} hn w => ?_⟩
  have hnorm : ∀ u t : Euc d, ‖xΦS d (u - t) - xΦS d u‖ = |xΦ (u - t) - xΦ u| := by
    intro u t
    rw [xΦS_apply, xΦS_apply, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have e : ∀ x : Euc d, |xΛn n (x - w) - xΛn n x| =
      (n⁻¹) ^ d * |xΦ (n⁻¹ • x - n⁻¹ • w) - xΦ (n⁻¹ • x)| := by
    intro x
    unfold xΛn
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity), smul_sub]
  simp_rw [e]
  rw [integral_const_mul]
  have h := Measure.integral_comp_smul (μ := (volume : Measure (Euc d)))
    (fun u : Euc d => |xΦ (u - n⁻¹ • w) - xΦ u|) n⁻¹
  have hfr : Module.finrank ℝ (Euc d) = d := by simp [Euc]
  rw [hfr, smul_eq_mul, inv_pow, inv_inv, abs_of_pos (by positivity)] at h
  have hb := hC (n⁻¹ • w)
  simp_rw [hnorm] at hb
  have hmin : min 1 ‖n⁻¹ • w‖ ≤ n⁻¹ * ‖w‖ := by
    refine (min_le_right _ _).trans (le_of_eq ?_)
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hn]
  calc (n⁻¹) ^ d * ∫ x : Euc d, |xΦ (n⁻¹ • x - n⁻¹ • w) - xΦ (n⁻¹ • x)|
      = ∫ u : Euc d, |xΦ (u - n⁻¹ • w) - xΦ u| := by
        have h2 : ∫ x : Euc d, |xΦ (n⁻¹ • x - n⁻¹ • w) - xΦ (n⁻¹ • x)| =
            n ^ d * ∫ u : Euc d, |xΦ (u - n⁻¹ • w) - xΦ u| := h
        rw [h2, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hn.ne', one_pow, one_mul]
    _ ≤ C * min 1 ‖n⁻¹ • w‖ := hb
    _ ≤ C * (n⁻¹ * ‖w‖) := mul_le_mul_of_nonneg_left hmin hC0

theorem xe_L1 {a : Euc d → ℝ} {φ : 𝓢(Euc d, ℂ)} (ha : ∀ x, φ x = (a x : ℂ)) :
    ∃ C0 C1 : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧ ∀ n : ℝ, 2 ≤ n →
      Integrable (fun x => a x - xan a n x) ∧ ∫ x, |a x - xan a n x| ≤ C0 ∧
        ((∫ x, a x) = 0 → ∫ x, |a x - xan a n x| ≤ C1 * n⁻¹) := by
  have hare : a = fun x => (φ x).re := by funext x; rw [ha]; simp
  have hac : Continuous a := by rw [hare]; exact Complex.continuous_re.comp φ.continuous
  have hai : Integrable a := by rw [hare]; exact φ.integrable.re
  have haabs : ∀ x, |a x| = ‖φ x‖ := fun x => by rw [ha, Complex.norm_real, Real.norm_eq_abs]
  obtain ⟨M, hM0, hM⟩ := xhbdd φ
  have hMa : ∀ x, |a x| ≤ M := fun x => by rw [haabs]; exact hM x
  obtain ⟨Ca, hCa0, hCa⟩ := xtrans_le φ
  have hCa' : ∀ w : Euc d, ∫ x, |a (x - w) - a x| ≤ Ca * ‖w‖ := by
    intro w
    have h1 := hCa w
    have h2 : ∀ x, ‖φ (x - w) - φ x‖ = |a (x - w) - a x| := by
      intro x; rw [ha, ha, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simp_rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hCa0)
  set m1 : ℝ := ∫ u : Euc d, |xΦ u| * ‖u‖ with hm1
  set A1 : ℝ := ∫ y, |a y| with hA1
  set P1 : ℝ := ∫ z : Euc d, |xΦ z| with hP1
  set A2 : ℝ := ∫ y, |a y| * ‖y‖ with hA2
  have hA1nn : 0 ≤ A1 := integral_nonneg fun _ => abs_nonneg _
  have hP1nn : 0 ≤ P1 := integral_nonneg fun _ => abs_nonneg _
  have hm1nn : 0 ≤ m1 := integral_nonneg fun _ => by positivity
  have hA2nn : 0 ≤ A2 := integral_nonneg fun _ => by positivity
  have haint2 : Integrable (fun y : Euc d => |a y| * ‖y‖) := by
    have h := φ.integrable_pow_mul volume 1
    refine h.congr (Eventually.of_forall fun y => ?_)
    simp only [pow_one, haabs]; ring
  obtain ⟨CΛ, hCΛ0, hCΛ⟩ := xΛn_trans (d := d)
  refine ⟨Ca * (2⁻¹ * m1) + A1 * P1, Ca * m1 + CΛ * A2, by positivity, by positivity, ?_⟩
  intro n hn
  have hn0 : 0 < n := by linarith
  have hΨi := xΨn_integrable (d := d) hn0.ne'
  have hΛi := xΛn_integrable (d := d) hn0.ne'
  obtain ⟨MΨ, hMΨ⟩ := xΨn_bdd (d := d) n
  obtain ⟨MΛ, hMΛ⟩ := xΛn_bdd (d := d) n
  have hΨc := xΨn_continuous (d := d) n
  have hΛc := xΛn_continuous (d := d) n
  -- decomposition
  set Hn : Euc d → ℝ := fun x => (∫ w, a (x - w) * xΨn n w) - (∫ w : Euc d, xΨn n w) * a x with hHn
  set Lon : Euc d → ℝ := fun x => ∫ y, a y * xΛn n (x - y) with hLon
  have hdec : ∀ x, a x - xan a n x = -Hn x + Lon x := by
    intro x
    have i1 : Integrable (fun y => a y * xΨn n (x - y)) :=
      hai.mul_bdd (c := MΨ) (hΨc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
        (Eventually.of_forall fun y => by simpa using hMΨ (x - y))
    have i2 : Integrable (fun y => a y * xΛn n (x - y)) :=
      hai.mul_bdd (c := MΛ) (hΛc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
        (Eventually.of_forall fun y => by simpa using hMΛ (x - y))
    have e1 : xan a n x = (∫ y, a y * xΨn n (x - y)) - ∫ y, a y * xΛn n (x - y) := by
      unfold xan
      rw [← integral_sub i1 i2]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only
      rw [xKr_xσ' hn]; ring
    have e2 : (∫ y, a y * xΨn n (x - y)) = ∫ w, a (x - w) * xΨn n w := by
      have := integral_sub_left_eq_self (μ := (volume : Measure (Euc d)))
        (fun y => a y * xΨn n (x - y)) x
      rw [← this]
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      simp only [sub_sub_cancel]
    rw [e1, e2, hHn, hLon, xΨn_integral hn0]
    simp only
    ring
  have hHi : Integrable Hn := by
    have h1 : Integrable (fun x => ∫ w, xΨn n w * a (x - w)) := xconv_integrable hΨi hai
    have h2 : Integrable (fun x => (∫ w : Euc d, xΨn n w) * a x) := hai.const_mul _
    refine (h1.sub h2).congr (Eventually.of_forall fun x => ?_)
    simp only [hHn, Pi.sub_apply]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    ring
  have hLi : Integrable Lon := xconv_integrable hai hΛi
  have hbd : ∫ x, |a x - xan a n x| ≤ (∫ x, |Hn x|) + ∫ x, |Lon x| := by
    rw [← integral_add hHi.abs hLi.abs]
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
      (hHi.abs.add hLi.abs) (Eventually.of_forall fun x => ?_)
    show |a x - xan a n x| ≤ |Hn x| + |Lon x|
    rw [hdec x]
    calc |-Hn x + Lon x| ≤ |-Hn x| + |Lon x| := abs_add_le _ _
      _ = |Hn x| + |Lon x| := by rw [abs_neg]
  -- the high-frequency part
  have hH : ∫ x, |Hn x| ≤ Ca * (n⁻¹ * m1) := by
    have := xmollify_L1 (f := a) (Θ := xΨn n) hai hac hMa hΨi hΨc (fun w => Ca * ‖w‖) hCa'
      ((xΨn_mul_integrable hn0).const_mul Ca |>.congr (Eventually.of_forall fun w => by simp only; ring))
    refine this.trans (le_of_eq ?_)
    have e : ∀ w : Euc d, |xΨn n w| * (Ca * ‖w‖) = Ca * (|xΨn n w| * ‖w‖) := fun w => by ring
    simp_rw [e]
    rw [integral_const_mul, xΨn_mul_integral hn0]
  -- the low-frequency part
  have hL : ∫ x, |Lon x| ≤ A1 * P1 := by
    have := xL1_conv hai hΛi
    rw [xΛn_integral_abs hn0] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · have hψ : Integrable (fun x => ((φ - xφn φ n hn0) x).re) := (φ - xφn φ n hn0).integrable.re
    refine hψ.congr (Eventually.of_forall fun x => ?_)
    simp only [sub_apply, xφn_real ha n hn0, ha]
    simp
  · refine hbd.trans ?_
    refine add_le_add (hH.trans ?_) hL
    have : n⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hn
    nlinarith [mul_nonneg hCa0 hm1nn]
  · intro hmass
    refine hbd.trans ?_
    have hLz : ∫ x, |Lon x| ≤ CΛ * (n⁻¹ * A2) := by
      have := xmollify_L1 (f := xΛn n) (Θ := a) (M := |n⁻¹ ^ d| * (xΦ_bdd (d := d)).choose)
        hΛi hΛc (fun x => by
          unfold xΛn
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left ((xΦ_bdd (d := d)).choose_spec _) (abs_nonneg _))
        hai hac (fun w => CΛ * (n⁻¹ * ‖w‖)) (fun w => hCΛ hn0 w)
        ((haint2.const_mul (CΛ * n⁻¹)).congr (Eventually.of_forall fun w => by simp only; ring))
      simp only [hmass, zero_mul] at this
      have e0 : ∀ x, (∫ w, xΛn n (x - w) * a w) - 0 = Lon x := by
        intro x
        rw [sub_zero, hLon]
        simp only
        refine integral_congr_ae (Eventually.of_forall fun w => ?_)
        ring
      simp_rw [e0] at this
      refine this.trans (le_of_eq ?_)
      have e : ∀ w : Euc d, |a w| * (CΛ * (n⁻¹ * ‖w‖)) = (CΛ * n⁻¹) * (|a w| * ‖w‖) := fun w => by ring
      simp_rw [e]
      rw [integral_const_mul]; ring
    calc (∫ x, |Hn x|) + ∫ x, |Lon x| ≤ Ca * (n⁻¹ * m1) + CΛ * (n⁻¹ * A2) := add_le_add hH hLz
      _ = (Ca * m1 + CΛ * A2) * n⁻¹ := by ring

end HRS.Commutator.Whole.XNRS
