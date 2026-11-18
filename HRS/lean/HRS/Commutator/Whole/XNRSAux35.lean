import HRS.Commutator.Whole.XNRSAux34
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Packet X-NRS, part 35: the mollified field has temperate growth
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

theorem xconv_tg_aux {v : Euc d → ℝ} (hvc : Continuous v) {A B : ℝ} (hB : 0 ≤ B)
    (hv : ∀ x, |v x| ≤ A + B * ‖x‖) :
    ∀ n : ℕ, ∀ {W G : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      (L : ℝ →L[ℝ] W →L[ℝ] G) (g : Euc d → W), ContDiff ℝ ∞ g → HasCompactSupport g →
      ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ n (v ⋆[L] g) x‖ ≤ C * (1 + ‖x‖) := by
  intro n
  induction n with
  | zero =>
    intro W G _ _ _ _ _ _ L g hg hc
    obtain ⟨R, hR⟩ := (hc.isCompact.isBounded).subset_closedBall (0 : Euc d)
    set R' : ℝ := max R 0 with hR'
    have hgc : Continuous g := hg.continuous
    have hgi : Integrable (fun y => ‖g y‖) := (hgc.integrable_of_hasCompactSupport hc).norm
    set G1 : ℝ := ∫ y, ‖g y‖ with hG1
    have hG10 : 0 ≤ G1 := integral_nonneg fun _ => norm_nonneg _
    refine ⟨‖L‖ * G1 * (|A| + B * R' + B), fun x => ?_⟩
    rw [norm_iteratedFDeriv_zero]
    have hA0 := abs_nonneg A
    have hR0 : 0 ≤ R' := le_max_right _ _
    have hpt : ∀ t, ‖L (v t) (g (x - t))‖ ≤ ‖L‖ * (|A| + B * R' + B * ‖x‖) * ‖g (x - t)‖ := by
      intro t
      by_cases hgt : g (x - t) = 0
      · simp [hgt]
      · have hmem : x - t ∈ tsupport g := subset_tsupport _ hgt
        have h1 : ‖x - t‖ ≤ R := by simpa using hR hmem
        have h2 : ‖t‖ ≤ ‖x‖ + R' := by
          have : ‖t‖ ≤ ‖x‖ + ‖x - t‖ := by
            calc ‖t‖ = ‖x - (x - t)‖ := by rw [sub_sub_cancel]
              _ ≤ ‖x‖ + ‖x - t‖ := norm_sub_le _ _
          have := le_max_left R 0
          linarith
        have h3 : |v t| ≤ |A| + B * R' + B * ‖x‖ := by
          calc |v t| ≤ A + B * ‖t‖ := hv t
            _ ≤ |A| + B * (‖x‖ + R') := by
                have := le_abs_self A
                nlinarith [mul_le_mul_of_nonneg_left h2 hB]
            _ = _ := by ring
        calc ‖L (v t) (g (x - t))‖ ≤ ‖L (v t)‖ * ‖g (x - t)‖ := (L (v t)).le_opNorm _
          _ ≤ (‖L‖ * ‖v t‖) * ‖g (x - t)‖ := by
              gcongr; exact L.le_opNorm _
          _ ≤ (‖L‖ * (|A| + B * R' + B * ‖x‖)) * ‖g (x - t)‖ := by
              gcongr; rw [Real.norm_eq_abs]; exact h3
    have hint : Integrable (fun t => ‖L‖ * (|A| + B * R' + B * ‖x‖) * ‖g (x - t)‖) :=
      (hgi.comp_sub_left x).const_mul _
    have := norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
    unfold convolution
    refine this.trans ?_
    rw [integral_const_mul, integral_sub_left_eq_self (μ := (volume : Measure (Euc d))) (fun y => ‖g y‖) x, ← hG1]
    have : ‖L‖ * (|A| + B * R' + B * ‖x‖) * G1 ≤ ‖L‖ * G1 * (|A| + B * R' + B) * (1 + ‖x‖) := by
      have h0 := norm_nonneg L
      have hx := norm_nonneg x
      have : (|A| + B * R' + B * ‖x‖) ≤ (|A| + B * R' + B) * (1 + ‖x‖) := by
        nlinarith [mul_nonneg hB hx, mul_nonneg hA0 hx, mul_nonneg (mul_nonneg hB hR0) hx]
      calc ‖L‖ * (|A| + B * R' + B * ‖x‖) * G1 = ‖L‖ * G1 * (|A| + B * R' + B * ‖x‖) := by ring
        _ ≤ ‖L‖ * G1 * ((|A| + B * R' + B) * (1 + ‖x‖)) :=
            mul_le_mul_of_nonneg_left this (mul_nonneg h0 hG10)
        _ = _ := by ring
    exact this
  | succ n ih =>
    intro W G _ _ _ _ _ _ L g hg hc
    have hf1 : ∀ x, HasFDerivAt (v ⋆[L] g) ((v ⋆[L.precompR (Euc d)] fderiv ℝ g) x) x := fun x =>
      hc.hasFDerivAt_convolution_right L hvc.locallyIntegrable (hg.of_le (by simp)) x
    have hfd : fderiv ℝ (v ⋆[L] g) = v ⋆[L.precompR (Euc d)] fderiv ℝ g :=
      funext fun x => (hf1 x).fderiv
    obtain ⟨C, hC⟩ := ih (L.precompR (Euc d)) (fderiv ℝ g) (hg.fderiv_right (by simp)) (hc.fderiv ℝ)
    refine ⟨C, fun x => ?_⟩
    rw [← norm_iteratedFDeriv_fderiv, hfd]
    exact hC x

open HRS.Commutator.Whole HRS.Commutator.Whole.SAMP1 in
theorem xmol_xtvf {k : Euc d → ℝ} (hk : XMolKer k) (hks : ContDiff ℝ ∞ k) {v : Euc d → Euc d}
    {L : ℝ≥0} (hL : LipschitzWith L v) : XTVF (xmol k v) := by
  intro c
  have hvc : Continuous (fun x => v x c) :=
    (EuclideanSpace.proj c : Euc d →L[ℝ] ℝ).continuous.comp hL.continuous
  have hbd : ∀ x, |v x c| ≤ ‖v 0‖ + (L : ℝ) * ‖x‖ := by
    intro x
    have h1 : |v x c| ≤ ‖v x‖ := by
      have := PiLp.norm_apply_le (v x) c
      simpa [Real.norm_eq_abs] using this
    exact h1.trans (lip_norm_growth hL x)
  have hfun : (fun x => xmol k v x c) = fun x => ((fun t => v t c) ⋆[ContinuousLinearMap.mul ℝ ℝ] k) x := by
    funext x
    rw [xmol_apply_comp v x (xmol_integrable hk hL x) c, convolution_def]
    have := integral_sub_left_eq_self (μ := (volume : Measure (Euc d)))
      (fun y => k y * v (x - y) c) x
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [sub_sub_cancel, ContinuousLinearMap.mul_apply']
    ring
  rw [hfun]
  refine ⟨hk.cpt.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hvc.locallyIntegrable hks, ?_⟩
  intro n
  obtain ⟨C, hC⟩ := xconv_tg_aux hvc (A := ‖v 0‖) (B := (L : ℝ)) L.2 hbd n
    (ContinuousLinearMap.mul ℝ ℝ) k hks hk.cpt
  exact ⟨1, C, fun x => by simpa using hC x⟩

end HRS.Commutator.Whole.XNRS
