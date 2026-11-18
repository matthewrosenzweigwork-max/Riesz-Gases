import HRS.Commutator.Whole.LOWVAux7

/-!
# CMX-LOWV auxiliary 8: splitting, `L²` versus `Ḣ^{-α}`, components of `P_{≤1} v`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole HRS.Commutator.Whole.SAMP2

variable {d : ℕ}

theorem lowv_commKer_add (F H V : Euc d → Euc d) (x y : Euc d) :
    commKer (fun z => F z + H z) V x y = commKer F V x y + commKer H V x y := by
  unfold commKer
  split_ifs with h
  · simp
  · rw [inner_add_right]

theorem lowv_Ccomm_split {F H V : Euc d → Euc d} {a : Euc d → ℝ}
    (hF : Integrable (fun p : Euc d × Euc d => commKer F V p.1 p.2 * a p.1 * a p.2)
      (volume.prod volume))
    (hH : Integrable (fun p : Euc d × Euc d => commKer H V p.1 p.2 * a p.1 * a p.2)
      (volume.prod volume)) :
    CcommFun (fun z => F z + H z) V a = CcommFun F V a + CcommFun H V a := by
  have e : ∀ p : Euc d × Euc d, commKer (fun z => F z + H z) V p.1 p.2 * a p.1 * a p.2 =
      commKer F V p.1 p.2 * a p.1 * a p.2 + commKer H V p.1 p.2 * a p.1 * a p.2 := fun p => by
    rw [lowv_commKer_add]; ring
  have hG : Integrable (fun p : Euc d × Euc d =>
      commKer (fun z => F z + H z) V p.1 p.2 * a p.1 * a p.2) (volume.prod volume) :=
    (hF.add hH).congr (Eventually.of_forall fun p => (e p).symm)
  unfold CcommFun
  rw [← integral_prod _ hG, ← integral_prod _ hF, ← integral_prod _ hH]
  simp_rw [e]
  exact integral_add hF hH

/-- `L²` norm of a band-limited Schwartz function against the `Ḣ^{-β}` weight. -/
theorem lowv_L2_le (hd : 1 ≤ d) {Λ β : ℝ} (hΛ : 0 < Λ) (hβ : 0 ≤ β)
    (φ : SchwartzMap (Euc d) ℂ) (hφ : ∀ ξ : Euc d, 2 * Λ ≤ ‖ξ‖ → 𝓕 (⇑φ) ξ = 0) :
    ENNReal.ofReal (∫ x, ‖φ x‖ ^ 2) ≤ ENNReal.ofReal ((4 * Real.pi * Λ) ^ (2 * β)) *
      ∫⁻ ξ, ENNReal.ofReal ((2 * Real.pi * ‖ξ‖) ^ (2 * (-β))) * ‖𝓕 (⇑φ) ξ‖ₑ ^ 2 := by
  have hi : Integrable (fun x => ‖φ x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm φ.continuous.aestronglyMeasurable).1 (φ.memLp 2)
  have h1 : ENNReal.ofReal (∫ x, ‖φ x‖ ^ 2) = ∫⁻ x, ‖φ x‖ₑ ^ (2 : ℝ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => by positivity)]
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
    norm_num
  rw [h1, ← lintegral_sq_fourier φ]
  have hpos : 0 < 4 * Real.pi * Λ := by positivity
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_ne_zero_euc (d := d) hd] with ξ hξ
  rw [show (‖𝓕 (⇑φ) ξ‖ₑ ^ (2 : ℝ)) = ‖𝓕 (⇑φ) ξ‖ₑ ^ 2 by
    rw [ENNReal.rpow_two]]
  by_cases h : 2 * Λ ≤ ‖ξ‖
  · rw [hφ ξ h]; simp
  · push Not at h
    have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    have hx : 0 < 2 * Real.pi * ‖ξ‖ := by positivity
    have hxy : 2 * Real.pi * ‖ξ‖ ≤ 4 * Real.pi * Λ := by nlinarith [Real.pi_pos]
    have h2 : (4 * Real.pi * Λ) ^ (-(2 * β)) ≤ (2 * Real.pi * ‖ξ‖) ^ (-(2 * β)) :=
      Real.rpow_le_rpow_of_nonpos hx hxy (by linarith)
    have h3 : 1 ≤ (4 * Real.pi * Λ) ^ (2 * β) * (2 * Real.pi * ‖ξ‖) ^ (2 * (-β)) := by
      have : (4 * Real.pi * Λ) ^ (2 * β) * (4 * Real.pi * Λ) ^ (-(2 * β)) = 1 := by
        rw [← Real.rpow_add hpos]; simp
      rw [show 2 * (-β) = -(2 * β) by ring]
      calc (1 : ℝ) = (4 * Real.pi * Λ) ^ (2 * β) * (4 * Real.pi * Λ) ^ (-(2 * β)) := this.symm
        _ ≤ _ := by gcongr
    calc ‖𝓕 (⇑φ) ξ‖ₑ ^ 2 = 1 * ‖𝓕 (⇑φ) ξ‖ₑ ^ 2 := (one_mul _).symm
      _ ≤ ENNReal.ofReal ((4 * Real.pi * Λ) ^ (2 * β) * (2 * Real.pi * ‖ξ‖) ^ (2 * (-β))) *
            ‖𝓕 (⇑φ) ξ‖ₑ ^ 2 := by
          gcongr
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal h3
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity), mul_assoc]

/-- Components of `P_{≤L} v`. -/
theorem lowv_Pleq_comp {L : ℝ} (hL : 0 < L) {v : Euc d → Euc d} {C0 : ℝ}
    (hv : Continuous v) (hvg : ∀ x, ‖v x‖ ≤ C0 * (1 + ‖x‖)) (x : Euc d) (i : Fin d) :
    Pleq L v x i = Pleq L (fun z => v z i) x := by
  unfold Pleq
  have hint : Integrable (fun y => psiL L y • v (x - y)) := by
    have hG := lowv_psiL_integrable_mul (d := d) hL 1
    refine ((hG.const_mul (C0 * (1 + ‖x‖))).mono' ?_ (Eventually.of_forall fun y => ?_))
    · exact ((lowv_psiL_continuous hL).smul (hv.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
    · rw [norm_smul, Real.norm_eq_abs]
      have h1 : 1 + ‖x - y‖ ≤ (1 + ‖x‖) * (1 + ‖y‖) := by
        have : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
        nlinarith [norm_nonneg x, norm_nonneg y]
      have hC0 : 0 ≤ C0 := by
        have := hvg 0
        simp at this
        exact (norm_nonneg _).trans this
      calc |psiL L y| * ‖v (x - y)‖ ≤ |psiL L y| * (C0 * (1 + ‖x - y‖)) := by
            gcongr; exact hvg _
        _ ≤ |psiL L y| * (C0 * ((1 + ‖x‖) * (1 + ‖y‖))) := by gcongr
        _ = C0 * (1 + ‖x‖) * ((1 + ‖y‖) ^ 1 * |psiL L y|) := by ring
  have := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).integral_comp_comm hint
  simpa using this.symm

end HRS.Commutator.Whole
