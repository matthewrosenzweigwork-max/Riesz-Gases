import HRS.Commutator.Whole.INHOMAux26

/-!
# CMX-INHOM auxiliary 27: continuity of `a ↦ 𝒞_{g_{>1}}(v,a)` on `L²`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

theorem inhom_Ccomm_cont (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {v : Euc d → Euc d}
    {L : ℝ≥0} (hL : LipschitzWith L v) {b b' : Euc d → ℝ}
    (hb : AEStronglyMeasurable b volume) (hb' : AEStronglyMeasurable b' volume)
    (hb2 : Integrable (fun x => b x ^ 2) volume) (hb'2 : Integrable (fun x => b' x ^ 2) volume)
    {η : ℝ} (hη : 0 < η) (hδ : ∫ x, (b x - b' x) ^ 2 ≤ η ^ 2) :
    |CcommFun (ghiForce s) v b - CcommFun (ghiForce s) v b'| ≤
      L * (∫ z, inhom_W (d := d) s z) * η * (2 + (∫ x, b x ^ 2) + ∫ x, b' x ^ 2) / 2 := by
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  have hδm : AEStronglyMeasurable (fun x => b x - b' x) volume := hb.sub hb'
  have hδ2 : Integrable (fun x => (b x - b' x) ^ 2) volume := by
    refine ((hb2.const_mul 2).add (hb'2.const_mul 2)).mono' (hδm.pow 2) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (b x + b' x)]
  obtain ⟨hWm, hW, hWn, hWe⟩ := inhom_W_props hd hs0 hsd (d := d)
  have hW1 : 0 ≤ ∫ z, inhom_W (d := d) s z := integral_nonneg hWn
  have hint : ∀ {f g : Euc d → ℝ}, AEStronglyMeasurable f volume → AEStronglyMeasurable g volume →
      Integrable (fun x => f x ^ 2) volume → Integrable (fun x => g x ^ 2) volume →
      Integrable (fun p : Euc d × Euc d => commKer (ghiForce s) v p.1 p.2 * f p.1 * g p.2)
        (volume.prod volume) := fun hf hg hf2 hg2 => (inhom_L2_form hd hs0 hsd hL hf hg hf2 hg2 one_pos).1
  have hrepr : ∀ {f : Euc d → ℝ}, AEStronglyMeasurable f volume → Integrable (fun x => f x ^ 2) volume →
      CcommFun (ghiForce s) v f =
        ∫ p : Euc d × Euc d, commKer (ghiForce s) v p.1 p.2 * f p.1 * f p.2 ∂(volume.prod volume) := by
    intro f hf hf2
    unfold CcommFun
    rw [integral_prod _ (hint hf hf hf2 hf2)]
  have e1 := hint hδm hb hδ2 hb2
  have e2 := hint hb' hδm hb'2 hδ2
  have hdiff : CcommFun (ghiForce s) v b - CcommFun (ghiForce s) v b' =
      (∫ p : Euc d × Euc d, commKer (ghiForce s) v p.1 p.2 * (b p.1 - b' p.1) * b p.2
        ∂(volume.prod volume)) +
      ∫ p : Euc d × Euc d, commKer (ghiForce s) v p.1 p.2 * b' p.1 * (b p.2 - b' p.2)
        ∂(volume.prod volume) := by
    rw [hrepr hb hb2, hrepr hb' hb'2, ← integral_add e1 e2,
      ← integral_sub (hint hb hb hb2 hb2) (hint hb' hb' hb'2 hb'2)]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    ring
  have h1 := (inhom_L2_form hd hs0 hsd hL hδm hb hδ2 hb2 (t := η⁻¹) (inv_pos.2 hη)).2
  have h2 := (inhom_L2_form hd hs0 hsd hL hb' hδm hb'2 hδ2 (t := η) hη).2
  rw [inv_inv] at h1
  rw [hdiff]
  set Dδ := ∫ x, (b x - b' x) ^ 2 with hDδ
  set B2 := ∫ x, b x ^ 2 with hB2
  set B2' := ∫ x, b' x ^ 2 with hB2'
  set W1 := ∫ z, inhom_W (d := d) s z with hW1def
  have hDη : η⁻¹ * Dδ ≤ η := by
    rw [inv_mul_le_iff₀ hη]; nlinarith
  have hDη' : Dδ * η⁻¹ ≤ η := by rw [mul_comm]; exact hDη
  refine (abs_add_le _ _).trans ?_
  have hb1 : (η⁻¹ * Dδ + η * B2) / 2 ≤ (η + η * B2) / 2 := by linarith
  have hb2' : (η * B2' + η⁻¹ * Dδ) / 2 ≤ (η * B2' + η) / 2 := by linarith
  calc _ ≤ L * ((η⁻¹ * Dδ + η * B2) / 2 * W1) + L * ((η * B2' + η⁻¹ * Dδ) / 2 * W1) := add_le_add h1 h2
    _ ≤ L * ((η + η * B2) / 2 * W1) + L * ((η * B2' + η) / 2 * W1) := by gcongr
    _ = _ := by ring

end HRS.Commutator.Whole
