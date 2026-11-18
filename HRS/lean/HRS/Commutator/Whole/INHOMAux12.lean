import HRS.Commutator.Whole.INHOMAux11

/-!
# CMX-INHOM auxiliary 12: `Ccomm` against a Schwartz density, and the decomposition of `𝒞_{g_{>1}}`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

theorem inhom_Ccomm_ofDensity {F V : Euc d → Euc d} {Lv B : ℝ} (hFc : Continuous F)
    (hB : ∀ x, ‖F x‖ ≤ B) (hVc : Continuous V) (hV : ∀ x y, ‖V x - V y‖ ≤ Lv * ‖x - y‖)
    (hLv : 0 ≤ Lv) {a : Euc d → ℝ} (hac : Continuous a)
    (hai : Integrable (fun y : Euc d => (1 + ‖y‖) * |a y|) volume) :
    Ccomm F V (SMeas.ofDensity a) = CcommFun F V a := by
  have hglo := lowv_glo_piece hFc hB hVc hV hLv hac hai
  obtain ⟨ha1, hax⟩ := lowv_a_int_aux hac hai
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hKc : ∀ x : Euc d, Continuous fun y => commKer F V x y := by
    intro x
    have : (fun y => commKer F V x y) = fun y => lowv_K F V x y := funext fun y => lowv_commKer_eq F V x y
    rw [this]
    exact (lowv_K_continuous hFc hVc).comp (continuous_const.prodMk continuous_id)
  have hinner : ∀ x : Euc d, Integrable (fun y => a y * commKer F V x y) volume := by
    intro x
    have hb : ∀ y : Euc d, ‖a y * commKer F V x y‖ ≤
        (Lv * B * (1 + ‖x‖)) * ((1 + ‖y‖) * |a y|) := by
      intro y
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, lowv_commKer_eq]
      have h1 := lowv_K_bound hB hV hLv x y
      have h2 : ‖x‖ + ‖y‖ ≤ (1 + ‖x‖) * (1 + ‖y‖) := by
        nlinarith [norm_nonneg x, norm_nonneg y]
      calc |a y| * |lowv_K F V x y| ≤ |a y| * (Lv * B * ((1 + ‖x‖) * (1 + ‖y‖))) := by
            gcongr
            exact h1.trans (by gcongr)
        _ = _ := by ring
    exact (hai.const_mul _).mono' (hac.aestronglyMeasurable.mul (hKc x).aestronglyMeasurable)
      (Eventually.of_forall hb)
  have hint2 : Integrable (fun x : Euc d => ∫ y, commKer F V x y * a x * a y) volume :=
    hglo.integral_prod_left
  have hrew : ∀ x : Euc d, ∫ y, commKer F V x y * a x * a y = a x * ∫ y, a y * commKer F V x y := by
    intro x
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    ring
  unfold Ccomm SMeas.pair2 CcommFun
  have hin : ∀ x : Euc d, (SMeas.ofDensity a).int (fun y => commKer F V x y) =
      ∫ y, a y * commKer F V x y := fun x =>
    energyAux_int_ofDensity a _ hac.measurable (hinner x)
  simp_rw [hin]
  rw [energyAux_int_ofDensity a _ hac.measurable ?_]
  · simp_rw [hrew]
  · simpa [hrew] using hint2

lemma inhom_commKer_addV (F V₁ V₂ : Euc d → Euc d) (x y : Euc d) :
    commKer F (fun z => V₁ z + V₂ z) x y = commKer F V₁ x y + commKer F V₂ x y := by
  unfold commKer
  split_ifs with h
  · simp
  · rw [← inner_add_left, add_sub_add_comm]

theorem inhom_Ccomm_splitV {F V₁ V₂ : Euc d → Euc d} {a : Euc d → ℝ}
    (h1 : Integrable (fun p : Euc d × Euc d => commKer F V₁ p.1 p.2 * a p.1 * a p.2)
      (volume.prod volume))
    (h2 : Integrable (fun p : Euc d × Euc d => commKer F V₂ p.1 p.2 * a p.1 * a p.2)
      (volume.prod volume)) :
    CcommFun F (fun z => V₁ z + V₂ z) a = CcommFun F V₁ a + CcommFun F V₂ a := by
  have e : ∀ p : Euc d × Euc d, commKer F (fun z => V₁ z + V₂ z) p.1 p.2 * a p.1 * a p.2 =
      commKer F V₁ p.1 p.2 * a p.1 * a p.2 + commKer F V₂ p.1 p.2 * a p.1 * a p.2 := fun p => by
    rw [inhom_commKer_addV]; ring
  have hG : Integrable (fun p : Euc d × Euc d =>
      commKer F (fun z => V₁ z + V₂ z) p.1 p.2 * a p.1 * a p.2) (volume.prod volume) :=
    (h1.add h2).congr (Eventually.of_forall fun p => (e p).symm)
  unfold CcommFun
  rw [← integral_prod _ hG, ← integral_prod _ h1, ← integral_prod _ h2]
  simp_rw [e]
  exact integral_add h1 h2

lemma inhom_Pleq_lipschitz : ∃ M : ℝ, 0 ≤ M ∧ ∀ (v : Euc d → Euc d) (L : ℝ≥0), LipschitzWith L v →
    ∀ x x' : Euc d, ‖Pleq 1 v x - Pleq 1 v x'‖ ≤ M * L * ‖x - x'‖ :=
  ⟨∫ y : Euc d, |psiL 1 y|, integral_nonneg fun y => abs_nonneg _,
    fun v L hL x x' => SAMP1.Pleq_lip hL x x'⟩

/-- The decomposition `𝒞_{g_{>1}}(v,a) = 𝒞_g(v,a) - 𝒞_{g_{≤1}}(v_{≤1},a) - 𝒞_{g_{≤1}}(v_{>1},a)`. -/
theorem inhom_a1_split (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {v : Euc d → Euc d}
    {L : ℝ≥0} (hL : LipschitzWith L v) {a : Euc d → ℝ} (hac : Continuous a)
    (hai : Integrable (fun y : Euc d => (1 + ‖y‖) * |a y|) volume) {M : ℝ} (hM : ∀ x, |a x| ≤ M)
    (ha1 : Integrable (fun y => |a y|) volume) (ha2 : Integrable (fun x : Euc d => a x ^ 2) volume) :
    CcommFun (ghiForce s) v a = CcommFun (kernGrad s) v a - CcommFun (gloForce s) (Pleq 1 v) a -
      CcommFun (gloForce s) (Pgt 1 v) a := by
  obtain ⟨hFcd, hF0, hFodd, hFder⟩ := gloForce_props hd hs0 hsd
  obtain ⟨B, hBd⟩ := hFder 0
  have hB : ∀ x, ‖gloForce s x‖ ≤ B := fun x => by simpa using hBd x
  have hFc : Continuous (gloForce s : Euc d → Euc d) := hFcd.continuous
  have hk1 : Integrable (fun x : Euc d => ‖x‖ * ‖ghiForce s x‖) :=
    memLp_one_iff_integrable.1 (kernel_remainder_Lp hd hs0 hsd).1
  have hghim := inhom_ghi_measurable hd hs0 hsd (d := d)
  obtain ⟨Mq, hMq0, hMq⟩ := inhom_Pleq_lipschitz (d := d)
  have hvc : Continuous v := hL.continuous
  have hV : ∀ x y, ‖v x - v y‖ ≤ L * ‖x - y‖ := fun x y => by
    simpa [dist_eq_norm] using hL.dist_le_mul x y
  have hV1c : Continuous (Pleq 1 v) := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    refine Metric.continuousAt_iff.2 fun ε hε => ?_
    have hc : 0 < Mq * L + 1 := by positivity
    refine ⟨ε / (Mq * L + 1), by positivity, fun y hy => ?_⟩
    rw [dist_eq_norm] at hy ⊢
    calc ‖Pleq 1 v y - Pleq 1 v x‖ ≤ Mq * L * ‖y - x‖ := hMq v L hL y x
      _ ≤ (Mq * L + 1) * ‖y - x‖ := by gcongr; linarith
      _ < (Mq * L + 1) * (ε / (Mq * L + 1)) := by gcongr
      _ = ε := by field_simp
  have hV1 : ∀ x y, ‖Pleq 1 v x - Pleq 1 v y‖ ≤ (Mq * L) * ‖x - y‖ := fun x y => hMq v L hL x y
  have hV2c : Continuous (Pgt 1 v) := by
    have : (Pgt 1 v : Euc d → Euc d) = fun x => v x - Pleq 1 v x := rfl
    rw [this]; exact hvc.sub hV1c
  have hV2 : ∀ x y, ‖Pgt 1 v x - Pgt 1 v y‖ ≤ (L + Mq * L) * ‖x - y‖ := by
    intro x y
    have : Pgt 1 v x - Pgt 1 v y = (v x - v y) - (Pleq 1 v x - Pleq 1 v y) := by
      simp only [Pgt]; abel
    rw [this]
    calc ‖(v x - v y) - (Pleq 1 v x - Pleq 1 v y)‖ ≤ ‖v x - v y‖ + ‖Pleq 1 v x - Pleq 1 v y‖ :=
          norm_sub_le _ _
      _ ≤ L * ‖x - y‖ + (Mq * L) * ‖x - y‖ := add_le_add (hV x y) (hV1 x y)
      _ = _ := by ring
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  have hglo := lowv_glo_piece hFc hB hvc hV hL0 hac hai
  have hglo1 := lowv_glo_piece hFc hB hV1c hV1 (by positivity) hac hai
  have hglo2 := lowv_glo_piece hFc hB hV2c hV2 (by positivity) hac hai
  obtain ⟨hghi, -⟩ := lowv_ghi_piece hghim hvc hV hL0 hk1 hac hM ha1 ha2
  have hsplit := lowv_Ccomm_split hglo hghi
  have hG : (fun z : Euc d => gloForce s z + ghiForce s z) = kernGrad s := by
    funext z; simp [ghiForce]
  rw [hG] at hsplit
  have hv : (fun z => Pleq 1 v z + Pgt 1 v z) = v := by
    funext z; simp [Pgt]
  have hsplit2 := inhom_Ccomm_splitV (a := a) hglo1 hglo2
  rw [hv] at hsplit2
  linarith

end HRS.Commutator.Whole
