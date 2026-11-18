import HRS.Commutator.Torus.TLOWVAux5

/-!
# T-LOWV, part 6: Lemma 4.1 on the torus, conditional on the unrenormalised commutator estimate (`nrs_T`)
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

lemma tlowv_commKernel_add {F₁ F₂ : Torus d → Euc d} (v : Torus d → Euc d) (x y : Torus d) :
    commKernel (fun z => F₁ z + F₂ z) v x y = commKernel F₁ v x y + commKernel F₂ v x y := by
  unfold commKernel
  split_ifs
  · simp
  · rw [inner_add_right]

/-- Additivity of the commutator form in the force, for odd measurable forces with `L¹` weights. -/
lemma tlowv_CcommFun_add {F₁ F₂ : Torus d → Euc d} (h1m : Measurable F₁) (h1o : ∀ z, F₁ (-z) = -F₁ z)
    (h1W : Integrable (tlowvW F₁)) (h2m : Measurable F₂) (h2o : ∀ z, F₂ (-z) = -F₂ z)
    (h2W : Integrable (tlowvW F₂)) {v : Torus d → Euc d} {L : ℝ} (hL : 0 ≤ L)
    (hv : IsLipschitzVF L v) (hvc : Continuous v) {a : Torus d → ℝ} (hac : Continuous a) :
    CcommFunT (fun z => F₁ z + F₂ z) v a = CcommFunT F₁ v a + CcommFunT F₂ v a := by
  have ha2 : Integrable (fun x => a x ^ 2) :=
    (HRS.PDE.R2Aux.memLp_of_continuous_real hac).integrable_sq
  have hI1 := (tlowv_L2_form h1m h1o h1W hL hv hvc hac.aestronglyMeasurable hac.aestronglyMeasurable
    ha2 ha2 one_pos).1
  have hI2 := (tlowv_L2_form h2m h2o h2W hL hv hvc hac.aestronglyMeasurable hac.aestronglyMeasurable
    ha2 ha2 one_pos).1
  have hsum : Integrable (fun p : Torus d × Torus d =>
      commKernel (fun z => F₁ z + F₂ z) v p.1 p.2 * a p.1 * a p.2) (volume.prod volume) := by
    refine (hI1.add hI2).congr (Eventually.of_forall fun p => ?_)
    show commKernel F₁ v p.1 p.2 * a p.1 * a p.2 + commKernel F₂ v p.1 p.2 * a p.1 * a p.2 =
      commKernel (fun z => F₁ z + F₂ z) v p.1 p.2 * a p.1 * a p.2
    rw [tlowv_commKernel_add]
    ring
  rw [tlowv_CcommFun_eq hsum, tlowv_CcommFun_eq hI1, tlowv_CcommFun_eq hI2, ← integral_add hI1 hI2]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [tlowv_commKernel_add]
  ring

/-- `∇g_≤` has an `L¹` weight (it is bounded). -/
lemma tlowv_glo_W (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {η : ℝ} (hη : 0 < η) :
    Measurable (gloForceT s η : Torus d → Euc d) ∧ Integrable (tlowvW (gloForceT s η : Torus d → Euc d)) := by
  have hc := tsamp_gloForce_continuous hd hs0 hsd hη
  refine ⟨hc.measurable, ?_⟩
  obtain ⟨B, hB⟩ := ten_bound_of_continuous (continuous_norm.comp hc)
  refine ten_integrable_of_bdd (μ := volume) (tlowvW_measurable hc.measurable) (d * B) (fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (tlowvW_nonneg _ _)]
  unfold tlowvW
  have : ‖gloForceT s η z‖ ≤ B := by simpa using hB z
  exact mul_le_mul (KernelGrad.tdist_le_card _) this (norm_nonneg _) (Nat.cast_nonneg d)

/-- The `ghi`-part of the commutator form against a low-frequency density: `L¹` bound for the weight. -/
lemma tlowv_ghi_part (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {CW : ℝ}
    (hCW : ∀ η : ℝ, 0 < η → η ≤ 1 → Integrable (tlowvW (ghiForceT s η : Torus d → Euc d)) ∧
        ∫ z, tlowvW (ghiForceT s η : Torus d → Euc d) z ≤ CW * η ^ ((d : ℝ) - s))
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) {V : Torus d → Euc d} {L : ℝ} (hL : 0 ≤ L)
    (hV : IsLipschitzVF L V) (hVc : Continuous V) {a : Torus d → ℝ} (hac : Continuous a)
    (hc0 : Torus.fcoef a 0 = 0)
    (hsupp : ∀ k : Lattice d, η * Lattice.enorm k ≥ 8 → Torus.fcoef a k = 0) :
    ENNReal.ofReal |CcommFunT (ghiForceT s η) V a| ≤
      ENNReal.ofReal (L * CW * (16 * Real.pi) ^ ((d : ℝ) - s)) *
        homSqT (-Whole.alphaE d s) (fun k => Torus.fcoef a k) := by
  have hd2 : 2 ≤ d := by omega
  have hsd1 : s + 1 < (d : ℝ) := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have he : 0 < (d : ℝ) - s := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨hWi, hWb⟩ := hCW η hη hη1
  have hmem : MemLp a 2 volume := HRS.PDE.R2Aux.memLp_of_continuous_real hac
  have ha2 : Integrable (fun x => a x ^ 2) := hmem.integrable_sq
  have hform := tlowv_L2_form (tkr_ghi_measurable hd2 hs0 hsd1 hη) (tlowv_ghi_odd hd hs0 hsd hη) hWi hL hV
    hVc hac.aestronglyMeasurable hac.aestronglyMeasurable ha2 ha2 one_pos
  rw [← tlowv_CcommFun_eq hform.1] at hform
  have h2 := hform.2
  have hA0 : 0 ≤ ∫ x, a x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hW0 : 0 ≤ ∫ z, tlowvW (ghiForceT s η : Torus d → Euc d) z := integral_nonneg (tlowvW_nonneg _)
  have h3 : |CcommFunT (ghiForceT s η) V a| ≤ L * (∫ z, tlowvW (ghiForceT s η : Torus d → Euc d) z) *
      ∫ x, a x ^ 2 := by
    refine h2.trans (le_of_eq ?_)
    simp only [inv_one, one_mul]
    ring
  have hL2 := tlowv_L2_le_hom hmem hη (by norm_num : (0 : ℝ) < 8) hc0 hsupp he
  have hexp : -(((d : ℝ) - s) / 2) = -Whole.alphaE d s := by unfold Whole.alphaE; ring
  rw [hexp] at hL2
  have hmain : L * (∫ z, tlowvW (ghiForceT s η : Torus d → Euc d) z) * ∫ x, a x ^ 2 ≤
      L * CW * η ^ ((d : ℝ) - s) * ∫ x, a x ^ 2 := by
    have h1 : L * (∫ z, tlowvW (ghiForceT s η : Torus d → Euc d) z) ≤ L * (CW * η ^ ((d : ℝ) - s)) :=
      mul_le_mul_of_nonneg_left hWb hL
    rw [mul_assoc L CW]
    exact mul_le_mul_of_nonneg_right h1 hA0
  calc ENNReal.ofReal |CcommFunT (ghiForceT s η) V a|
      ≤ ENNReal.ofReal (L * CW * η ^ ((d : ℝ) - s) * ∫ x, a x ^ 2) :=
        ENNReal.ofReal_le_ofReal (h3.trans hmain)
    _ = ENNReal.ofReal (L * CW * η ^ ((d : ℝ) - s)) * ENNReal.ofReal (∫ x, a x ^ 2) :=
        ENNReal.ofReal_mul (by
          have : 0 ≤ CW * η ^ ((d : ℝ) - s) := le_trans hW0 hWb
          have hCW0 : 0 ≤ CW := by
            by_contra hneg
            have : CW * η ^ ((d : ℝ) - s) < 0 :=
              mul_neg_of_neg_of_pos (not_le.1 hneg) (Real.rpow_pos_of_pos hη _)
            linarith
          positivity)
    _ ≤ ENNReal.ofReal (L * CW * η ^ ((d : ℝ) - s)) *
          (ENNReal.ofReal ((2 * Real.pi * 8 / η) ^ ((d : ℝ) - s)) *
            homSqT (-Whole.alphaE d s) (fun k => Torus.fcoef a k)) := by
        gcongr
    _ = ENNReal.ofReal (L * CW * (16 * Real.pi) ^ ((d : ℝ) - s)) *
          homSqT (-Whole.alphaE d s) (fun k => Torus.fcoef a k) := by
        have hCW0 : 0 ≤ CW := by
          have h1 : 0 ≤ CW * η ^ ((d : ℝ) - s) := le_trans hW0 hWb
          by_contra hneg
          have : CW * η ^ ((d : ℝ) - s) < 0 :=
            mul_neg_of_neg_of_pos (not_le.1 hneg) (Real.rpow_pos_of_pos hη _)
          linarith
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        have e1 : 2 * Real.pi * 8 / η = (16 * Real.pi) / η := by ring
        rw [e1, Real.div_rpow (by positivity) hη.le]
        have hηe : 0 < η ^ ((d : ℝ) - s) := Real.rpow_pos_of_pos hη _
        field_simp

end HRS.Commutator.TorusNote
