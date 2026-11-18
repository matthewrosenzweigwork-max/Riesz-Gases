import HRS.MS.SA16U3K10g

/-!
# S.A.16 K10, part (h): the two estimates feeding the gradient pair bound (worker SA16U3)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Cutoff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.CZ.Pv HRS.CZ.ElemA HRS.CZ.Hls Phase2SA16

section K10h
variable {d : ℕ}

/-- `ofReal 2` is `2` in `eLpNorm` exponents -/
lemma sa16u3_two : ENNReal.ofReal (2 : ℝ) = 2 := ENNReal.ofReal_ofNat 2

/-- the symmetric part: `|∫ f (T(aW) - a T W)| ≤ C5 ‖a‖_{C_b^1} ‖f‖_2 ‖W‖_2` -/
lemma sa16u3_S_bound (hd : 1 ≤ d) {θ δ : ℝ} (hθ1 : 1 < θ) (hδ : 0 < δ) (i : Fin d) {C5 : ℝ}
    (hC5 : 0 ≤ C5)
    (h5 : ∀ a : Euc d → ℝ, MemCb 1 a → ∀ W : SchwartzMap (Euc d) ℝ,
      eLpNorm (fun x => oddBlend d θ δ 1 i (fun y => a y * W y) x - a x * oddBlend d θ δ 1 i W x)
          (ENNReal.ofReal 2) volume ≤
        ENNReal.ofReal (C5 * cbNorm 1 a) * eLpNorm W (ENNReal.ofReal 2) volume)
    {a : Euc d → ℝ} (ha : MemCb 1 a) (f W : SchwartzMap (Euc d) ℝ) :
    |∫ x, f x * (spliceOdd d θ δ i (fun y => a y * W y) x - a x * spliceOdd d θ δ i W x)| ≤
      sa16u3_N (⇑f) * (C5 * cbNorm 1 a * sa16u3_N (⇑W)) := by
  have hac : Continuous a := ha.1.continuous
  have h := h5 a ha W
  simp only [sa16u3_oddBlend_one, sa16u3_two] at h
  have hWm := sa16u3_memLp_schwartz W
  have hcm : AEStronglyMeasurable (fun x => spliceOdd d θ δ i (fun y => a y * W y) x -
      a x * spliceOdd d θ δ i W x) volume :=
    (sa16u3_T_aesm i (hac.mul W.continuous)).sub
      (hac.aestronglyMeasurable.mul (sa16u3_T_aesm i W.continuous))
  have hfin : ENNReal.ofReal (C5 * cbNorm 1 a) * eLpNorm W 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hWm.eLpNorm_ne_top
  have hcmem : MemLp (fun x => spliceOdd d θ δ i (fun y => a y * W y) x -
      a x * spliceOdd d θ δ i W x) 2 volume :=
    lt_of_le_of_lt h (lt_top_iff_ne_top.2 hfin)
  refine (sa16u3_pair (sa16u3_memLp_schwartz f) hcmem).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (sa16u3_N_nonneg _)
  unfold sa16u3_N
  have h1 := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hC5 (sa16u3_cb_nonneg 1 a))] at h1
  exact h1

/-- the antisymmetric part: `|∫ ∂_v a T(W) Z| ≤ C8 ‖a‖_{C_b^2} (‖Z‖_2 + ‖∇Z‖_2) ‖W‖_2` -/
lemma sa16u3_A_bound (hd : 1 ≤ d) {θ δ : ℝ} (hθ1 : 1 < θ) (hδ : 0 < δ) (i : Fin d) {C8 : ℝ}
    (hC8 : 0 ≤ C8) [Fact (2 ≤ (2 : ℝ))]
    (h8 : ∀ b : Euc d → ℝ, MemCb 1 b → ∀ Z : SchwartzMap (Euc d) ℝ,
      eLpNorm (spliceOdd d θ δ i (fun y => b y * Z y)) (ENNReal.ofReal 2) volume ≤
        ENNReal.ofReal (C8 * cbNorm 1 b) * wNormE 1 2 (⇑Z))
    {a : Euc d → ℝ} (ha : MemCb 2 a) (v : Euc d) (hv : ‖v‖ = 1) (Z W : SchwartzMap (Euc d) ℝ) :
    |∫ x, fderiv ℝ a x v * spliceOdd d θ δ i (⇑W) x * Z x| ≤
      C8 * cbNorm 2 a * (sa16u3_N (⇑Z) + sa16u3_N (fun x => ‖fderiv ℝ Z x‖)) * sa16u3_N (⇑W) := by
  obtain ⟨hb1, hbcb⟩ := sa16u3_cb_partial ha v hv
  set b : Euc d → ℝ := fun x => fderiv ℝ a x v with hb
  have hbc : Continuous b := hb1.1.continuous
  obtain ⟨B1, hB1⟩ := hb1.2 0 (by norm_num)
  have hbb : ∀ x, |b x| ≤ B1 := fun x => by
    have := hB1 ⟨x, rfl⟩
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using this
  have hgb := sa16u3_good_mul hbc hbb (sa16u3_good_schwartz Z)
  have hgW := sa16u3_good_schwartz W
  obtain ⟨hwN1, hwN2⟩ := sa16u3_wN_le Z
  have hsk := sa16u3_skew hd hθ1 hδ i (f := fun y => b y * Z y) (g := ⇑W) hgb.1 hgW.1 hgb.2.1 hgW.2.1
    (Bf := hgb.2.2.choose) (Bg := hgW.2.2.choose) hgb.2.2.choose_spec hgW.2.2.choose_spec
  have e1 : ∫ x, fderiv ℝ a x v * spliceOdd d θ δ i (⇑W) x * Z x =
      ∫ x, (b x * Z x) * spliceOdd d θ δ i (⇑W) x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hb]; ring
  rw [e1, hsk, abs_neg]
  -- the `L^2` bound on `T(bZ)`
  have h := h8 b hb1 Z
  simp only [sa16u3_two] at h
  have hfin : ENNReal.ofReal (C8 * cbNorm 1 b) * wNormE 1 2 (⇑Z) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwN1
  have hmem : MemLp (spliceOdd d θ δ i (fun y => b y * Z y)) 2 volume :=
    lt_of_le_of_lt h (lt_top_iff_ne_top.2 hfin)
  refine (sa16u3_pair hmem (sa16u3_memLp_schwartz W)).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (sa16u3_N_nonneg _)
  unfold sa16u3_N at *
  have h1 := ENNReal.toReal_mono hfin h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hC8 (sa16u3_cb_nonneg 1 b))] at h1
  refine h1.trans ?_
  have hcb : cbNorm 1 b ≤ cbNorm 2 a := hbcb
  have hC : C8 * cbNorm 1 b ≤ C8 * cbNorm 2 a := mul_le_mul_of_nonneg_left hcb hC8
  calc C8 * cbNorm 1 b * (wNormE 1 2 (⇑Z)).toReal
      ≤ C8 * cbNorm 2 a * (wNormE 1 2 (⇑Z)).toReal :=
        mul_le_mul_of_nonneg_right hC ENNReal.toReal_nonneg
    _ ≤ C8 * cbNorm 2 a * ((eLpNorm (⇑Z) 2 volume).toReal +
          (eLpNorm (fun x => ‖fderiv ℝ Z x‖) 2 volume).toReal) :=
        mul_le_mul_of_nonneg_left hwN2 (mul_nonneg hC8 (sa16u3_cb_nonneg 2 a))

end K10h
end HRS.Whole.AppendixA.Phase2SA16Cutoff
