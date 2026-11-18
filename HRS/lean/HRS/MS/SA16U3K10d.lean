import HRS.MS.SA16U3K10c

/-!
# S.A.16 K10, part (d): the antisymmetric identity (worker SA16U3)

Integrating by parts in the displayed derivative and using `T ∂ = ∂ T` (`sa16u3_T_fderiv_apply`), the mixed
second derivative terms of `∫ ∂_l Z a T ∂_j Z` and `∫ ∂_j Z a T ∂_l Z` coincide, leaving
`-∫ ∂_l a T(∂_j Z) Z + ∫ ∂_j a T(∂_l Z) Z`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Cutoff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.CZ.Pv HRS.CZ.ElemA Phase2SA16

section K10d
variable {d : ℕ}

open LineDeriv in
lemma sa16u3_mixed_symm (Z : SchwartzMap (Euc d) ℝ) (v w : Euc d) :
    ∂_{v} (∂_{w} Z) = ∂_{w} (∂_{v} Z) := by
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hZ : ContDiff ℝ 2 (⇑Z) := Z.smooth 2
  have hs : IsSymmSndFDerivAt ℝ (⇑Z) x := hZ.contDiffAt.isSymmSndFDerivAt (by simp)
  have e1 : ∀ u t : Euc d, fderiv ℝ (fun y => fderiv ℝ (⇑Z) y u) x t =
      fderiv ℝ (fderiv ℝ (⇑Z)) x t u := by
    intro u t
    have hd1 : DifferentiableAt ℝ (fderiv ℝ (⇑Z)) x :=
      ((hZ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
    have := fderiv_clm_apply (c := fderiv ℝ (⇑Z)) (u := fun _ => u) (x := x) hd1
      (differentiableAt_const _)
    simp [this]
  show fderiv ℝ (fun y => fderiv ℝ (⇑Z) y w) x v = fderiv ℝ (fun y => fderiv ℝ (⇑Z) y v) x w
  rw [e1, e1]
  exact hs v w

/-- integration by parts in the displayed derivative -/
lemma sa16u3_ibp (hd : 1 ≤ d) {θ δ : ℝ} (hθ1 : 1 < θ) (hδ : 0 < δ) (i : Fin d)
    {a : Euc d → ℝ} (ha : ContDiff ℝ 2 a) {Ba Bda : ℝ} (hBa : ∀ x, |a x| ≤ Ba)
    (hBda : ∀ x, ‖fderiv ℝ a x‖ ≤ Bda) (Z Zw : SchwartzMap (Euc d) ℝ) (v : Euc d) :
    ∫ x, fderiv ℝ Z x v * a x * spliceOdd d θ δ i Zw x =
      -(∫ x, fderiv ℝ a x v * spliceOdd d θ δ i Zw x * Z x) -
        ∫ x, a x * spliceOdd d θ δ i (fun y => fderiv ℝ Zw y v) x * Z x := by
  set T : (Euc d → ℝ) → Euc d → ℝ := fun u => spliceOdd d θ δ i u with hT
  have hha : Differentiable ℝ a := ha.differentiable (by norm_num)
  have hTW : Differentiable ℝ (fun y => spliceOdd d θ δ i Zw y) :=
    sa16u3_T_differentiable hd hθ1 hδ i Zw
  have hgZw := sa16u3_good_schwartz Zw
  obtain ⟨BT, hBT⟩ := sa16u3_T_bdd hd hθ1 hδ i hgZw
  -- the second-level derivative is a Schwartz function
  set Zwv : SchwartzMap (Euc d) ℝ := SchwartzMap.evalCLM ℝ (Euc d) ℝ v (SchwartzMap.fderivCLM ℝ (Euc d) ℝ Zw)
    with hZwv
  have hZwv_apply : ∀ y, Zwv y = fderiv ℝ Zw y v := fun y => rfl
  have hgZwv := sa16u3_good_schwartz Zwv
  obtain ⟨BT2, hBT2⟩ := sa16u3_T_bdd hd hθ1 hδ i hgZwv
  have hTcont : Continuous (fun y => spliceOdd d θ δ i Zw y) := hTW.continuous
  have hTcont2 : Continuous (fun y => spliceOdd d θ δ i (fun y => fderiv ℝ Zw y v) y) :=
    (sa16u3_T_differentiable hd hθ1 hδ i Zwv).continuous
  have hda : Continuous (fun y => fderiv ℝ a y v) :=
    ((ha.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  -- G and its derivative
  set G : Euc d → ℝ := fun x => a x * spliceOdd d θ δ i Zw x with hG
  have hGd : Differentiable ℝ G := hha.mul hTW
  have hGder : ∀ x, fderiv ℝ G x v = fderiv ℝ a x v * spliceOdd d θ δ i Zw x +
      a x * spliceOdd d θ δ i (fun y => fderiv ℝ Zw y v) x := by
    intro x
    have h1 := fderiv_mul (hha x) (hTW x)
    have h2 : fderiv ℝ G x = a x • fderiv ℝ (fun y => spliceOdd d θ δ i Zw y) x +
        (spliceOdd d θ δ i Zw x) • fderiv ℝ a x := h1
    rw [h2]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [sa16u3_T_fderiv_apply hd hθ1 hδ i Zw x v]
    ring
  -- integrability
  have hZi : Integrable (⇑Z) volume := Z.integrable
  have b1 : ∃ B, ∀ x, |fderiv ℝ a x v * spliceOdd d θ δ i Zw x| ≤ B := by
    refine ⟨(Bda * ‖v‖) * BT, fun x => ?_⟩
    rw [abs_mul]
    refine mul_le_mul ?_ (hBT x) (abs_nonneg _) (by
      have := hBda 0
      exact mul_nonneg ((norm_nonneg _).trans this) (norm_nonneg _))
    calc |fderiv ℝ a x v| = ‖fderiv ℝ a x v‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ a x‖ * ‖v‖ := (fderiv ℝ a x).le_opNorm v
      _ ≤ Bda * ‖v‖ := mul_le_mul_of_nonneg_right (hBda x) (norm_nonneg _)
  have b2 : ∃ B, ∀ x, |a x * spliceOdd d θ δ i (fun y => fderiv ℝ Zw y v) x| ≤ B := by
    refine ⟨Ba * BT2, fun x => ?_⟩
    rw [abs_mul]
    exact mul_le_mul (hBa x) (hBT2 x) (abs_nonneg _) ((abs_nonneg _).trans (hBa x))
  have iH1 : Integrable (fun x => fderiv ℝ a x v * spliceOdd d θ δ i Zw x * Z x) :=
    hZi.bdd_mul (hda.mul hTcont).aestronglyMeasurable (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using b1.choose_spec x)
  have iH2 : Integrable (fun x => a x * spliceOdd d θ δ i (fun y => fderiv ℝ Zw y v) x * Z x) :=
    hZi.bdd_mul (ha.continuous.mul hTcont2).aestronglyMeasurable (Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using b2.choose_spec x)
  have iGZ : Integrable (fun x => G x * Z x) := by
    refine hZi.bdd_mul (ha.continuous.mul hTcont).aestronglyMeasurable
      (c := Ba * BT) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hBa x) (hBT x) (abs_nonneg _) ((abs_nonneg _).trans (hBa x))
  have iGZ' : Integrable (fun x => G x * fderiv ℝ Z x v) := by
    have hZv := sa16u3_good_schwartz (SchwartzMap.evalCLM ℝ (Euc d) ℝ v (SchwartzMap.fderivCLM ℝ (Euc d) ℝ Z))
    refine hZv.2.1.bdd_mul (ha.continuous.mul hTcont).aestronglyMeasurable
      (c := Ba * BT) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hBa x) (hBT x) (abs_nonneg _) ((abs_nonneg _).trans (hBa x))
  have iDG : Integrable (fun x => fderiv ℝ G x v * Z x) := by
    refine (iH1.add iH2).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    rw [hGder x]; ring
  have ibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := G) (g := ⇑Z) (v := v)
    iDG iGZ' iGZ (fun x _ => hGd x) (fun x _ => Z.differentiableAt)
  have e1 : ∫ x, fderiv ℝ Z x v * a x * spliceOdd d θ δ i Zw x = ∫ x, G x * fderiv ℝ Z x v := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hG]; ring
  rw [e1, ibp]
  have e2 : ∫ x, fderiv ℝ G x v * Z x =
      (∫ x, fderiv ℝ a x v * spliceOdd d θ δ i Zw x * Z x) +
        ∫ x, a x * spliceOdd d θ δ i (fun y => fderiv ℝ Zw y v) x * Z x := by
    rw [← integral_add iH1 iH2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [hGder x]; ring
  rw [e2]; ring

end K10d
end HRS.Whole.AppendixA.Phase2SA16Cutoff
