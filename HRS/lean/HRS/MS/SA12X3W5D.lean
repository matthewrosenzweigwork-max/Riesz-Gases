import HRS.MS.SA12X3W5C

/-!
# S.A.12 C5-T06 (SA12X3), part D: continuity of jets and time derivative of a dilated torus path
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate ContDiff

namespace HRS.PDE.SA12W2

variable {d : ℕ}

open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Construction

theorem sa12x3w_contF_scaled {L t : ℝ} (hL : 0 < L) {w : ℝ → Torus d → ℝ} (hw : sa12w2_JC t w) {n : ℕ}
    (idx : Fin n → Fin d) :
    ContinuousOn (fun p : ℝ × Euc d => partialDeriv idx (fun x => Torus.lift (w p.1) (L⁻¹ • x)) p.2)
      (Icc (0 : ℝ) t ×ˢ univ) := by
  have h := sa12x3w_jc_scale (t := t) (c := L⁻¹) (inv_ne_zero hL.ne') (f := fun τ => Torus.lift (w τ)) hw.1 hw.2 1 n
  have h2 := (continuous_eval_const (fun l : Fin n => EuclideanSpace.single (idx l) (1 : ℝ))).comp_continuousOn h
  refine h2.congr (fun q hq => ?_)
  simp [partialDeriv]

theorem sa12x3w_deriv_scaled {L t : ℝ} (hL : 0 < L) {w W : ℝ → Torus d → ℝ} {Φ : ℝ → Euc d → ℝ}
    (hder : ∀ (j : ℕ) (y : Euc d), ∀ τ ∈ Icc (0 : ℝ) t,
      HasDerivWithinAt (fun σ => iteratedFDeriv ℝ j (Torus.lift (w σ)) y)
        (iteratedFDeriv ℝ j (Torus.lift (W τ)) y) (Icc (0 : ℝ) t) τ)
    (hgen : ∀ τ ∈ Icc (0 : ℝ) t, ∀ x : Euc d, Torus.lift (W τ) (L⁻¹ • x) = Φ τ x)
    {n : ℕ} (idx : Fin n → Fin d) (x : Euc d) (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) t) :
    HasDerivWithinAt (fun τ' => partialDeriv idx (fun y => Torus.lift (w τ') (L⁻¹ • y)) x)
      (partialDeriv idx (Φ τ) x) (Icc (0 : ℝ) t) τ := by
  have hLi : L⁻¹ ≠ 0 := inv_ne_zero hL.ne'
  set v : Fin n → Euc d := fun l => EuclideanSpace.single (idx l) (1 : ℝ) with hv
  set A : ContinuousMultilinearMap ℝ (fun _ : Fin n => Euc d) ℝ →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euc d) ℝ v with hA
  have h1 := A.hasFDerivAt.comp_hasDerivWithinAt τ (hder n (L⁻¹ • x) τ hτ)
  have h2 : HasDerivWithinAt (fun τ' => partialDeriv idx (fun y => Torus.lift (w τ') (L⁻¹ • y)) x)
      (L⁻¹ ^ n * (A (iteratedFDeriv ℝ n (Torus.lift (W τ)) (L⁻¹ • x)))) (Icc (0 : ℝ) t) τ := by
    refine (h1.const_mul (L⁻¹ ^ n)).congr (fun σ _ => ?_) ?_
    · rw [sa12x3w_pd_smul hLi]
      rfl
    · rw [sa12x3w_pd_smul hLi]
      rfl
  refine h2.congr_deriv ?_
  have hfun : Torus.lift (W τ) = fun y => Φ τ (L • y) := by
    funext y
    have := hgen τ hτ (L • y)
    rwa [smul_smul, inv_mul_cancel₀ hL.ne', one_smul] at this
  have hA' : A (iteratedFDeriv ℝ n (Torus.lift (W τ)) (L⁻¹ • x)) = partialDeriv idx (Torus.lift (W τ)) (L⁻¹ • x) := rfl
  rw [hA', hfun, sa12x3w_pd_smul hL.ne', smul_smul, mul_inv_cancel₀ hL.ne', one_smul, ← mul_assoc, ← mul_pow,
    inv_mul_cancel₀ hL.ne', one_pow, one_mul]

end HRS.PDE.SA12W2
