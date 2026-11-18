import HRS.MS.R2S11Aux17
import HRS.MS.WsStatAux12

/-!
# S11.2 (a): derivative bounds for the test functions and window measurability
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2S11

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

/-- Derivatives of order `≤ k` of a `C_b^k` unit-ball function are bounded by `1`. -/
theorem s11_cbUnit_bound {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] {k : ℕ}
    {Φ : B → ℝ} (hΦ : Φ ∈ HRS.CbUnitBall B k) {j : ℕ} (hj : j ≤ k) (x : B) :
    ‖iteratedFDeriv ℝ j Φ x‖ ≤ 1 := by
  obtain ⟨-, hb, hc⟩ := hΦ
  have h1 : ‖iteratedFDeriv ℝ j Φ x‖ ≤ ⨆ z : B, ‖iteratedFDeriv ℝ j Φ z‖ := le_ciSup (hb j hj) x
  have h2 : (⨆ z : B, ‖iteratedFDeriv ℝ j Φ z‖) ≤ HRS.cbNorm k Φ := by
    unfold HRS.cbNorm
    refine Finset.single_le_sum (f := fun j => ⨆ z : B, ‖iteratedFDeriv ℝ j Φ z‖)
      (fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  linarith

/-- `‖D²(D³Φ)(x)‖ = ‖D⁵Φ(x)‖`. -/
theorem s11_norm_iter_iter {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] (Φ : B → ℝ) (x : B) :
    ‖iteratedFDeriv ℝ 2 (iteratedFDeriv ℝ 3 Φ) x‖ = ‖iteratedFDeriv ℝ 5 Φ x‖ := by
  set g := iteratedFDeriv ℝ 3 Φ with hg
  have h1 : ‖iteratedFDeriv ℝ 1 (fderiv ℝ g) x‖ = ‖iteratedFDeriv ℝ (1 + 1) g x‖ :=
    norm_iteratedFDeriv_fderiv
  have h2 : fderiv ℝ g = (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (3 + 1) => B) ℝ) ∘
      iteratedFDeriv ℝ 4 Φ := by
    funext y
    have : iteratedFDeriv ℝ (3 + 1) Φ y = (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (3 + 1) => B) ℝ).symm
        (fderiv ℝ g y) := rfl
    simp only [Function.comp_apply]
    show _ = (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (3 + 1) => B) ℝ) (iteratedFDeriv ℝ (3 + 1) Φ y)
    rw [this, LinearIsometryEquiv.apply_symm_apply]
  have h3 : ‖iteratedFDeriv ℝ 1 (fderiv ℝ g) x‖ = ‖iteratedFDeriv ℝ 1 (iteratedFDeriv ℝ 4 Φ) x‖ := by
    rw [h2]
    exact LinearIsometryEquiv.norm_iteratedFDeriv_comp_left _ _ _ _
  have h4 : ‖iteratedFDeriv ℝ 1 (iteratedFDeriv ℝ 4 Φ) x‖ = ‖iteratedFDeriv ℝ 5 Φ x‖ := by
    rw [norm_iteratedFDeriv_one]
    exact norm_fderiv_iteratedFDeriv
  have h5 : ‖iteratedFDeriv ℝ (1 + 1) g x‖ = ‖iteratedFDeriv ℝ 2 g x‖ := rfl
  rw [← h5, ← h1, h3, h4]

/-- `x ↦ L (D³Φ x)` is `C²` with second derivative bounded by `‖L‖ ‖D⁵Φ‖`. -/
theorem s11_cubic_F {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] {Φ : B → ℝ} (hΦ : ContDiff ℝ 5 Φ)
    (L : (B [×3]→L[ℝ] ℝ) →L[ℝ] ℝ) :
    ContDiff ℝ 2 (fun x => L (iteratedFDeriv ℝ 3 Φ x)) ∧
      ∀ x, ‖iteratedFDeriv ℝ 2 (fun x => L (iteratedFDeriv ℝ 3 Φ x)) x‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ 5 Φ x‖ := by
  have hg : ContDiff ℝ 2 (iteratedFDeriv ℝ 3 Φ) := hΦ.iteratedFDeriv_right (by norm_num)
  refine ⟨L.contDiff.comp hg, fun x => ?_⟩
  have e : iteratedFDeriv ℝ 2 (fun x => L (iteratedFDeriv ℝ 3 Φ x)) x =
      L.compContinuousMultilinearMap (iteratedFDeriv ℝ 2 (iteratedFDeriv ℝ 3 Φ) x) :=
    L.iteratedFDeriv_comp_left hg.contDiffAt (by norm_num)
  rw [e]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (norm_nonneg _)
  exact s11_norm_iter_iter Φ x

end HRS.MS.R2S11
