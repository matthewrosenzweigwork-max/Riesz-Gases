import HRS.MS.SA12W2T

/-!
# S.A.12 C5 (SA12W2 worker), part U: elementary facts for the rescaled torus solution (`R26-T5.T06`, first half)

For a torus function `u` the physical function `x ↦ lift u (L⁻¹ • x)` is smooth and `L`-periodic, has bounded jets
(`BddJets`), and equals the datum `φ` when `lift u = φ(L·)`.  These are the periodicity, bounded-jet and initial-value
fields of `IsPerSol` for `F τ = lift (toFun (P τ)) (L⁻¹ ·)` in `R26-T5.T06` (`sa12w2_C5`, not yet proved).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate ContDiff

namespace HRS.PDE.SA12W2

variable {d : ℕ}

open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Construction

theorem sa12w2_scaled_per {L : ℝ} (hL : 0 < L) (u : Torus d → ℝ) (x : Euc d) (z : Fin d → ℤ) :
    Torus.lift u (L⁻¹ • (x + L • latticePt z)) = Torus.lift u (L⁻¹ • x) := by
  rw [smul_add, smul_smul, inv_mul_cancel₀ hL.ne', one_smul]
  exact Torus.lift_periodic u _ z

theorem sa12w2_scaled_contDiff {L : ℝ} (hL : 0 < L) {u : Torus d → ℝ} (hu : ContDiff ℝ ∞ (Torus.lift u)) :
    ContDiff ℝ ∞ (fun x : Euc d => Torus.lift u (L⁻¹ • x)) :=
  hu.comp (contDiff_const_smul L⁻¹)

theorem sa12w2_scaled_bddJets {L : ℝ} (hL : 0 < L) {u : Torus d → ℝ} (hu : ContDiff ℝ ∞ (Torus.lift u)) (m : ℕ) :
    BddJets m (fun x : Euc d => Torus.lift u (L⁻¹ • x)) := by
  have hF := sa12w2_scaled_contDiff hL hu
  obtain ⟨Bd, hBd⟩ := sa12v_smooth_bdd L hL hF (fun x z => sa12w2_scaled_per hL u x z) m
  refine ⟨hF, fun j hj idx => ⟨Bd, fun x => ?_⟩⟩
  unfold partialDeriv
  have h1 := ContinuousMultilinearMap.le_opNorm (iteratedFDeriv ℝ j (fun x : Euc d => Torus.lift u (L⁻¹ • x)) x)
    (fun l => EuclideanSpace.single (idx l) (1 : ℝ))
  have h2 : ∀ l, ‖(EuclideanSpace.single (idx l) (1 : ℝ) : Euc d)‖ = 1 := fun l => by simp
  simp only [h2, Finset.prod_const_one, mul_one] at h1
  calc |iteratedFDeriv ℝ j (fun x : Euc d => Torus.lift u (L⁻¹ • x)) x (fun l => EuclideanSpace.single (idx l) 1)|
      = ‖iteratedFDeriv ℝ j (fun x : Euc d => Torus.lift u (L⁻¹ • x)) x (fun l => EuclideanSpace.single (idx l) 1)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ‖iteratedFDeriv ℝ j (fun x : Euc d => Torus.lift u (L⁻¹ • x)) x‖ := h1
    _ ≤ Bd := hBd j hj x

theorem sa12w2_scaled_init {L : ℝ} (hL : 0 < L) {u : Torus d → ℝ} {φ : Euc d → ℝ}
    (hu : Torus.lift u = fun y => φ (L • y)) :
    (fun x : Euc d => Torus.lift u (L⁻¹ • x)) = φ := by
  funext x
  rw [hu]
  show φ (L • L⁻¹ • x) = φ x
  rw [smul_smul, mul_inv_cancel₀ hL.ne', one_smul]

end HRS.PDE.SA12W2
