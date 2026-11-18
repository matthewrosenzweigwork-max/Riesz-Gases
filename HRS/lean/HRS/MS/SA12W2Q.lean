import HRS.MS.SA12W2P

/-!
# S.A.12 C5 (SA12W2 worker), part Q: `sa12w2_key`, generator conjugacy under dilation (`R26-T5.T05`)
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

theorem sa12w2_matVec_smul_mat (c : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (v : Euc d) :
    Torus.matVec (c • M) v = c • Torus.matVec M v := by
  simp [Torus.matVec]

theorem sa12w2_matVec_smul_vec (c : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (v : Euc d) :
    Torus.matVec M (c • v) = c • Torus.matVec M v := by
  simp [Torus.matVec]

theorem sa12w2_key (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {L T : ℝ} (hL : 0 < L)
    {γ : Euc d → ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {ν : ℝ} {μ : ℝ → Euc d → ℝ} {V : Euc d → ℝ}
    {b : ℝ → Euc d → Euc d} (hP : PerSmooth s T L γ M ν μ V b) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T)
    (D : DynData d) (hDs : D.s = s) (hDM : D.M = (L ^ (-s - 2)) • M) (hDν : D.invβ = ν / L ^ 2)
    (hDV : Torus.lift D.V = fun y => V (L • y) / L ^ 2)
    (u : Torus d → ℝ) (hu : ContDiff ℝ ∞ (Torus.lift u)) (x : Euc d) :
    ν * Laplacian.laplacian (fun x => Torus.lift u (L⁻¹ • x)) x +
        inner ℝ (b τ x) (gradient (fun x => Torus.lift u (L⁻¹ • x)) x) -
        perNonlocal L γ M (μ τ) (fun x => Torus.lift u (L⁻¹ • x)) x =
      backwardGenerator D (sa12w2_dens L (μ τ)) u (Torus.mk (L⁻¹ • x)) := by
  obtain ⟨y', rfl⟩ : ∃ y', x = L • y' := ⟨L⁻¹ • x, by rw [smul_inv_smul₀ hL.ne']⟩
  rw [inv_smul_smul₀ hL.ne']
  have hμs := hP.μ_smooth τ hτ
  have hμp := hP.μ_periodic τ hτ
  have hnl := sa12w2_nonlocal_bridge hd hs0 hsd hL hP.hγ M hμs hμp u hu y'
  have hdr := sa12w2_drift_bridge hd hs0 hsd hL hP.hγ hμs hμp y'
  have hu1 : ContDiff ℝ 1 (Torus.lift u) := hu.of_le (by simp)
  have hgradF : gradient (fun x => Torus.lift u (L⁻¹ • x)) (L • y') = L⁻¹ • gradient (Torus.lift u) y' := by
    rw [sa12w2_grad_dil hu1 (inv_ne_zero hL.ne'), inv_smul_smul₀ hL.ne']
  have hlapF : Laplacian.laplacian (fun x => Torus.lift u (L⁻¹ • x)) (L • y') =
      (L⁻¹) ^ 2 * Laplacian.laplacian (Torus.lift u) y' := by
    rw [sa12w2_lap_dil (inv_ne_zero hL.ne'), inv_smul_smul₀ hL.ne']
  have hgu : Torus.grad u (Torus.mk y') = gradient (Torus.lift u) y' :=
    HRS.KernelD1Aux.lift_grad u y'
  have hgV : Torus.grad D.V (Torus.mk y') = L⁻¹ • gradient V (L • y') := by
    have : Torus.grad D.V (Torus.mk y') = gradient (Torus.lift D.V) y' := HRS.KernelD1Aux.lift_grad D.V y'
    rw [this, hDV, sa12w2_grad_V (hP.V_smooth.of_le (by simp)) hL]
  have hb : b τ (L • y') = L • meanFieldDrift D (sa12w2_dens L (μ τ)) (Torus.mk y') := by
    rw [hP.b_eq τ hτ]
    unfold torusDriftL meanFieldDrift
    rw [hdr, hDM, hDs, hgV, sa12w2_matVec_smul_vec, sa12w2_matVec_smul_mat, smul_sub]
    simp only [smul_smul]
    have e1 : L * L ^ (-s - 2) = L ^ (-s - 1) := by
      rw [show -s - 1 = (-s - 2) + 1 by ring, Real.rpow_add hL, Real.rpow_one]; ring
    rw [e1, mul_inv_cancel₀ hL.ne', one_smul]
  unfold backwardGenerator
  rw [hb, hgradF, hlapF, inner_smul_left, inner_smul_right, hgu, hDν, hDs, sa12w2_lap_lift u y', hDM]
  have h2 : (L ^ 2)⁻¹ = L⁻¹ ^ 2 := by rw [inv_pow]
  have hnl' : perNonlocal L γ M (μ τ) (fun x => Torus.lift u (L⁻¹ • x)) (L • y') =
      ∑ j, (convGradConv (periodicRieszGrad d s) (fun y => sa12w2_dens L (μ τ) y *
        (Torus.matVec ((L ^ (-s - 2)) • M).transpose (Torus.grad u y)) j) (Torus.mk y')) j := hnl
  rw [hnl']
  simp only [conj_trivial, smul_eq_mul]
  rw [← mul_assoc L L⁻¹, mul_inv_cancel₀ hL.ne', one_mul, div_eq_mul_inv, h2]
  ring

end HRS.PDE.SA12W2
