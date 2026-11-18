import HRS.MH.EdgeSharpDa
import HRS.PDE.MeanFieldOneLe
import HRS.PDE.WellPosed
import HRS.PDE.MeanFieldSemigroup
import HRS.MD.EQGaussLyapDet
import HRS.MD.EQEvoUnif

/-!
# EdgeSharp Group D (packets D4, D5)

Statements copied verbatim from `HRS/MH/EdgeSharpSpec.lean`.  Routes: see the packet docstrings there.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.EdgeSharp

open HRS

variable {d : ℕ}

/-- A forward solution at constant density `1` has diagonal Fourier coefficients. -/
private theorem forward_const_coeff (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {r : ℝ} (hr : 0 ≤ r) {c : PDE.Coeff d} {F : ℝ → PDE.Coeff d}
    (hF : PDE.IsForwardSolution (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) (fun _ => 1) r c F)
    (k : Lattice d) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 r) :
    F τ k = ((Real.exp (PDE.modelEigenvalue d s β⁻¹ (-1) k * τ) : ℝ) : ℂ) * c k := by
  set lam : ℝ := PDE.modelEigenvalue d s β⁻¹ (-1) k with hlam
  have hgen : ∀ σ, PDE.forwardGen (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) (fun _ => 1) (F σ) k =
      (lam : ℂ) * F σ k := fun σ =>
    forwardGen_const_density_all hd s hs0 hsd (-1) β⁻¹ (inv_nonneg.mpr hβ.le) (F σ) k
  have hint : IntegrableOn (fun σ => (lam : ℂ) * F σ k) (Set.Icc 0 r) := by
    exact (hF.integrable k).congr_fun (fun σ _ => hgen σ) measurableSet_Icc
  have heq : ∀ τ ∈ Set.Icc 0 r, F τ k = c k + ∫ σ in (0 : ℝ)..τ, (lam : ℂ) * F σ k := by
    intro τ hτ
    have := hF.eq k τ hτ
    rw [this]
    exact congrArg (c k + ·) (intervalIntegral.integral_congr (fun σ _ => hgen σ))
  have hcont : ContinuousOn (fun τ => F τ k) (Set.Icc 0 r) := by
    have hu : Set.uIcc (0 : ℝ) r = Set.Icc 0 r := Set.uIcc_of_le hr
    have h1 : ContinuousOn (fun x => ∫ σ in (0 : ℝ)..x, (lam : ℂ) * F σ k) (Set.Icc 0 r) := by
      rw [← hu]
      exact intervalIntegral.continuousOn_primitive_interval (by rw [hu]; exact hint)
    exact (continuousOn_const.add h1).congr heq
  refine eq_exp_mul_of_integral_eq lam (c k) (fun τ => F τ k) hcont ?_ τ hτ
  intro τ' hτ'
  rw [heq τ' hτ', intervalIntegral.integral_const_mul]

private theorem isSmooth_const' (c : ℝ) : Torus.IsSmooth (fun _ : Torus d => c) := by
  unfold Torus.IsSmooth Torus.IsCk Torus.lift
  exact contDiff_const

/-- [D4] The Fourier coefficients of the propagator at density `1`: `(U^{0,r}ψ)^(k) = e^{λ_k r} ψ̂(k)`.
Route (`r = 0`: `PDE.MFSemigroup.propagator_zero`, `ClassicalAux.convKernelFacts`): for `r > 0`,
`PDE.MFOneLe.frozen_classical_of_one_le` (`HRS/PDE/MeanFieldOneLe.lean:237`, `ρβ = 1`, `V = 0`, `T' = r`; positivity/probability/smoothness of `1`:
`eqevo_isProb_one`, `PDE.MFSemigroup.isCk_nat_of_isSmooth`) gives `AdjointData` and a classical solution `F`;
`PDE.MFOneLe.propagator_frozen_eq_of_one_le` (`τ = T' = r`) gives `propagator .. 0 r ψ = F 0`;
`PDE.classical_toCoeff_isForwardSolution` (`HRS/PDE/WellPosed.lean:344`, `hV : IsCk 1 (fun _ => 0)`, `hμ` const) gives
`IsForwardSolution D (fun _ => 1) r (coeffOf ψ) (fun τ => coeffOf (F (r - τ)))` and `ContinuousInHs 2`; coordinatewise continuity from
`PDE.MFApriori.norm_coeff_le_hsNorm`-type bound (or from `cont_c2` of the classical solution); by [D1] (`mfData d s _ _ (fun _ => 0) β _` is
definitionally `modelData d s _ _ (-1) β⁻¹ _`) the equation reads `G τ = ψ̂(k) + λ_k ∫_0^τ G`; apply [D2] at `τ = r`. -/
theorem coeffOf_propagator_hom (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {r : ℝ} (hr : 0 ≤ r) {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) (k : Lattice d) :
    PDE.coeffOf (propagator (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) (fun _ => 1) 0 r ψ) k =
      ((Real.exp (PDE.modelEigenvalue d s β⁻¹ (-1) k * r) : ℝ) : ℂ) * PDE.coeffOf ψ k := by
  have h0s : Torus.IsSmooth (fun _ : Torus d => (0 : ℝ)) := isSmooth_const' 0
  have h1s : Torus.IsSmooth (fun _ : Torus d => (1 : ℝ)) := isSmooth_const' 1
  rcases eq_or_lt_of_le hr with h | h
  · subst h
    have hK : PDE.ClassicalAux.ConvKernelFacts d (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ).s :=
      PDE.ClassicalAux.convKernelFacts hd _
    change PDE.coeffOf (propagator _ (fun _ => fun _ : Torus d => (1 : ℝ)) 0 0 ψ) k = _
    rw [PDE.MFSemigroup.propagator_zero _ hK (PDE.MFSemigroup.isCk_nat_of_isSmooth h0s 1) (fun _ => fun _ : Torus d => (1 : ℝ))
      (PDE.MFSemigroup.isCk_nat_of_isSmooth h1s 1) (PDE.MFSemigroup.isCk_nat_of_isSmooth hψ 2)]
    simp
  · obtain ⟨R, MB, Λ, VB, hA, F, hF⟩ := PDE.MFOneLe.frozen_classical_of_one_le hd s hs0 hsd β hβ
      (fun _ => 0) h0s (fun _ => 1) MD.EQEvoUnif.eqevo_isProb_one h1s (fun _ => one_pos) ψ hψ r h
    have hprop := PDE.MFOneLe.propagator_frozen_eq_of_one_le hd s hs0 hsd (PDE.mStar d)
      (by unfold PDE.mStar; omega) R MB Λ VB _ 0 r (fun _ : Torus d => (1 : ℝ)) hA ⟨h, le_rfl⟩ hF ⟨h, le_rfl⟩
    change PDE.coeffOf (propagator _ (fun _ => fun _ : Torus d => (1 : ℝ)) 0 r ψ) k = _
    rw [hprop]
    have hsol := (PDE.classical_toCoeff_isForwardSolution hd (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ)
      (PDE.MFSemigroup.isCk_nat_of_isSmooth h0s 1) (fun _ => 1) r h
      (fun _ _ => PDE.MFSemigroup.isCk_nat_of_isSmooth h1s 1) ψ F hF).1
    have := forward_const_coeff hd hs0 hsd hβ hr hsol k ⟨hr, le_rfl⟩
    simpa [sub_self] using this

/-- [D5] `∫ (U^{0,r}ψ) ψ_k = e^{λ_k r} ∫ ψ ψ_k`.  Route: [D5a] for `f = U^{0,r}ψ` (continuous: `eqgld_prop_smooth`,
`HRS/MD/EQGaussLyapDet.lean:107`, or `Torus.IsCk` of the classical solution) and for `ψ`, [D4] at `k` and `-k`, [D3]. -/
theorem integral_propagator_mul_cosTest (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {r : ℝ} (hr : 0 ≤ r) {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) (k : Lattice d) :
    ∫ x, propagator (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) (fun _ => 1) 0 r ψ x * PDE.cosTest k x =
      Real.exp (PDE.modelEigenvalue d s β⁻¹ (-1) k * r) * ∫ x, ψ x * PDE.cosTest k x := by
  have hsm : Torus.IsSmooth (propagator (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ)
      (fun _ => fun _ : Torus d => (1 : ℝ)) 0 r ψ) :=
    MD.EQGaussLyapDet.eqgld_prop_smooth hd hs0 hsd (fun _ => 0) (isSmooth_const' 0) hβ
      (fun _ => 1) MD.EQEvoUnif.eqevo_isProb_one (isSmooth_const' 1) (fun _ => one_pos) ψ hψ 0 r le_rfl hr
  have hc : Continuous (propagator (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ)
      (fun _ => fun _ : Torus d => (1 : ℝ)) 0 r ψ) :=
    PDE.ClassicalAux.continuous_of_isCk (PDE.MFSemigroup.isCk_nat_of_isSmooth hsm 1)
  have hψc : Continuous ψ :=
    PDE.ClassicalAux.continuous_of_isCk (PDE.MFSemigroup.isCk_nat_of_isSmooth hψ 1)
  apply Complex.ofReal_injective
  have h1 := integral_mul_cosTest_eq_coeff k hc
  have h2 := integral_mul_cosTest_eq_coeff k hψc
  have e1 : PDE.coeffOf (propagator (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ)
      (fun _ => fun _ : Torus d => (1 : ℝ)) 0 r ψ) k =
      ((Real.exp (PDE.modelEigenvalue d s β⁻¹ (-1) k * r) : ℝ) : ℂ) * PDE.coeffOf ψ k :=
    coeffOf_propagator_hom hd hs0 hsd hβ hr hψ k
  have e2 : PDE.coeffOf (propagator (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ)
      (fun _ => fun _ : Torus d => (1 : ℝ)) 0 r ψ) (-k) =
      ((Real.exp (PDE.modelEigenvalue d s β⁻¹ (-1) k * r) : ℝ) : ℂ) * PDE.coeffOf ψ (-k) := by
    have := coeffOf_propagator_hom hd hs0 hsd hβ hr hψ (-k)
    rw [modelEigenvalue_neg] at this
    exact this
  change (((∫ x, propagator (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ)
      (fun _ => fun _ : Torus d => (1 : ℝ)) 0 r ψ x * PDE.cosTest k x : ℝ)) : ℂ) = _
  rw [h1, Complex.ofReal_mul, h2, e1, e2]
  ring

end HRS.MH.EdgeSharp
