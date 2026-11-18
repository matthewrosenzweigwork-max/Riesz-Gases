import HRS.MS.SA12W2J
import HRS.MS.ToriCoefBAux1

/-!
# S.A.12 C5 (SA12W2 worker), part K: the nonlocal bridge (`R26-T5.T05`, nonlocal half)

`sa12w2_nonlocal_bridge`: for `F(x) = u(x/L)` the periodic nonlocal term `perNonlocal L γ M μ F` at `L y` equals the
unit-torus cancellation-convention term `∑_j (∇g * (ρ (M₁ᵀ∇u)_j))_j (y)` with `M₁ = L^{-s-2}M`, `ρ = L^d μ(L·)`.
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

theorem sa12w2_g1_mul_int (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (y' : Euc d) {q : Euc d → ℝ}
    (hq : Continuous q) :
    IntegrableOn (fun w => HRS.MS.Ker1.ker1_g1 d s (y' - w) * q w) (HRS.MC.CepP3.cubeE d) := by
  have hT : Integrable (fun v : Torus d => periodicRiesz d s (Torus.mk y' - v)) :=
    (integrable_comp_sub_left (periodicRiesz d s) (Torus.mk y')).2
      (HRS.MS.Ker1.ker1_g1_integrable hd hs0 hsd)
  have hloc : LocallyIntegrable (fun w : Euc d => HRS.MS.Ker1.ker1_g1 d s (y' - w)) volume := by
    have := HRS.MS.Ker1.ker1_locInt_comp_mk hT
    convert this using 2
    simp [HRS.MS.Ker1.ker1_g1, sa12w2_mk_sub]
  have hK := HRS.MS.ToriCoefB.tcb_compact_Icc (d := d) 0 1
  have h1 := (hloc.integrableOn_isCompact hK).mul_continuousOn hq.continuousOn hK
  refine h1.mono_set ?_
  intro w hw i
  exact ⟨(hw i).1, (hw i).2.le⟩

theorem sa12w2_Hf_smooth {s L : ℝ} (hL : 0 < L) (M : Matrix (Fin d) (Fin d) ℝ) {μt : Euc d → ℝ}
    (hμ : ContDiff ℝ ∞ μt)
    (hμp : ∀ (x : Euc d) (z : Fin d → ℤ), μt (x + L • latticePt z) = μt x) (u : Torus d → ℝ)
    (hu : ContDiff ℝ ∞ (Torus.lift u)) (i : Fin d) :
    ContDiff ℝ ∞ (Torus.lift (fun y => sa12w2_dens L μt y *
      (Torus.matVec ((L ^ (-s - 2)) • M).transpose (Torus.grad u y)) i)) := by
  set F : Euc d → ℝ := fun x => Torus.lift u (L⁻¹ • x) with hFdef
  have hF : ContDiff ℝ ∞ F := hu.comp (contDiff_const_smul L⁻¹)
  have hfd : ∀ j : Fin d, ContDiff ℝ ∞ (fun y => fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))) := fun j =>
    (hF.fderiv_right (m := ∞) (by exact_mod_cast le_top)).clm_apply contDiff_const
  have hΞs : ContDiff ℝ ∞ (fun y => ∑ j, M j i * (μt y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)))) :=
    ContDiff.sum fun j _ => contDiff_const.mul (hμ.mul (hfd j))
  have : Torus.lift (fun y => sa12w2_dens L μt y *
      (Torus.matVec ((L ^ (-s - 2)) • M).transpose (Torus.grad u y)) i) =
      fun x => (L ^ (s + 1 - d))⁻¹ * ∑ j, M j i * (μt (L • x) * fderiv ℝ F (L • x) (EuclideanSpace.single j (1 : ℝ))) := by
    funext x
    have h := sa12w2_Xi_scale (s := s) hL M hμp u hu i x
    rw [eq_inv_mul_iff_mul_eq₀ (Real.rpow_pos_of_pos hL _).ne']
    exact h.symm
  rw [this]
  exact contDiff_const.mul (hΞs.comp (contDiff_const_smul L))

theorem sa12w2_nonlocal_bridge (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {L : ℝ} (hL : 0 < L)
    {γ : Euc d → ℝ} (hγ : IsPeriodicRieszKernel d s L γ) (M : Matrix (Fin d) (Fin d) ℝ) {μt : Euc d → ℝ}
    (hμ : ContDiff ℝ ∞ μt)
    (hμp : ∀ (x : Euc d) (z : Fin d → ℤ), μt (x + L • latticePt z) = μt x) (u : Torus d → ℝ)
    (hu : ContDiff ℝ ∞ (Torus.lift u)) (y' : Euc d) :
    perNonlocal L γ M μt (fun x => Torus.lift u (L⁻¹ • x)) (L • y') =
      ∑ j, (convGradConv (periodicRieszGrad d s) (fun y => sa12w2_dens L μt y *
        (Torus.matVec ((L ^ (-s - 2)) • M).transpose (Torus.grad u y)) j) (Torus.mk y')) j := by
  set F : Euc d → ℝ := fun x => Torus.lift u (L⁻¹ • x) with hFdef
  have hF : ContDiff ℝ ∞ F := hu.comp (contDiff_const_smul L⁻¹)
  have hFp : ∀ (x : Euc d) (z : Fin d → ℤ), F (x + L • latticePt z) = F x := by
    intro x z
    simp only [hFdef, smul_add, inv_smul_smul₀ hL.ne']
    exact Torus.lift_periodic u _ z
  have hfd : ∀ j : Fin d, ContDiff ℝ ∞ (fun y => fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))) := fun j =>
    (hF.fderiv_right (m := ∞) (by exact_mod_cast le_top)).clm_apply contDiff_const
  set hfun : Fin d → Euc d → ℝ := fun j y => μt y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)) with hhdef
  have hh : ∀ j, ContDiff ℝ ∞ (hfun j) := fun j => hμ.mul (hfd j)
  have hhp : ∀ j (x : Euc d) (z : Fin d → ℤ), hfun j (x + L • latticePt z) = hfun j x := by
    intro j x z
    simp only [hhdef]
    rw [hμp, sa12v_fderiv_periodic L hFp _ x z]
  set q : Fin d → Fin d → Euc d → ℝ := fun i j y => fderiv ℝ (hfun j) y (EuclideanSpace.single i (1 : ℝ))
    with hqdef
  have hqc : ∀ i j, Continuous (q i j) := fun i j =>
    ((hh j).fderiv_right (m := ∞) (by exact_mod_cast le_top)).clm_apply contDiff_const |>.continuous
  have h1 : perNonlocal L γ M μt F (L • y') = ∑ i, ∑ j, M j i * perConv L γ (q i j) (L • y') := by
    unfold perNonlocal
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [periodic_convolution_derivative L hL γ _ hγ.locInt hγ.periodic ((hh j).of_le (by simp)) (hhp j) i
      (L • y')]
  have h2 : ∀ i j, perConv L γ (q i j) (L • y') = L ^ d * L ^ (-s) *
      ∫ w in HRS.MC.CepP3.cubeE d, HRS.MS.Ker1.ker1_g1 d s (y' - w) * q i j (L • w) := fun i j =>
    sa12w2_perConv_torus hd hs0 hsd hL hγ _ y'
  have hint : ∀ i j, IntegrableOn (fun w => HRS.MS.Ker1.ker1_g1 d s (y' - w) * q i j (L • w))
      (HRS.MC.CepP3.cubeE d) := fun i j =>
    sa12w2_g1_mul_int hd hs0 hsd y' ((hqc i j).comp (continuous_const_smul L))
  have hsum : ∫ w in HRS.MC.CepP3.cubeE d, HRS.MS.Ker1.ker1_g1 d s (y' - w) *
        ∑ i, ∑ j, M j i * q i j (L • w) =
      ∑ i, ∑ j, M j i * ∫ w in HRS.MC.CepP3.cubeE d, HRS.MS.Ker1.ker1_g1 d s (y' - w) * q i j (L • w) := by
    have e : (fun w => HRS.MS.Ker1.ker1_g1 d s (y' - w) * ∑ i, ∑ j, M j i * q i j (L • w)) =
        fun w => ∑ i, ∑ j, M j i * (HRS.MS.Ker1.ker1_g1 d s (y' - w) * q i j (L • w)) := by
      funext w
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hint i j).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hint i j).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
  have hconv := sa12w2_conv_cube hd s hs0 hsd (fun j y => sa12w2_dens L μt y *
    (Torus.matVec ((L ^ (-s - 2)) • M).transpose (Torus.grad u y)) j) (fun j =>
    (sa12w2_Hf_smooth (s := s) hL M hμ hμp u hu j).of_le (by simp)) y'
  rw [h1]
  simp_rw [h2]
  have e3 : ∑ i : Fin d, ∑ j : Fin d, M j i * (L ^ d * L ^ (-s) *
      ∫ w in HRS.MC.CepP3.cubeE d, HRS.MS.Ker1.ker1_g1 d s (y' - w) * q i j (L • w)) =
      L ^ d * L ^ (-s) * ∫ w in HRS.MC.CepP3.cubeE d, HRS.MS.Ker1.ker1_g1 d s (y' - w) *
        ∑ i, ∑ j, M j i * q i j (L • w) := by
    rw [hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e3]
  have e4 : ∀ w : Euc d, ∑ i, ∑ j, M j i * q i j (L • w) =
      L ^ (s - d) * ∑ i : Fin d, Torus.partialDeriv i (fun y => sa12w2_dens L μt y *
        (Torus.matVec ((L ^ (-s - 2)) • M).transpose (Torus.grad u y)) i) (Torus.mk w) := fun w =>
    sa12w2_kk_scale hL M hμ hμp u hu w
  simp_rw [e4]
  have hc : L ^ d * L ^ (-s) * L ^ (s - d) = 1 := by
    rw [← Real.rpow_natCast L d, ← Real.rpow_add hL, ← Real.rpow_add hL]
    have : (d : ℝ) + -s + (s - d) = 0 := by ring
    rw [this, Real.rpow_zero]
  rw [hconv]
  have e5 : ∀ w : Euc d, HRS.MS.Ker1.ker1_g1 d s (y' - w) * (L ^ (s - d) * ∑ i : Fin d,
      Torus.partialDeriv i (fun y => sa12w2_dens L μt y *
        (Torus.matVec ((L ^ (-s - 2)) • M).transpose (Torus.grad u y)) i) (Torus.mk w)) =
      L ^ (s - d) * (HRS.MS.Ker1.ker1_g1 d s (y' - w) * ∑ i : Fin d,
      Torus.partialDeriv i (fun y => sa12w2_dens L μt y *
        (Torus.matVec ((L ^ (-s - 2)) • M).transpose (Torus.grad u y)) i) (Torus.mk w)) := fun w => by ring
  simp_rw [e5]
  rw [integral_const_mul, ← mul_assoc, hc, one_mul]

end HRS.PDE.SA12W2
