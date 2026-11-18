import HRS.MS.SA12W2E
import HRS.MS.Ker1Aux4
import HRS.MS.SA12V1
import HRS.Whole.RegMF

/-!
# S.A.12 C5 (SA12W2 worker), part F: regime scaling and the rescaled density (`R26-T5.T01/T02`, first half)
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

/-- The regime is invariant under the rescaling `M ↦ L^{-s-2}M`, `ν ↦ ν/L²`, `ν₀ ↦ ν₀/L²` (R2b is excluded by `RdRegimeHolds`). -/
theorem sa12w2_regime (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ν ν₀ L T : ℝ) (hL : 0 < L)
    (Rg : PDE.Regime) (ρ : ℝ → Torus d → ℝ) (hR : RdRegimeHolds Rg d s M ν ν₀) :
    PDE.Regime.Holds Rg d s ((L ^ (-s - 2)) • M) (ν / L ^ 2) (ν₀ / L ^ 2) T ρ := by
  have hsym : ∀ c : ℝ, Torus.symPart (c • M) = c • Torus.symPart M := by
    intro c
    unfold Torus.symPart
    rw [Matrix.transpose_smul, ← smul_add, smul_comm]
  have hc : 0 ≤ L ^ (-s - 2) := (Real.rpow_pos_of_pos hL _).le
  cases Rg with
  | R1 => simpa [PDE.Regime.Holds, RdRegimeHolds] using hR
  | R2a =>
    refine ⟨hR.1, ?_⟩
    rw [hsym, hR.2, smul_zero]
  | R2b lam0 => simp [RdRegimeHolds] at hR
  | R2c =>
    refine ⟨hR.1, hR.2.1, ?_⟩
    unfold Torus.SymNonpos
    rw [hsym, ← smul_neg]
    exact hR.2.2.smul hc
  | R3 =>
    exact ⟨hR.1, div_pos hR.2.1 (pow_pos hL 2), div_le_div_of_nonneg_right hR.2.2 (pow_pos hL 2).le⟩

/-- Clamped reversed time. -/
def sa12w2_tau (t T r : ℝ) : ℝ := min (max (t - r) 0) T

theorem sa12w2_tau_mem {t T : ℝ} (hT : 0 ≤ T) (r : ℝ) : sa12w2_tau t T r ∈ Icc (0 : ℝ) T :=
  ⟨le_min (le_max_right _ _) hT, min_le_right _ _⟩

theorem sa12w2_tau_eq {t T r : ℝ} (ht : t ≤ T) (hr : r ∈ Icc (0 : ℝ) T) :
    sa12w2_tau t T r = max (t - r) 0 := by
  unfold sa12w2_tau
  have hT0 : (0 : ℝ) ≤ T := hr.1.trans hr.2
  exact min_eq_left (max_le (by linarith [hr.1]) hT0)

/-- The rescaled density `y ↦ L^d g (L y)` as a torus function. -/
def sa12w2_dens (L : ℝ) (g : Euc d → ℝ) : Torus d → ℝ := sa12w2_desc L fun x => L ^ d * g x

theorem sa12w2_dens_lift {L : ℝ} {g : Euc d → ℝ}
    (hper : ∀ (x : Euc d) (z : Fin d → ℤ), g (x + L • latticePt z) = g x) (y : Euc d) :
    Torus.lift (sa12w2_dens L g) y = L ^ d * g (L • y) :=
  sa12w2_lift_desc (f := fun x => L ^ d * g x) (fun x z => by rw [hper x z]) y

theorem sa12w2_dens_prob {L : ℝ} (hL : 0 < L) {g : Euc d → ℝ}
    (hper : ∀ (x : Euc d) (z : Fin d → ℤ), g (x + L • latticePt z) = g x) (hg : ContDiff ℝ ∞ g)
    (hnn : ∀ x, 0 ≤ g x) (hint : ∫ x in periodBox d L, g x = 1) :
    IsProbDensity (sa12w2_dens L g) := by
  have hck : Torus.IsCk 0 (sa12w2_dens L g) :=
    sa12w2_contDiff_desc (f := fun x => L ^ d * g x) (fun x z => by rw [hper x z]) hL.ne'
      (contDiff_const.mul (hg.of_le (by simp)))
  have hc : Continuous (sa12w2_dens L g) := Torus.continuous_of_continuous_lift hck.continuous
  refine ⟨fun x => ?_, hc.measurable, ?_⟩
  · exact mul_nonneg (pow_nonneg hL.le _) (hnn _)
  · rw [sa12w2_torus_int_cube _ hc.aestronglyMeasurable]
    have : ∀ w : Euc d, sa12w2_dens L g (Torus.mk w) = L ^ d * g (L • w) := fun w =>
      sa12w2_dens_lift hper w
    simp_rw [this]
    rw [sa12w2_cube_box hL (fun x => L ^ d * g x), integral_const_mul, hint]
    simp [smul_eq_mul]
    field_simp

/-- Uniform `C_b^n` bound of the rescaled densities over `τ ∈ [0,T]`. -/
theorem sa12w2_dens_cb {L T : ℝ} (hL : 0 < L) {μ : ℝ → Euc d → ℝ}
    (hper : ∀ τ ∈ Icc (0 : ℝ) T, ∀ (x : Euc d) (z : Fin d → ℤ), μ τ (x + L • latticePt z) = μ τ x)
    (hsm : ∀ τ ∈ Icc (0 : ℝ) T, ContDiff ℝ ∞ (μ τ)) (hTime : PeriodicTimeSmooth T μ) (n : ℕ) :
    ∃ Λ : ℝ, ∀ τ ∈ Icc (0 : ℝ) T, Torus.cbNorm n (sa12w2_dens L (μ τ)) ≤ Λ := by
  have hB : ∀ j : ℕ, ∃ B : ℝ, ∀ τ ∈ Icc (0 : ℝ) T, ∀ x : Euc d, ‖iteratedFDeriv ℝ j (μ τ) x‖ ≤ B := by
    intro j
    exact sa12v_bdd_param 0 T L hL (fun q : ℝ × Euc d => iteratedFDeriv ℝ j (μ q.1) q.2) (hTime j)
      (fun σ hσ x k => sa12v_iter_periodic L (hper σ hσ) j x k)
  choose Bf hBf using hB
  refine ⟨∑ j ∈ Finset.range (n + 1), L ^ d * L ^ j * |Bf j|, fun τ hτ => ?_⟩
  unfold Torus.cbNorm
  refine Finset.sum_le_sum fun j _ => ?_
  refine ciSup_le fun x => ?_
  have hlift : Torus.lift (sa12w2_dens L (μ τ)) = fun y => L ^ d • (fun y => μ τ (L • y)) y := by
    funext y
    rw [sa12w2_dens_lift (hper τ hτ)]
    simp
  rw [hlift]
  have hcd : ContDiffAt ℝ j (fun y : Euc d => μ τ (L • y)) x :=
    (((hsm τ hτ).comp (contDiff_const_smul L)).of_le (by exact_mod_cast le_top)).contDiffAt
  rw [iteratedFDeriv_const_smul_apply' hcd, HRS.MS.Ker1.ker1_iteratedFDeriv_comp_smul (μ τ) hL.ne' j x]
  have h1 := hBf j τ hτ (L • x)
  calc ‖L ^ d • L ^ j • iteratedFDeriv ℝ j (μ τ) (L • x)‖
      = L ^ d * (L ^ j * ‖iteratedFDeriv ℝ j (μ τ) (L • x)‖) := by
        rw [norm_smul, norm_smul]
        simp [abs_of_pos hL, abs_of_nonneg (pow_nonneg hL.le _)]
    _ ≤ L ^ d * (L ^ j * |Bf j|) := by
        gcongr
        exact h1.trans (le_abs_self _)
    _ = L ^ d * L ^ j * |Bf j| := by ring

end HRS.PDE.SA12W2
