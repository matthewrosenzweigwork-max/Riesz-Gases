import HRS.MS.ThCorrSob
import HRS.MS.UniqN2aA
import HRS.MS.UniqN1aA
import HRS.MS.Ker1Aux4
import HRS.Whole.Adjoint
import HRS.Prob.Gaussian

/-!
# UL-1 (S5.1 nonlocal term), part 1: `ulNL`, `generatorW_fixed`, the cutoff and the far kernel

* `ulNL s M ρ u x = ∑_j (convGradConvW (∇g) (ρ (Mᵀ∇u)_j) x)_j`, the nonlocal term `N u` of the generator
  `νΔ - Qx·∇ + c·∇ - N` of `fixedViscosityCoeff s M Q ν c ρ`; `generatorW_fixed` is the unfolding.
* `ul1Th = ul1B`: an even smooth bump, `= 1` on `B(0,1/8)`, `= 0` off `B(0,1/4)`.
* `ul1Gh z = (1 - ul1Th z) g(z)` is smooth (`g = rieszKernel d s`), equal to `g` off `B(0,1/4)`;
  `ul1K i = ∂_i ul1Gh` is a smooth kernel all of whose derivatives are bounded (bounds from `ker1_E_bound`).

Helper lemmas carry the prefix `ul1_`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.Ul

open HRS HRS.Whole HRS.MS.UniqN2a HRS.MS.UniqN0 HRS.MS.UniqN1a

variable {d : ℕ}

/-- The nonlocal term `N u (x) = ∑_j (convGradConvW (∇g) (ρ (Mᵀ∇u)_j) x)_j` of the generator of
`fixedViscosityCoeff s M Q ν c ρ` (with the sign convention `generatorW = νΔ + b·∇ - N`). -/
def ulNL (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ) (u : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∑ j, (convGradConvW (rieszKernelGrad d s)
      (fun y => ρ y * (Torus.matVec M.transpose (gradient u y)) j) x) j

/-- Unfolding of the generator of `fixedViscosityCoeff` at time `0`. -/
theorem generatorW_fixed (s : ℝ) (M Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (c : Euc d → Euc d)
    (ρ : Euc d → ℝ) (u : Euc d → ℝ) (x : Euc d) :
    generatorW (fixedViscosityCoeff s M Q ν c ρ) 0 u x =
      ν * Laplacian.laplacian u x - inner ℝ (Torus.matVec Q x) (gradient u x) +
        inner ℝ (c x) (gradient u x) - ulNL s M ρ u x := by
  unfold generatorW fixedViscosityCoeff ulNL
  simp only [inner_add_left, inner_neg_left]
  ring

/-! ### The cutoff -/

/-- the bump `1` on `B̄(0,1/8)`, `0` off `B(0,1/4)` -/
def ul1B (d : ℕ) : ContDiffBump (0 : Euc d) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- the cutoff `θ'` as a function -/
def ul1Th (d : ℕ) (z : Euc d) : ℝ := ul1B d z

theorem ul1_th_contDiff : ContDiff ℝ ∞ (ul1Th d) := (ul1B d).contDiff

theorem ul1_th_compact : HasCompactSupport (ul1Th d) := (ul1B d).hasCompactSupport

theorem ul1_th_one {z : Euc d} (hz : ‖z‖ ≤ 1 / 8) : ul1Th d z = 1 :=
  (ul1B d).one_of_mem_closedBall (by simpa [ul1B] using hz)

theorem ul1_th_zero {z : Euc d} (hz : 1 / 4 ≤ ‖z‖) : ul1Th d z = 0 :=
  (ul1B d).zero_of_le_dist (by simpa [ul1B, dist_zero_right] using hz)

theorem ul1_th_nonneg (z : Euc d) : 0 ≤ ul1Th d z := (ul1B d).nonneg

theorem ul1_th_le_one (z : Euc d) : ul1Th d z ≤ 1 := (ul1B d).le_one

theorem ul1_th_neg (z : Euc d) : ul1Th d (-z) = ul1Th d z := (ul1B d).neg z

theorem ul1_fderiv_th_neg (z v : Euc d) :
    fderiv ℝ (ul1Th d) (-z) v = - fderiv ℝ (ul1Th d) z v := by
  have h : ul1Th d = fun w => ul1Th d (-w) := funext fun w => (ul1_th_neg w).symm
  have hd : HasFDerivAt (fun w : Euc d => ul1Th d (-w))
      ((fderiv ℝ (ul1Th d) (-z)).comp (-ContinuousLinearMap.id ℝ (Euc d))) z :=
    ((ul1_th_contDiff.differentiable (by simp)) (-z)).hasFDerivAt.comp z (hasFDerivAt_id z).neg
  have h2 := hd.fderiv
  rw [← h] at h2
  have := congrArg (fun L => L v) h2
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply, map_neg] at this
  rw [this]; simp

theorem ul1_fderiv_th_zero {z : Euc d} (hz : ‖z‖ < 1 / 8) (v : Euc d) :
    fderiv ℝ (ul1Th d) z v = 0 := by
  have hev : ul1Th d =ᶠ[𝓝 z] fun _ => 1 := by
    filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hz] with w hw
    exact ul1_th_one hw.le
  rw [hev.fderiv_eq]; simp

/-! ### The smooth far part `(1 - θ') g` and its kernel -/

/-- `ĝ = (1 - θ') g`, smooth, equal to `g` off `B(0,1/4)` and `0` near the origin -/
def ul1Gh (d : ℕ) (s : ℝ) (z : Euc d) : ℝ := (1 - ul1Th d z) * rieszKernel d s z

theorem ul1_Gh_contDiff (s : ℝ) : ContDiff ℝ ∞ (ul1Gh d s) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    have hev : ul1Gh d s =ᶠ[𝓝 (0 : Euc d)] fun _ => 0 := by
      filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds
        (show ‖(0 : Euc d)‖ < 1 / 8 by simp)] with w hw
      simp [ul1Gh, ul1_th_one hw.le]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have h1 : ContDiffAt ℝ ∞ (fun w : Euc d => 1 - ul1Th d w) z :=
      (contDiff_const.sub ul1_th_contDiff).contDiffAt
    have h2 : ContDiffAt ℝ ∞ (rieszKernel d s) z :=
      (rieszKernel_contDiffOn (d := d) (s := s)).contDiffAt
        (isOpen_ne.mem_nhds (show z ∈ {x : Euc d | x ≠ 0} from hz))
    exact h1.mul h2

theorem ul1_Gh_eq {s : ℝ} {z : Euc d} (hz : 1 / 4 ≤ ‖z‖) : ul1Gh d s z = rieszKernel d s z := by
  simp [ul1Gh, ul1_th_zero hz]

/-- the far kernel `K_i = ∂_i ĝ` -/
def ul1K (d : ℕ) (s : ℝ) (i : Fin d) (z : Euc d) : ℝ :=
  fderiv ℝ (ul1Gh d s) z (EuclideanSpace.single i 1)

theorem ul1_K_contDiff (s : ℝ) (i : Fin d) : ContDiff ℝ ∞ (ul1K d s i) := by
  have h : ContDiff ℝ ∞ (fderiv ℝ (ul1Gh d s)) :=
    (ul1_Gh_contDiff s).fderiv_right (m := ∞) (by simp)
  exact h.clm_apply contDiff_const

/-- for `1 ≤ N`: all derivatives of `ĝ` are bounded -/
theorem ul1_Gh_deriv_bdd {s : ℝ} (hs0 : 0 ≤ s) (N : ℕ) (hN : 1 ≤ N) :
    ∃ B : ℝ, ∀ z, ‖iteratedFDeriv ℝ N (ul1Gh d s) z‖ ≤ B := by
  have hNs : 0 < (N : ℝ) + s := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  obtain ⟨C, hC0, hC⟩ := HRS.MS.Ker1.ker1_E_bound (d := d) hs0 N hNs
  have hcont : Continuous (iteratedFDeriv ℝ N (ul1Gh d s)) :=
    (ul1_Gh_contDiff s).continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨B1, hB1⟩ := (isCompact_closedBall (0 : Euc d) (1 / 3)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max B1 (C * 3 ^ (s + N)), fun z => ?_⟩
  by_cases hz : ‖z‖ ≤ 1 / 3
  · exact (hB1 z (mem_closedBall_zero_iff.2 hz)).trans (le_max_left _ _)
  · have hz' : 1 / 3 < ‖z‖ := not_le.1 hz
    have hev : ul1Gh d s =ᶠ[𝓝 z] rieszKernel d s := by
      filter_upwards [isOpen_lt continuous_const continuous_norm |>.mem_nhds
        (show (1 / 4 : ℝ) < ‖z‖ by linarith)] with w hw
      exact ul1_Gh_eq hw.le
    rw [(hev.iteratedFDeriv ℝ N).eq_of_nhds]
    refine ((hC z (norm_pos_iff.1 (by linarith))).trans ?_).trans (le_max_right _ _)
    have h3 : ‖z‖ ^ (-s - N) ≤ (1 / 3) ^ (-s - N) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hz'.le (by linarith)
    have h4 : ((1 : ℝ) / 3) ^ (-s - N) = 3 ^ (s + N) := by
      rw [Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow,
        show -s - N = -(s + N) by ring, Real.rpow_neg (by norm_num)]
      simp
    rw [h4] at h3
    exact mul_le_mul_of_nonneg_left h3 hC0

/-- all derivatives of the far kernel `K_i` are bounded -/
theorem ul1_K_deriv_bdd {s : ℝ} (hs0 : 0 ≤ s) (i : Fin d) (n : ℕ) :
    ∃ B : ℝ, ∀ z, ‖iteratedFDeriv ℝ n (ul1K d s i) z‖ ≤ B := by
  obtain ⟨B, hB⟩ := ul1_Gh_deriv_bdd (d := d) hs0 (n + 1) (by omega)
  refine ⟨B, fun z => ?_⟩
  have h1 : ul1K d s i = fun w => (fderiv ℝ (ul1Gh d s) w) (EuclideanSpace.single i 1) := rfl
  have hd : ContDiff ℝ ∞ (fderiv ℝ (ul1Gh d s)) :=
    (ul1_Gh_contDiff s).fderiv_right (m := ∞) (by simp)
  calc ‖iteratedFDeriv ℝ n (ul1K d s i) z‖
      ≤ ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ * ‖iteratedFDeriv ℝ n (fderiv ℝ (ul1Gh d s)) z‖ := by
        rw [h1]
        exact norm_iteratedFDeriv_clm_apply_const (hd.contDiffAt) (by exact_mod_cast le_top)
    _ ≤ B := by
        rw [norm_iteratedFDeriv_fderiv]
        simpa using hB z

end HRS.MS.Ul
