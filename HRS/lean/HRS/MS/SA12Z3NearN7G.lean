import HRS.MS.SA12Z3NearN7F

/-!
# S.A.12 N7 (SA12Z3), part G: the energy bound for one index tuple

For `∂^{idx}` with `|idx| ≤ m`: `|∫ ω² ∂^{idx}F ∂^{idx}(eucNonlocal a F)| ≤ A₁ ∫ W Y`,
`Y = ∑_{r ≤ m} ∑_γ (∂^γ F)²`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

theorem sa12z3_hess_cont {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i j : Fin d) {v : Euc d → ℝ}
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) : Continuous (hessRiesz d s i j v) := by
  have hf : hessRiesz d s i j v = fun y => D1 i (HRS.Whole.AppendixALemmas.kernelConvDeriv d s j v) y :=
    funext fun x => sa12z3_hess_eq hs0 hsd i j hv hvc x
  rw [hf]
  exact HRS.MS.UniqN1c.n1c_D1_kcd_cont hs0 hsd hv hvc j i

theorem sa12z3_firstRiesz_cont {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d) {v : Euc d → ℝ}
    (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v) : Continuous (firstRiesz d s i v) := by
  have hK : firstRiesz d s i v = HRS.Whole.convFun (rieszKernel d s) (D1 i v) :=
    funext fun x => sa12z3_firstRiesz_eq' hs0 hsd i hv hvc x
  rw [hK]
  exact K_cont hs0 hsd ((hv.continuous_fderiv one_ne_zero).clm_apply continuous_const) (D1_supp hvc i)

theorem sa12z3_memCb_of_cc {k : ℕ} {f : Euc d → ℝ} (hf : ContDiff ℝ k f) (hfc : HasCompactSupport f) :
    MemCb k f := by
  refine ⟨hf, fun j hj => ?_⟩
  have hc : Continuous (fun x => ‖iteratedFDeriv ℝ j f x‖) :=
    (hf.continuous_iteratedFDeriv (by exact_mod_cast hj)).norm
  have hcs : HasCompactSupport (fun x => ‖iteratedFDeriv ℝ j f x‖) := (hfc.iteratedFDeriv (𝕜 := ℝ) j).norm
  exact hc.bddAbove_range_of_hasCompactSupport hcs

/-- One term of the energy estimate. -/
theorem sa12z3_term {c : Euc d} {R : ℝ} {om W u X v : Euc d → ℝ} {K κ e : ℝ} (hom : Continuous om)
    (homc : HasCompactSupport om) (homs : Function.support om ⊆ closedBall c R)
    (hom1 : ∀ x, |om x| ≤ 1) (hWc : Continuous W) (hWcs : HasCompactSupport W)
    (hWom : ∀ x, om x ^ 2 ≤ W x) (huc : Continuous u) (hX : Continuous X)
    (hK : 0 ≤ K) (hκ : 0 ≤ κ) (he : 0 ≤ e) (hue : ∫ x, W x * u x ^ 2 ≤ e)
    (hop : Real.sqrt (∫ x, ((closedBall c R).indicator X x) ^ 2) ≤ K * Real.sqrt (∫ x, v x ^ 2))
    (hvκ : ∫ x, v x ^ 2 ≤ κ * e) :
    |∫ x, om x ^ 2 * (u x * X x)| ≤ K * Real.sqrt κ * e := by
  refine (sa12z3_pair hom homc homs hom1 hWc hWcs hWom huc hX).trans ?_
  refine sa12z3_close he hκ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hue) (Real.sqrt_nonneg _) ?_
  exact hop.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hvκ) hK)

end HRS.MH.AdjointRd.Phase2SA12Near
