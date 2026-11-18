import HRS.MS.SA12NN2K
import HRS.MS.SA12Z3NearN5A

/-!
# S.A.12 N2 endpoint (SA12X2), part A: polarization of `hessRiesz` and the `L²` bound of `Q_l`

At `s = d - 1`, `Q_l v = x_l H v - H(y_l v)` satisfies `‖1_B Q_l v‖₂ ≤ C ‖v‖₂` for every ball `B`
(by polarization `H^{ij} = ¼ (D_{e_i+e_j}² - D_{e_i-e_j}²)` and `sa12n_dual_ball`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3 HRS.MS.UniqN3a HRS.MS.UniqN2b

variable {d : ℕ}

/-- Polarization of a single Hessian entry. -/
theorem sa12x2_hess_polar {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i j : Fin d) {v : Euc d → ℝ}
    (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v) (y : Euc d) :
    hessRiesz d s i j v y = (1 / 4 : ℝ) *
      (HRS.Whole.convFun (rieszKernel d s) (qq (sa12z3_dp d i j) v) y -
        HRS.Whole.convFun (rieszKernel d s) (qq (sa12z3_dm d i j) v) y) := by
  rw [sa12z3_hess_convFun hs0 hsd i j hv hvc y]
  have hI : ∀ q : Euc d, Integrable (fun x => rieszKernel d s (y - x) * qq q v x) volume := fun q =>
    n2b_conv_integrable hs0 hsd (qq_contDiff hv) (qq_hasCompactSupport hvc) y
  have e1 : HRS.Whole.convFun (rieszKernel d s) (D1 i (D1 j v)) y =
      HRS.Whole.convFun (rieszKernel d s) (fun x => (1 / 4 : ℝ) * (qq (sa12z3_dp d i j) v x -
        qq (sa12z3_dm d i j) v x)) y := by
    unfold HRS.Whole.convFun
    congr 1; funext x
    rw [HRS.MS.UniqN3c.n3c_hess_symm hv j i x, HRS.MS.UniqN1b.n1b_polar hv i j x]
    rfl
  rw [e1]
  unfold HRS.Whole.convFun
  have e2 : (fun x => rieszKernel d s (y - x) * ((1 / 4 : ℝ) * (qq (sa12z3_dp d i j) v x -
        qq (sa12z3_dm d i j) v x))) = fun x => (1 / 4 : ℝ) *
      (rieszKernel d s (y - x) * qq (sa12z3_dp d i j) v x -
        rieszKernel d s (y - x) * qq (sa12z3_dm d i j) v x) := by
    funext x; ring
  rw [e2, integral_const_mul, integral_sub (hI _) (hI _)]

theorem sa12x2_norm_dp_le (i j : Fin d) : ‖sa12z3_dp d i j‖ ^ 2 ≤ 4 := by
  have h : ‖sa12z3_dp d i j‖ ≤ 2 := by
    refine (norm_add_le _ _).trans ?_
    simp; norm_num
  nlinarith [norm_nonneg (sa12z3_dp d i j)]

theorem sa12x2_norm_dm_le (i j : Fin d) : ‖sa12z3_dm d i j‖ ^ 2 ≤ 4 := by
  have h : ‖sa12z3_dm d i j‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    simp; norm_num
  nlinarith [norm_nonneg (sa12z3_dm d i j)]

/-- The `L²` bound of `Q_l v = x_l H v - H(y_l v)` on every ball, at `s = d - 1`. -/
theorem sa12x2_Q_bound (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i j l : Fin d) (v : Euc d → ℝ), ContDiff ℝ 2 v →
      HasCompactSupport v → ∀ (c' : Euc d) (r' : ℝ),
      eLpNorm ((closedBall c' r').indicator (fun x =>
        x l * hessRiesz d ((d : ℝ) - 1) i j v x -
          hessRiesz d ((d : ℝ) - 1) i j (fun y => y l * v y) x)) 2 volume ≤
        ENNReal.ofReal C * eLpNorm v 2 volume := by
  obtain ⟨C, hC0, hC⟩ := sa12n_dual_ball hd
  have hs0 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsd : (d : ℝ) - 1 < d := by linarith
  refine ⟨2 * C, by positivity, fun i j l v hv hvc c' r' => ?_⟩
  have hv1 : ContDiff ℝ 2 (fun y : Euc d => y l * v y) :=
    (EuclideanSpace.proj l : Euc d →L[ℝ] ℝ).contDiff.mul hv
  have hv1c : HasCompactSupport (fun y : Euc d => y l * v y) := hvc.mul_left
  let Pq : Euc d → Euc d → ℝ := fun q x => x l * HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 1)) (qq q v) x -
    HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 1)) (qq q (fun y => y l * v y)) x
  have hPc : ∀ q, Continuous (Pq q) := fun q => by
    refine ((EuclideanSpace.proj l : Euc d →L[ℝ] ℝ).continuous.mul ?_).sub ?_
    · exact sa12n_convFun_continuous hs0 hsd (qq_contDiff hv) (qq_hasCompactSupport hvc)
    · exact sa12n_convFun_continuous hs0 hsd (qq_contDiff hv1) (qq_hasCompactSupport hv1c)
  have hQ : ∀ x, x l * hessRiesz d ((d : ℝ) - 1) i j v x -
      hessRiesz d ((d : ℝ) - 1) i j (fun y => y l * v y) x =
        (1 / 4 : ℝ) * (Pq (sa12z3_dp d i j) x - Pq (sa12z3_dm d i j) x) := by
    intro x
    rw [sa12x2_hess_polar hs0 hsd i j hv hvc x, sa12x2_hess_polar hs0 hsd i j hv1 hv1c x]
    simp only [Pq]; ring
  have hfun : (closedBall c' r').indicator (fun x => x l * hessRiesz d ((d : ℝ) - 1) i j v x -
          hessRiesz d ((d : ℝ) - 1) i j (fun y => y l * v y) x) =
      (1 / 4 : ℝ) • ((closedBall c' r').indicator (Pq (sa12z3_dp d i j)) -
        (closedBall c' r').indicator (Pq (sa12z3_dm d i j))) := by
    funext x
    by_cases hx : x ∈ closedBall c' r'
    · simp only [Set.indicator_of_mem hx, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      exact hQ x
    · simp [Set.indicator_of_notMem hx]
  rw [hfun, eLpNorm_const_smul]
  have h1 := hC (sa12z3_dp d i j) l v hv hvc c' r'
  have h2 := hC (sa12z3_dm d i j) l v hv hvc c' r'
  have h3 : eLpNorm ((closedBall c' r').indicator (Pq (sa12z3_dp d i j)) -
      (closedBall c' r').indicator (Pq (sa12z3_dm d i j))) 2 volume ≤
      eLpNorm ((closedBall c' r').indicator (Pq (sa12z3_dp d i j))) 2 volume +
        eLpNorm ((closedBall c' r').indicator (Pq (sa12z3_dm d i j))) 2 volume :=
    eLpNorm_sub_le (by norm_num)
  have h4 : eLpNorm ((closedBall c' r').indicator (Pq (sa12z3_dp d i j))) 2 volume ≤
      ENNReal.ofReal (4 * C) * eLpNorm v 2 volume :=
    h1.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith [mul_le_mul_of_nonneg_left (sa12x2_norm_dp_le i j) hC0])) le_rfl)
  have h5 : eLpNorm ((closedBall c' r').indicator (Pq (sa12z3_dm d i j))) 2 volume ≤
      ENNReal.ofReal (4 * C) * eLpNorm v 2 volume :=
    h2.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith [mul_le_mul_of_nonneg_left (sa12x2_norm_dm_le i j) hC0])) le_rfl)
  have hn : ‖(1 / 4 : ℝ)‖ₑ = ENNReal.ofReal (1 / 4) := by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_pos (by norm_num)]
  rw [hn]
  calc ENNReal.ofReal (1 / 4) * eLpNorm ((closedBall c' r').indicator (Pq (sa12z3_dp d i j)) -
        (closedBall c' r').indicator (Pq (sa12z3_dm d i j))) 2 volume
      ≤ ENNReal.ofReal (1 / 4) * (ENNReal.ofReal (4 * C) * eLpNorm v 2 volume +
          ENNReal.ofReal (4 * C) * eLpNorm v 2 volume) :=
        by gcongr; exact h3.trans (add_le_add h4 h5)
    _ = (ENNReal.ofReal (1 / 4) * (ENNReal.ofReal (4 * C) + ENNReal.ofReal (4 * C))) *
          eLpNorm v 2 volume := by ring
    _ = ENNReal.ofReal (2 * C) * eLpNorm v 2 volume := by
        congr 1
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring

end HRS.MH.AdjointRd.Phase2SA12Near
