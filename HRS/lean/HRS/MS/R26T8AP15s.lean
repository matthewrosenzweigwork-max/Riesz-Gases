import HRS.MS.R26T8AP15r
import HRS.MS.R26T8AF07a
import HRS.MS.R26T8AF01b
import HRS.MS.R26T8AP11g6

/-!
# S8.2 T8A P15s: the drift coordinates `α_i(x) = -forceMean_i(x) - a x_i`
`‖D^j α_i(x)‖ ≤ B jb(x)` for `j ≤ k`, `α_i ∈ C^k`; and `(critCoeff d a beta rho).drift 0 x i = α_i(x)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_drift_coord_eq (a beta : ℝ) (rho : Euc d → ℝ) (i : Fin d) (x : Euc d) :
    (critCoeff d a beta rho).drift 0 x i = -(forceMean rho x i) - a * x i := by
  rw [r26t8a_f07a_drift]
  simp [sub_eq_add_neg]

theorem r26t8a_critCoeff_nu (a beta : ℝ) (rho : Euc d → ℝ) : (critCoeff d a beta rho).ν = beta⁻¹ := by
  simp [critCoeff, quadraticGradientDyn, WholeDyn.coeff]

set_option maxHeartbeats 1600000 in
theorem r26t8a_drift_coord (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i : Fin d,
      ContDiff ℝ (k : WithTop ℕ∞) (fun x => -(forceMean rho x i) - a * x i) ∧
      ∀ j ≤ k, ∀ x : Euc d, ‖iteratedFDeriv ℝ j (fun x => -(forceMean rho x i) - a * x i) x‖ ≤ B * jbracket x := by
  obtain ⟨hFs, hFb⟩ := r26t8a_thermal_force d hd a beta ha hbeta rho hrho
  obtain ⟨CF, hCF0, hCF⟩ := r26t8a_g6_force_unif (F := forceMean rho) (fun l => by
    obtain ⟨C, hC0, hC⟩ := hFb l
    exact ⟨C, hC0, fun x => (le_add_of_nonneg_right (norm_nonneg _)).trans (hC x)⟩) k
  refine ⟨CF + |a|, by positivity, fun i => ?_⟩
  set pr : Euc d →L[ℝ] ℝ := EuclideanSpace.proj i with hpr
  have hprn : ‖pr‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    show ‖v i‖ ≤ 1 * ‖v‖
    rw [one_mul, Real.norm_eq_abs]; exact r26t8a_abs_coord_le v i
  set L : Euc d →L[ℝ] ℝ := a • pr with hL
  have hLn : ‖L‖ ≤ |a| := by
    rw [hL]
    calc ‖a • pr‖ ≤ ‖a‖ * ‖pr‖ := ContinuousLinearMap.opNorm_smul_le a pr
      _ ≤ |a| * 1 := by rw [Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left hprn (abs_nonneg _)
      _ = |a| := mul_one _
  have hFk : ContDiff ℝ (k : WithTop ℕ∞) (forceMean rho) := hFs.of_le (by exact_mod_cast le_top)
  have hu : ContDiff ℝ (k : WithTop ℕ∞) (fun x => forceMean rho x i) := pr.contDiff.comp hFk
  have hv : ContDiff ℝ (k : WithTop ℕ∞) (fun x : Euc d => a * x i) := by
    have : (fun x : Euc d => a * x i) = ⇑L := by funext x; simp [hL, hpr]
    rw [this]; exact L.contDiff
  have e : (fun x => -(forceMean rho x i) - a * x i) = (fun x => -(forceMean rho x i)) - fun x : Euc d => a * x i := rfl
  refine ⟨by rw [e]; exact hu.neg.sub hv, fun j hj x => ?_⟩
  have hjb := r26t8a_one_le_jb x
  have hneg : ContDiff ℝ (k : WithTop ℕ∞) (fun x => -(forceMean rho x i)) := hu.neg
  rw [e, iteratedFDeriv_sub_apply (hneg.contDiffAt.of_le (by exact_mod_cast hj)) (hv.contDiffAt.of_le (by exact_mod_cast hj))]
  refine (norm_sub_le _ _).trans ?_
  have h1 : ‖iteratedFDeriv ℝ j (fun x => -(forceMean rho x i)) x‖ ≤ CF := by
    have := iteratedFDeriv_neg_apply (𝕜 := ℝ) (f := fun x => forceMean rho x i) (i := j) (x := x)
    rw [show (fun x => -(forceMean rho x i)) = -(fun x => forceMean rho x i) from rfl, this, norm_neg]
    have h1 := pr.norm_iteratedFDeriv_comp_left (f := forceMean rho) (x := x) (N := (k : WithTop ℕ∞)) (n := j)
      (hFk.contDiffAt) (by exact_mod_cast hj)
    calc _ ≤ ‖pr‖ * ‖iteratedFDeriv ℝ j (forceMean rho) x‖ := h1
      _ ≤ 1 * CF := mul_le_mul hprn (hCF j hj x) (norm_nonneg _) zero_le_one
      _ = CF := one_mul _
  have h2 : ‖iteratedFDeriv ℝ j (fun x : Euc d => a * x i) x‖ ≤ |a| * jbracket x := by
    have hLf : (fun x : Euc d => a * x i) = ⇑L := by funext x; simp [hL, hpr]
    rw [hLf]
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [norm_iteratedFDeriv_zero]
      calc ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
        _ ≤ |a| * jbracket x := by
          have : ‖x‖ ≤ jbracket x := by
            unfold jbracket
            exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖x‖])
          exact mul_le_mul hLn this (norm_nonneg _) (abs_nonneg _)
    · obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
      have hfd : fderiv ℝ (⇑L) = fun _ => L := funext fun x => L.fderiv
      rw [← norm_iteratedFDeriv_fderiv, hfd]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [norm_iteratedFDeriv_zero]
        calc ‖L‖ ≤ |a| := hLn
          _ = |a| * 1 := (mul_one _).symm
          _ ≤ |a| * jbracket x := mul_le_mul_of_nonneg_left hjb (abs_nonneg _)
      · rw [iteratedFDeriv_const_of_ne hn.ne']
        simp; positivity
  calc _ ≤ CF + |a| * jbracket x := add_le_add h1 h2
    _ ≤ (CF + |a|) * jbracket x := by nlinarith

end HRS.MS.R26T8A
