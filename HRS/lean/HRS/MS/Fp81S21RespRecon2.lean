import HRS.MS.Fp81S21RespRecon
import HRS.MS.R2InterpAux3

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS.Whole HRS.MS.R26T3

/-- The cosine analysis coordinates determine a continuous window path. -/
theorem fp81s21_respRecon_obs_injective (p : Parameters) :
    Function.Injective (fp81s21_cosRecon_obs26 p) := by
  intro y z heq
  have hcont (w : Window p) (α : MultiIndex p.d) :
      ContinuousOn (fp81s21_cosRecon_coordExt w α) (Set.Icc (0 : ℝ) p.T) := by
    apply continuousOn_iff_continuous_restrict.mpr
    have hc := (HRS.MS.R2Interp.s102_coordCLM
      (m := (wholeSpaceIndex p.d : ℝ)) α).continuous.comp w.continuous
    have he : (Set.Icc (0 : ℝ) p.T).domRestrict (fp81s21_cosRecon_coordExt w α) =
        (fun t => OscDual.coord (OscPath.at' w t) α) := by
      funext t
      simp [Set.domRestrict, fp81s21_cosRecon_coordExt, t.2]
    rw [he]
    exact hc
  have hcoord (α : MultiIndex p.d) (n : ℕ) :
      ∫ t in Set.Icc (0 : ℝ) p.T, r2CosBasis p.T n t *
          fp81s21_cosRecon_coordExt y α t =
        ∫ t in Set.Icc (0 : ℝ) p.T, r2CosBasis p.T n t *
          fp81s21_cosRecon_coordExt z α t := by
    let j := (r26t3_feature_enum p.d).symm (n, α)
    have hh := congrFun heq j
    have hcos : ∀ t, r26t3_cosine p.T n t = r2CosBasis p.T n t := by
      intro t
      unfold r26t3_cosine r2CosBasis
      split_ifs <;> simp [one_div]
    simp only [fp81s21_cosRecon_obs26, j, Equiv.apply_symm_apply, hcos] at hh
    exact mul_left_cancel₀ (Real.rpow_pos_of_pos (by positivity) _).ne' hh
  apply ContinuousMap.ext
  intro t
  apply OscDual.ext_hermiteCoeff
  intro α
  have hu := (hcont y α).sub (hcont z α)
  have hi (w : Window p) (n : ℕ) :
      IntegrableOn (fun t => r2CosBasis p.T n t * fp81s21_cosRecon_coordExt w α t)
        (Set.Icc (0 : ℝ) p.T) :=
    ((HRS.MS.R2WinOrb.s103_cosBasis_continuous p.T n).continuousOn.mul (hcont w α)).integrableOn_Icc
  have hz : ∀ n : ℕ, ∫ t in Set.Icc (0 : ℝ) p.T,
      r2CosBasis p.T n t * (fp81s21_cosRecon_coordExt y α t -
        fp81s21_cosRecon_coordExt z α t) = 0 := by
    intro n
    simp_rw [mul_sub]
    rw [integral_sub (hi y n) (hi z n), hcoord α n, sub_self]
  have hp := HRS.Whole.s11p_cos_unique p.hT _ hu hz t t.2
  have hpoint : OscDual.coord (OscPath.at' y t) α =
      OscDual.coord (OscPath.at' z t) α := by
    simpa [fp81s21_cosRecon_coordExt, t.2, sub_eq_zero] using hp
  change oscEigenvalue p.d α ^ ((wholeSpaceIndex p.d : ℝ) / 2) *
      OscDual.coord (OscPath.at' y t) α = _
  rw [hpoint]
  rfl

#print axioms fp81s21_respRecon_obs_injective

end HRS.Fp81.S21
end
