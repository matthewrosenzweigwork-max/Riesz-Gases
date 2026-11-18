import HRS.MS.R2InterpAux52

/-!
# S10.2 (worker S102), part 53 (packet F6, regularity): continuity of the Gram integrals
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MC.Sec7.S7PIL

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ}

theorem s102_grad_contAt_x {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW C t φ f)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) t) (a : Fin d) : Continuous fun x => gradient (f r) x a := by
  have h := (hf.c2 r hr).continuous_fderiv (by norm_num)
  have : (fun x => gradient (f r) x a) = fun x => fderiv ℝ (f r) x (EuclideanSpace.single a (1 : ℝ)) := by
    funext x; exact s102_gradient_apply _ _ _
  rw [this]
  exact (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single a (1 : ℝ) : Euc d)).continuous.comp h

/-- The Gram integrals of the grid are continuous in the starting time on `[0, t_k ∧ t_{k'}]` (stationary integrable density). -/
theorem s102_gram_cont (hT : 0 < T) (L : ℕ)
    (hcls : ∀ (α : MultiIndex d) (t : ℝ), t ∈ Icc (0 : ℝ) T → ∃ f, IsClassicalAdjointW C t (oscTestFun m α) f)
    (ρ0 : Euc d → ℝ) (hρ0 : Integrable ρ0) (hstat : ∀ v, C.ρ v = ρ0) (k k' : Fin (s102_q d L)) :
    ContinuousOn (fun v => s102_gram C m hT L v k k') (Icc 0 (min (s102_tk hT L k) (s102_tk hT L k'))) := by
  have hk : s102_tk hT L k ∈ Icc (0 : ℝ) T := (s102_tauk hT L k).2
  have hk' : s102_tk hT L k' ∈ Icc (0 : ℝ) T := (s102_tauk hT L k').2
  have hF := s102_propagator_classical (hcls (s102_alk L k) _ hk)
  have hG := s102_propagator_classical (hcls (s102_alk L k') _ hk')
  obtain ⟨BF, hBF⟩ := s102_grad_bdd hF
  obtain ⟨BG, hBG⟩ := s102_grad_bdd hG
  set s : Set ℝ := Icc 0 (min (s102_tk hT L k) (s102_tk hT L k')) with hs
  have hsk : s ⊆ Icc 0 (s102_tk hT L k) := Icc_subset_Icc le_rfl (min_le_left _ _)
  have hsk' : s ⊆ Icc 0 (s102_tk hT L k') := Icc_subset_Icc le_rfl (min_le_right _ _)
  unfold s102_gram
  simp only [hstat]
  refine continuousOn_of_dominated (bound := fun x => (d : ℝ) * |BF| * |BG| * ‖ρ0 x‖) ?_ ?_ ?_ ?_
  · intro v hv
    refine AEStronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_) hρ0.aestronglyMeasurable
    simp_rw [s102_inner_eq_sum]
    exact continuous_finsetSum _ fun a _ =>
      (s102_grad_contAt_x hF (hsk hv) a).mul (s102_grad_contAt_x hG (hsk' hv) a)
  · intro v hv
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul, s102_inner_eq_sum, Real.norm_eq_abs]
    have h1 : |∑ a, gradient (propagatorW C v (s102_tk hT L k) (oscTestFun m (s102_alk L k))) x a *
        gradient (propagatorW C v (s102_tk hT L k') (oscTestFun m (s102_alk L k'))) x a| ≤
        (d : ℝ) * |BF| * |BG| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc _ ≤ ∑ _a : Fin d, |BF| * |BG| := Finset.sum_le_sum fun a _ => by
            rw [abs_mul]
            exact mul_le_mul ((hBF v (hsk hv) x a).trans (le_abs_self _))
              ((hBG v (hsk' hv) x a).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _)
        _ = _ := by simp [mul_assoc]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  · exact (hρ0.norm.const_mul _)
  · refine Filter.Eventually.of_forall fun x => ?_
    refine ContinuousOn.mul ?_ continuousOn_const
    simp_rw [s102_inner_eq_sum]
    exact continuousOn_finsetSum _ fun a _ =>
      ((s102_grad_contOn hF x a).mono hsk).mul ((s102_grad_contOn hG x a).mono hsk')

end HRS.MS.R2Interp

end
