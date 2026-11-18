import HRS.MS.Fp81S21BlockValue4
import HRS.MS.R2InterpAux3

/-! Uniqueness of the window covariance specification. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.Sec7 HRS.MS.R2Interp

/-- The observation products determine a projective window covariance tensor. -/
theorem fp81s21_window_J_unique {d : ℕ} {m T a : ℝ}
    (C : WholeCoeff d) (hT : 0 < T)
    (z : ℝ → (Euc d → ℝ) → ℝ) (I : Set ℝ)
    {J J' : TensorDual (OscPath d m T) 2}
    (hJ : fp81s21_IsWindowJValue C m T a z I J)
    (hJ' : fp81s21_IsWindowJValue C m T a z I J') : J = J' := by
  classical
  obtain ⟨_, _, hP3⟩ := s102_projection_strong (d := d) m T hT
  have hL : ∀ (L : ℕ) (M : OscPath d m T [×2]→L[ℝ] ℝ),
      J (M.compContinuousLinearMap fun _ => s102_Pj T hT L) =
        J' (M.compContinuousLinearMap fun _ => s102_Pj T hT L) := by
    intro L M
    rw [s102_pair_expand, s102_pair_expand]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    congr 1
    have key : ∀ K : TensorDual (OscPath d m T) 2,
        fp81s21_IsWindowJValue C m T a z I K →
        K ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
            ![s102_ellp hT L (r 0), s102_ellp hT L (r 1)]) =
          2 * C.ν * ∫ u in I ∩ Icc (0 : ℝ)
              (min (a + ((s102_node hT L (r 0).1 : Icc (0 : ℝ) T) : ℝ))
                (a + ((s102_node hT L (r 1).1 : Icc (0 : ℝ) T) : ℝ))),
            z u (fun x => inner ℝ
              (gradient (propagatorW C u (a + ((s102_node hT L (r 0).1 : Icc (0 : ℝ) T) : ℝ))
                (oscTestFun m (r 0).2)) x)
              (gradient (propagatorW C u (a + ((s102_node hT L (r 1).1 : Icc (0 : ℝ) T) : ℝ))
                (oscTestFun m (r 1).2)) x)) := by
      intro K hK
      exact hK.2 _ _ _ _ _ _ (s102_isDualCombo _) (s102_isDualCombo _)
        (s102_node hT L (r 0).1).2 (s102_node hT L (r 1).1).2
        (s102_ellp_eval hT L (r 0)) (s102_ellp_eval hT L (r 1))
    rw [key J hJ, key J' hJ']
  refine ContinuousLinearMap.ext fun M => ?_
  have t1 := (ContinuousLinearMap.apply ℝ ℝ M).continuous.continuousAt.tendsto.comp (hP3 2 J hJ.1)
  have t2 := (ContinuousLinearMap.apply ℝ ℝ M).continuous.continuousAt.tendsto.comp (hP3 2 J' hJ'.1)
  have e : ∀ L, ((ContinuousLinearMap.apply ℝ ℝ M) ∘ fun L => tensorPow 2 (s102_Pj T hT L) J) L =
      ((ContinuousLinearMap.apply ℝ ℝ M) ∘ fun L => tensorPow 2 (s102_Pj T hT L) J') L := by
    intro L
    exact hL L M
  have t2' : Tendsto ((ContinuousLinearMap.apply ℝ ℝ M) ∘ fun L => tensorPow 2 (s102_Pj T hT L) J)
      atTop (𝓝 (J' M)) := by
    refine t2.congr (fun L => (e L).symm)
  exact tendsto_nhds_unique t1 t2'

end HRS.Fp81.S21
end
#print axioms HRS.Fp81.S21.fp81s21_window_J_unique
