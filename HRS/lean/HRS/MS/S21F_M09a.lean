import HRS.MS.R2InterpAux3
import HRS.MS.S21E_Wick
import HRS.MS.GenPathAux47
import HRS.MS.S21F_D00

/-!
# S21F, packet R26-T3.M09a: projective window tensors are determined by products of observations

Same route as `s102_J_unique` (S10.2): `P_L = ∑_p ℓ_p(·) b_p` gives `J(M∘(P_L,P_L)) = ∑ M(b_p,b_q) J(ℓ_p ⊗ ℓ_q)` (`s102_pair_expand`); the
evaluation functionals `ℓ_p` are the observations `s21eObs` of oscillator basis functions at grid nodes (`s56_isOscTest`), so the hypothesis
makes both finite sums agree, and `(P_L)^{⊗2}J → J` on `projTensor` (`s102_projection_strong`) identifies `J = K`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R26T3
open HRS HRS.Whole

theorem s21f_obs_eq_ellp {d : ℕ} {m T : ℝ} (hT : 0 < T) (L : ℕ) (q : ℕ × MultiIndex d) :
    s21eObs m T (HRS.MS.GenPath.s56_isOscTest m q.2).2 (HRS.MS.R2Interp.s102_node hT L q.1) =
      HRS.MS.R2Interp.s102_ellp hT L q := by
  ext w
  rw [s21eObs_apply, HRS.MS.R2Interp.s102_ellp_eval, r2PathAt,
    dif_pos (HRS.MS.R2Interp.s102_node hT L q.1).2]

theorem r26t3_tensor2_ext (p : Parameters) (J K : projTensor (Window p) 2)
    (h : ∀ u v : Set.Icc (0 : ℝ) p.T, ∀ f g : Euc p.d → ℝ,
      ∀ hf : IsOscTest (wholeSpaceIndex p.d) f,
      ∀ hg : IsOscTest (wholeSpaceIndex p.d) g,
      (J : TensorDual (Window p) 2) (HRS.MC.E213U18.mk2
        (s21eObs (wholeSpaceIndex p.d) p.T hf.2 u)
        (s21eObs (wholeSpaceIndex p.d) p.T hg.2 v)) =
      (K : TensorDual (Window p) 2) (HRS.MC.E213U18.mk2
        (s21eObs (wholeSpaceIndex p.d) p.T hf.2 u)
        (s21eObs (wholeSpaceIndex p.d) p.T hg.2 v))) : J = K := by
  classical
  apply Subtype.ext
  have hT := p.hT
  obtain ⟨_, _, hP3⟩ := HRS.MS.R2Interp.s102_projection_strong (d := p.d) (wholeSpaceIndex p.d : ℝ) p.T hT
  have hL : ∀ (L : ℕ) (M : Window p [×2]→L[ℝ] ℝ),
      (J : TensorDual (Window p) 2) (M.compContinuousLinearMap fun _ => HRS.MS.R2Interp.s102_Pj p.T hT L) =
        (K : TensorDual (Window p) 2) (M.compContinuousLinearMap fun _ => HRS.MS.R2Interp.s102_Pj p.T hT L) := by
    intro L M
    rw [HRS.MS.R2Interp.s102_pair_expand, HRS.MS.R2Interp.s102_pair_expand]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    congr 1
    have := h (HRS.MS.R2Interp.s102_node hT L (r 0).1) (HRS.MS.R2Interp.s102_node hT L (r 1).1)
      _ _ (HRS.MS.GenPath.s56_isOscTest _ (r 0).2) (HRS.MS.GenPath.s56_isOscTest _ (r 1).2)
    rw [s21f_obs_eq_ellp hT L (r 0), s21f_obs_eq_ellp hT L (r 1)] at this
    exact this
  refine ContinuousLinearMap.ext fun M => ?_
  have t1 := (ContinuousLinearMap.apply ℝ ℝ M).continuous.continuousAt.tendsto.comp (hP3 2 J.1 J.2)
  have t2 := (ContinuousLinearMap.apply ℝ ℝ M).continuous.continuousAt.tendsto.comp (hP3 2 K.1 K.2)
  have t2' : Tendsto ((ContinuousLinearMap.apply ℝ ℝ M) ∘
      fun L => HRS.Sec7.tensorPow 2 (HRS.MS.R2Interp.s102_Pj p.T hT L) J.1) atTop (𝓝 (K.1 M)) :=
    t2.congr (fun L => (hL L M).symm)
  exact tendsto_nhds_unique t1 t2'

end HRS.MS.R26T3
