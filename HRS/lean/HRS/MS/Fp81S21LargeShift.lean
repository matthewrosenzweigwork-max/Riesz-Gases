import HRS.MS.Fp81S21ShiftKernel2
import HRS.MS.Fp81S21InitialBkernel
import HRS.MS.Fp81S21InitialBkernel2

open MeasureTheory Filter Topology Set ProbabilityTheory Function
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3

/-- Retain the exponential factor in the compatible corrector bound when passing to
its `C_b^2` velocity norm. -/
theorem fp81s21_compat_gradient_velocityBall_exp_decay
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (F : fp81s21_CompatPotentialFamily R)
    {C c : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ a : Set.Ici (0 : ℝ), ∀ j : ℕ,
      HasCbBound (fp81s21_k0 p.d)
        (C * Real.exp (-c * (a : ℝ)) * r26t3_feature_weight p.d j)
        (gradient ((F a).χ j)))
    (a : Set.Ici (0 : ℝ)) (j : ℕ) :
    HRS.Whole.IsR2VelocityBall p.d
      (3 * (C * Real.exp (-c * (a : ℝ)) * r26t3_feature_weight p.d j))
      (gradient ((F a).χ j)) := by
  let v : Euc p.d → Euc p.d := gradient ((F a).χ j)
  let B : ℝ := C * Real.exp (-c * (a : ℝ)) * r26t3_feature_weight p.d j
  have hweight : 0 ≤ r26t3_feature_weight p.d j := by
    dsimp [r26t3_feature_weight]
    apply mul_nonneg
    · apply Real.rpow_nonneg
      positivity
    · exact Real.rpow_nonneg (oscEigenvalue_pos _).le _
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg hC (Real.exp_pos _).le) hweight
  have hk2 : 2 ≤ fp81s21_k0 p.d := by
    unfold fp81s21_k0
    omega
  have hcb := hdecay a j
  have hcont : ContDiff ℝ 2 v := by
    dsimp [v]
    exact hcb.1.of_le (by exact_mod_cast hk2)
  have hderiv : ∀ i : ℕ, i ≤ 2 → ∀ x : Euc p.d,
      ‖iteratedFDeriv ℝ i v x‖ ≤ B := by
    intro i hi x
    dsimp [v, B]
    exact hcb.2 i (hi.trans hk2) x
  have hnorm : cbNormVecE 2 v ≤ ENNReal.ofReal (3 * B) := by
    simpa [B, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using
      (HRS.MS.MovAdj.s67_cb_le (j := 2) (v := v) (Y := fun _ => B) hderiv)
  exact ⟨hcont, by simpa [B] using hnorm⟩

/-- The commutator kernel of a compatible corrector has an exponentially decaying
singular-kernel envelope, uniformly in the nonnegative shift. -/
theorem fp81s21_compat_commutatorKernel_exp_decay
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (F : fp81s21_CompatPotentialFamily R)
    {C c : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ a : Set.Ici (0 : ℝ), ∀ j : ℕ,
      HasCbBound (fp81s21_k0 p.d)
        (C * Real.exp (-c * (a : ℝ)) * r26t3_feature_weight p.d j)
        (gradient ((F a).χ j)))
    (a : Set.Ici (0 : ℝ)) (j : ℕ) :
    IsBoundedPairKernel p.s
      ((p.s + 1) * (3 * (C * Real.exp (-c * (a : ℝ)) *
        r26t3_feature_weight p.d j)))
      (commutatorKernel p.d p.s (gradient ((F a).χ j))) := by
  let Λ : ℝ := 3 * (C * Real.exp (-c * (a : ℝ)) * r26t3_feature_weight p.d j)
  have hweight : 0 ≤ r26t3_feature_weight p.d j := by
    dsimp [r26t3_feature_weight]
    apply mul_nonneg
    · apply Real.rpow_nonneg
      positivity
    · exact Real.rpow_nonneg (oscEigenvalue_pos _).le _
  have hΛ : 0 ≤ Λ := by
    dsimp [Λ]
    positivity
  let v : HRS.MS.R2S11.s11V p.d Λ :=
    ⟨gradient ((F a).χ j),
      fp81s21_compat_gradient_velocityBall_exp_decay R F hC hdecay a j⟩
  have hLip : LipschitzWith (Real.toNNReal Λ) v.1 := by
    simpa [max_eq_left hΛ] using HRS.MS.R2S11.s11_V_lip v
  have hkernel := S99.s99_comm_isBounded p.hs0 (Real.toNNReal Λ) hLip
  have hcoerce : (Real.toNNReal Λ : ℝ) = Λ := Real.coe_toNNReal Λ hΛ
  have hkernel' : IsBoundedPairKernel p.s ((p.s + 1) * Λ)
      (commutatorKernel p.d p.s (gradient ((F a).χ j))) := by
    simpa only [hcoerce, v] using hkernel
  simpa only [Λ] using hkernel'

/-- Each bounded quadratic D1 test term inherits the exponential shift decay of
its compatible commutator kernel. -/
theorem fp81s21_initial_Bterm_qwin_exp_envelope
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    (F : fp81s21_CompatPotentialFamily R)
    {C c : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ a : Set.Ici (0 : ℝ), ∀ j : ℕ,
      HasCbBound (fp81s21_k0 p.d)
        (C * Real.exp (-c * (a : ℝ)) * r26t3_feature_weight p.d j)
        (gradient ((F a).χ j)))
    (a : ℝ) (ha : 0 ≤ a)
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) (r26t3_qwin R a)) :
    ∃ KB : ℝ, 0 ≤ KB ∧
      ∀ N : ℕ, 2 ≤ N → ∀ j : ℕ, ∀ ψ : SeqL2 → ℝ, S99.Bd 4 ψ →
        |fp81s21_initial_Bterm R (r26t3_qwin R a) N
            (fun x y => commutatorKernel p.d p.s
              (gradient ((F ⟨a, ha⟩).χ j)) x y) ψ| ≤
          (KB * C) * Real.exp (-c * a) * r26t3_feature_weight p.d j := by
  obtain ⟨KB, hKB, hBq⟩ :=
    fp81s21_initial_Bq_bound hδ hδh E hγ
  refine ⟨KB, hKB, fun N hN j ψ hψ => ?_⟩
  let aI : Set.Ici (0 : ℝ) := ⟨a, ha⟩
  let χ : Euc p.d → ℝ := (F aI).χ j
  let A : ℝ := C * Real.exp (-c * a) * r26t3_feature_weight p.d j
  have hA : 0 ≤ A := by
    dsimp [A]
    apply mul_nonneg
    · exact mul_nonneg hC (Real.exp_pos _).le
    · dsimp [r26t3_feature_weight]
      apply mul_nonneg
      · apply Real.rpow_nonneg
        positivity
      · exact Real.rpow_nonneg (oscEigenvalue_pos _).le _
  have hk2 : 2 ≤ fp81s21_k0 p.d := by
    unfold fp81s21_k0
    omega
  have hχ2 : ContDiff ℝ 2 χ := by
    dsimp [χ]
    exact ((F aI).smooth j).of_le (by
      exact_mod_cast (show 2 ≤ fp81s21_k0 p.d + 1 by
        unfold fp81s21_k0
        omega))
  have hB2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ A := by
    intro x
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]
    simpa [χ, A, aI] using
      (hdecay aI j).2 1 (by unfold fp81s21_k0; omega) x
  obtain ⟨-, -, hBqInt, hBqL1⟩ := hBq N hN hχ2 hB2
  have hkernel := fp81s21_compat_commutatorKernel_exp_decay
    R F hC hdecay aI j
  have htermInt := fp81s21_initial_Bterm_int hδ hδh R E hγ hφ
    hkernel hN hψ
  have hBqAbs := hBqInt.abs
  have hBqEq : ∀ X : EucConfig p.d N,
      fp81s21_initial_Bh R N
          (fun x y => commutatorKernel p.d p.s
            (gradient ((F aI).χ j)) x y) X =
        fp81s21_initialBq R χ N X := by
    intro X
    rfl
  unfold fp81s21_initial_Bterm
  rw [← Real.norm_eq_abs]
  calc
    ‖∫ X, fp81s21_initial_Bh R N
          (fun x y => commutatorKernel p.d p.s
            (gradient ((F aI).χ j)) x y) X *
        ψ (featureVec (r26t3_qwin R a) (r26t3_marg R N) X)
        ∂(r26t3_Q R N)‖ ≤
      ∫ X, ‖fp81s21_initial_Bh R N
          (fun x y => commutatorKernel p.d p.s
            (gradient ((F aI).χ j)) x y) X *
        ψ (featureVec (r26t3_qwin R a) (r26t3_marg R N) X)‖
        ∂(r26t3_Q R N) := norm_integral_le_integral_norm _
    _ ≤ ∫ X, |fp81s21_initialBq R χ N X| ∂(r26t3_Q R N) := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun X => norm_nonneg _)
        hBqAbs
        (Filter.Eventually.of_forall fun X => ?_)
      change ‖fp81s21_initial_Bh R N
          (fun x y => commutatorKernel p.d p.s
            (gradient ((F aI).χ j)) x y) X *
          ψ (featureVec (r26t3_qwin R a) (r26t3_marg R N) X)‖ ≤
        |fp81s21_initialBq R χ N X|
      rw [hBqEq X, Real.norm_eq_abs, abs_mul]
      calc
        |fp81s21_initialBq R χ N X| *
            |ψ (featureVec (r26t3_qwin R a) (r26t3_marg R N) X)| ≤
          |fp81s21_initialBq R χ N X| * 1 :=
            mul_le_mul_of_nonneg_left (hψ.abs_le _)
              (abs_nonneg _)
        _ = |fp81s21_initialBq R χ N X| := by ring
    _ ≤ KB * A := hBqL1
    _ = (KB * C) * Real.exp (-c * a) *
        r26t3_feature_weight p.d j := by
      dsimp [A]
      ring

#print axioms fp81s21_compat_gradient_velocityBall_exp_decay
#print axioms fp81s21_compat_commutatorKernel_exp_decay
#print axioms fp81s21_initial_Bterm_qwin_exp_envelope

end HRS.Fp81.S21

end
