import HRS.MS.Fp81S21LargeShift

open MeasureTheory Filter Topology Set ProbabilityTheory Function
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace HRS.Fp81.S21
open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3

theorem fp81s21_initial_Bterm_qwin_exp_envelope_uniform
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    (F : fp81s21_CompatPotentialFamily R)
    {C c : ℝ} (hC : 0 ≤ C)
    (hdecay : ∀ a : Set.Ici (0 : ℝ), ∀ j : ℕ,
      HasCbBound (fp81s21_k0 p.d)
        (C * Real.exp (-c * (a : ℝ)) * r26t3_feature_weight p.d j)
        (gradient ((F a).χ j)))
    (hφ : ∀ a : Set.Ici (0 : ℝ),
      IsSummableFeatureFamily (fp81s21_J1 p.d) (r26t3_qwin R (a : ℝ))) :
    ∃ KB : ℝ, 0 ≤ KB ∧ ∀ a : ℝ, ∀ ha : 0 ≤ a,
      ∀ N : ℕ, 2 ≤ N → ∀ j : ℕ, ∀ ψ : SeqL2 → ℝ, S99.Bd 4 ψ →
        |fp81s21_initial_Bterm R (r26t3_qwin R a) N
            (fun x y => commutatorKernel p.d p.s
              (gradient ((F ⟨a, ha⟩).χ j)) x y) ψ| ≤
          (KB * C) * Real.exp (-c * a) * r26t3_feature_weight p.d j := by
  obtain ⟨KB, hKB, hBq⟩ :=
    fp81s21_initial_Bq_bound hδ hδh E hγ
  refine ⟨KB, hKB, fun a ha N hN j ψ hψ => ?_⟩
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
  have htermInt := fp81s21_initial_Bterm_int hδ hδh R E hγ (hφ aI)
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


#print axioms fp81s21_initial_Bterm_qwin_exp_envelope_uniform
end HRS.Fp81.S21
end
