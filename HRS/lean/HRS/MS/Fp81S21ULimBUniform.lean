import HRS.MS.Fp81S21BkernelUniform4
import HRS.MS.Fp81S21InitialULim2

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45 S99
open HRS.Whole
open HRS (Euc MemCb cbNorm)
open HRS.MS.R26T3

/-- A common qwin coordinate envelope for the actual quadratic term, with
the response family fixed before the shift and particle number. -/
theorem fp81s21_initial_Bterm_qwin_envelope
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    (F : fp81s21_CompatPotentialFamily R)
    {K Cwin : ℝ} (hK : 0 ≤ K) (hCwin : 0 ≤ Cwin)
    (hFK : ∀ a : Set.Ici (0 : ℝ), (F a).K ≤ K)
    (hq : ∀ a : ℝ, 0 ≤ a →
      IsSummableFeatureFamily (fp81s21_J1 p.d) (r26t3_qwin R a) ∧
      ∀ j, cbNorm (fp81s21_J1 p.d) (r26t3_qwin R a j) ≤
        Cwin * r26t3_feature_weight p.d j) :
    ∃ KB : ℝ, 0 ≤ KB ∧
      ∀ N : ℕ, 2 ≤ N → ∀ a : ℝ, ∀ ha : 0 ≤ a, ∀ j : ℕ,
        ∀ ψ : SeqL2 → ℝ, S99.Bd 4 ψ →
          |fp81s21_initial_Bterm R (r26t3_qwin R a) N
              (fun x y => commutatorKernel p.d p.s
                (gradient ((F ⟨a, ha⟩).χ j)) x y) ψ| ≤
            (KB * (K * Cwin)) * r26t3_feature_weight p.d j := by
  obtain ⟨KB, hKB, hBq⟩ := fp81s21_initial_Bq_bound hδ hδh E hγ
  refine ⟨KB, hKB, fun N hN a ha j ψ hψ => ?_⟩
  let aI : Set.Ici (0 : ℝ) := ⟨a, ha⟩
  let φ : ℕ → Euc p.d → ℝ := r26t3_qwin R a
  let b : ℝ := cbNorm (fp81s21_J1 p.d) (φ j)
  let B2 : ℝ := (F aI).K * b
  have hJd : r26t3_J p.d = fp81s21_J1 p.d := rfl
  have hphi : IsSummableFeatureFamily (fp81s21_J1 p.d) φ := by
    simpa [φ] using (hq a ha).1
  have hb0 : 0 ≤ b := by
    dsimp [b]
    exact HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hb : b ≤ Cwin * r26t3_feature_weight p.d j := by
    dsimp [b, φ]
    simpa [hJd] using (hq a ha).2 j
  have hB20 : 0 ≤ B2 := mul_nonneg (F aI).hK hb0
  have hχ2 : ContDiff ℝ 2 ((F aI).χ j) := ((F aI).smooth j).of_le (by
    exact_mod_cast (show 2 ≤ fp81s21_k0 p.d + 1 by
      unfold fp81s21_k0
      omega))
  have hB2 : ∀ x, ‖fderiv ℝ (gradient ((F aI).χ j)) x‖ ≤ B2 := by
    intro x
    dsimp [B2, b, φ]
    exact (S45.s45_norm_fderiv_gradient hχ2 x).trans
      ((F aI).deriv j x 1 (by unfold fp81s21_k0; omega))
  have hv1 : ContDiff ℝ 1 (gradient ((F aI).χ j)) :=
    s45_contDiff_gradient hχ2
  have hvd : Differentiable ℝ (gradient ((F aI).χ j)) :=
    hv1.differentiable one_ne_zero
  let Λ : ℝ≥0 := ⟨B2, hB20⟩
  have hLip : LipschitzWith Λ (gradient ((F aI).χ j)) :=
    lipschitzWith_of_nnnorm_fderiv_le hvd (fun x => by
      have hx := hB2 x
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact hx)
  have hkernel : IsBoundedPairKernel p.s ((p.s + 1) * B2)
      (fun x y => commutatorKernel p.d p.s
        (gradient ((F aI).χ j)) x y) := by
    have hk := S99.s99_comm_isBounded (d := p.d) p.hs0 Λ hLip
    change IsBoundedPairKernel p.s ((p.s + 1) * (Λ : ℝ)) _ at hk
    rw [show (Λ : ℝ) = B2 from rfl] at hk
    exact hk
  obtain ⟨-, -, hBqInt, hBqL1⟩ :=
    hBq N hN (χ := (F aI).χ j) hχ2 hB2
  have htermInt := fp81s21_initial_Bterm_int hδ hδh R E hγ hphi
    hkernel hN hψ
  have hBqAbs := hBqInt.abs
  have hBqEq : ∀ X : EucConfig p.d N,
      fp81s21_initial_Bh R N
          (fun x y => commutatorKernel p.d p.s
            (gradient ((F aI).χ j)) x y) X =
        fp81s21_initialBq R ((F aI).χ j) N X := by
    intro X
    rfl
  have hB2le : B2 ≤ K * (Cwin * r26t3_feature_weight p.d j) := by
    dsimp [B2, b, φ]
    calc
      (F aI).K * cbNorm (fp81s21_J1 p.d) (r26t3_qwin R a j)
          ≤ K * cbNorm (fp81s21_J1 p.d) (r26t3_qwin R a j) :=
            mul_le_mul_of_nonneg_right (hFK aI) (HRS.MS.Tc5.tc5_cb_nonneg _ _)
      _ ≤ K * (Cwin * r26t3_feature_weight p.d j) :=
            mul_le_mul_of_nonneg_left hb hK
  unfold fp81s21_initial_Bterm
  rw [← Real.norm_eq_abs]
  calc
    ‖∫ X, fp81s21_initial_Bh R N
          (fun x y => commutatorKernel p.d p.s
            (gradient ((F aI).χ j)) x y) X *
        ψ (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N)‖ ≤
      ∫ X, ‖fp81s21_initial_Bh R N
          (fun x y => commutatorKernel p.d p.s
            (gradient ((F aI).χ j)) x y) X *
        ψ (featureVec φ (r26t3_marg R N) X)‖ ∂(r26t3_Q R N) :=
          norm_integral_le_integral_norm _
    _ ≤ ∫ X, |fp81s21_initialBq R ((F aI).χ j) N X|
          ∂(r26t3_Q R N) := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun X => norm_nonneg _)
        hBqAbs
        (Filter.Eventually.of_forall fun X => ?_)
      change ‖fp81s21_initial_Bh R N
          (fun x y => commutatorKernel p.d p.s
            (gradient ((F aI).χ j)) x y) X *
          ψ (featureVec φ (r26t3_marg R N) X)‖ ≤
        |fp81s21_initialBq R ((F aI).χ j) N X|
      rw [hBqEq X, Real.norm_eq_abs, abs_mul]
      calc
        |fp81s21_initialBq R ((F aI).χ j) N X| *
            |ψ (featureVec φ (r26t3_marg R N) X)| ≤
          |fp81s21_initialBq R ((F aI).χ j) N X| * 1 :=
            mul_le_mul_of_nonneg_left (hψ.abs_le _)
              (abs_nonneg _)
        _ = |fp81s21_initialBq R ((F aI).χ j) N X| := by ring
    _ ≤ KB * B2 := hBqL1
    _ ≤ KB * (K * (Cwin * r26t3_feature_weight p.d j)) :=
          mul_le_mul_of_nonneg_left hB2le hKB
    _ = (KB * (K * Cwin)) * r26t3_feature_weight p.d j := by ring

#print axioms fp81s21_initial_Bterm_qwin_envelope

end HRS.Fp81.S21

end
