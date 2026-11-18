import HRS.MS.Fp81S21InitialULim
import HRS.MS.Fp81S21InitialBkernel2

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

/-! The quadratic-series limit uses the actual-law centered-commutator moment
envelope and the qualitative actual-law singular-kernel limit. -/

/-- Uniform convergence of the actual-initial-law quadratic coefficient series. -/
theorem fp81s21_initial_ULimB
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ)
    {G : Measure SeqL2} [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianSeq G (fun i j =>
      HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel p.d p.s)
        (r26t3_mu R 0) p.γ (φ i) (φ j))) :
    ULim
      (fun N f => if 2 ≤ N then ∑' j,
        fp81s21_initial_Bterm R φ N
          (commutatorKernel p.d p.s (gradient (F.χ j))) (S99.pd f j) else 0)
      (fun f => ∑' j, (1 / 2) * ∑' l, ∑' q,
        fp81s21_initial_Qk R φ
          (commutatorKernel p.d p.s (gradient (F.χ j))) l q *
          ∫ z, S99.pd (S99.pd (S99.pd f j) l) q z ∂G) := by
  obtain ⟨KB, hKB0, hBq⟩ := fp81s21_initial_Bq_bound hδ hδh E hγ
  let b : ℕ → ℝ := fun j => cbNorm (fp81s21_J1 p.d) (φ j)
  have hb0 : ∀ j, 0 ≤ b j := fun j => by
    dsimp [b]
    exact HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbs : Summable b := hφ.2
  have hFK0 : 0 ≤ F.K := F.hK
  let M : ℕ → ℝ := fun j => KB * (F.K * b j)
  have hMs : Summable M := (hbs.mul_left F.K).mul_left KB
  have hM0 : ∀ j, 0 ≤ M j := fun j =>
    mul_nonneg hKB0 (mul_nonneg hFK0 (hb0 j))
  have hBt : ∀ N : ℕ, 2 ≤ N → ∀ j : ℕ, ∀ ψ : SeqL2 → ℝ,
      Bd 4 ψ →
      |fp81s21_initial_Bterm R φ N
          (commutatorKernel p.d p.s (gradient (F.χ j))) ψ| ≤ M j := by
    intro N hN j ψ hψ
    have hχ2 : ContDiff ℝ 2 (F.χ j) := (F.smooth j).of_le (by
      exact_mod_cast (show 2 ≤ fp81s21_k0 p.d + 1 by
        unfold fp81s21_k0
        omega))
    let B2 : ℝ := F.K * b j
    have hB20 : 0 ≤ B2 := mul_nonneg hFK0 (hb0 j)
    have hB2 : ∀ x, ‖fderiv ℝ (gradient (F.χ j)) x‖ ≤ B2 := by
      intro x
      dsimp [B2]
      exact (S45.s45_norm_fderiv_gradient hχ2 x).trans (F.deriv j x 1 (by
        unfold fp81s21_k0
        omega))
    obtain ⟨-, -, hBqInt, hBqL1⟩ := hBq N hN (χ := F.χ j) hχ2
      (B2 := B2) hB2
    have hkernel : IsBoundedPairKernel p.s ((p.s + 1) * B2)
        (commutatorKernel p.d p.s (gradient (F.χ j))) := by
      have hv1 : ContDiff ℝ 1 (gradient (F.χ j)) := s45_contDiff_gradient hχ2
      have hvd : Differentiable ℝ (gradient (F.χ j)) :=
        hv1.differentiable one_ne_zero
      let Λ : ℝ≥0 := ⟨B2, hB20⟩
      have hLip : LipschitzWith Λ (gradient (F.χ j)) :=
        lipschitzWith_of_nnnorm_fderiv_le hvd (fun x => by
          have hx := hB2 x
          rw [← NNReal.coe_le_coe, coe_nnnorm]
          exact hx)
      have hk := S99.s99_comm_isBounded (d := p.d) p.hs0 Λ hLip
      change IsBoundedPairKernel p.s ((p.s + 1) * (Λ : ℝ)) _ at hk
      rw [show (Λ : ℝ) = B2 from rfl] at hk
      exact hk
    have htermInt := fp81s21_initial_Bterm_int hδ hδh R E hγ hφ
      hkernel hN hψ
    have hBqabs : Integrable (fun X : EucConfig p.d N =>
        |fp81s21_initialBq R (F.χ j) N X|) (r26t3_Q R N) := hBqInt.abs
    have hBqEq : ∀ X : EucConfig p.d N,
        fp81s21_initial_Bh R N
            (commutatorKernel p.d p.s (gradient (F.χ j))) X =
          fp81s21_initialBq R (F.χ j) N X := by
      intro X
      rfl
    unfold fp81s21_initial_Bterm
    rw [← Real.norm_eq_abs]
    calc
      ‖∫ X, fp81s21_initial_Bh R N
            (commutatorKernel p.d p.s (gradient (F.χ j))) X *
          ψ (featureVec φ (r26t3_marg R N) X) ∂(r26t3_Q R N)‖ ≤
        ∫ X, ‖fp81s21_initial_Bh R N
            (commutatorKernel p.d p.s (gradient (F.χ j))) X *
          ψ (featureVec φ (r26t3_marg R N) X)‖ ∂(r26t3_Q R N) :=
            norm_integral_le_integral_norm _
      _ ≤ ∫ X, |fp81s21_initialBq R (F.χ j) N X| ∂(r26t3_Q R N) := by
        apply integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun X => norm_nonneg _)
          hBqabs
          (Filter.Eventually.of_forall fun X => ?_)
        change ‖fp81s21_initial_Bh R N
            (commutatorKernel p.d p.s (gradient (F.χ j))) X *
          ψ (featureVec φ (r26t3_marg R N) X)‖ ≤
            |fp81s21_initialBq R (F.χ j) N X|
        rw [hBqEq X, Real.norm_eq_abs, abs_mul]
        calc
          |fp81s21_initialBq R (F.χ j) N X| *
              |ψ (featureVec φ (r26t3_marg R N) X)| ≤
            |fp81s21_initialBq R (F.χ j) N X| * 1 :=
              mul_le_mul_of_nonneg_left (hψ.abs_le _) (abs_nonneg _)
          _ = |fp81s21_initialBq R (F.χ j) N X| := by ring
      _ ≤ KB * B2 := hBqL1
      _ = M j := by dsimp [M, B2]
  have hlimj : ∀ j, ULim
      (fun N f => if 2 ≤ N then fp81s21_initial_Bterm R φ N
          (commutatorKernel p.d p.s (gradient (F.χ j))) (S99.pd f j) else 0)
      (fun f => (1 / 2) * ∑' l, ∑' q,
        fp81s21_initial_Qk R φ
          (commutatorKernel p.d p.s (gradient (F.χ j))) l q *
          ∫ z, S99.pd (S99.pd (S99.pd f j) l) q z ∂G) := by
    intro j ε hε
    have hχ2 : ContDiff ℝ 2 (F.χ j) := (F.smooth j).of_le (by
      exact_mod_cast (show 2 ≤ fp81s21_k0 p.d + 1 by
        unfold fp81s21_k0
        omega))
    have hB2 : ∀ x, ‖fderiv ℝ (gradient (F.χ j)) x‖ ≤ F.K * b j := by
      intro x
      exact (S45.s45_norm_fderiv_gradient hχ2 x).trans (F.deriv j x 1 (by
        unfold fp81s21_k0
        omega))
    have hB20 : 0 ≤ F.K * b j := mul_nonneg hFK0 (hb0 j)
    have hv1 : ContDiff ℝ 1 (gradient (F.χ j)) := s45_contDiff_gradient hχ2
    have hvd : Differentiable ℝ (gradient (F.χ j)) :=
      hv1.differentiable one_ne_zero
    let Λ : ℝ≥0 := ⟨F.K * b j, hB20⟩
    have hLip : LipschitzWith Λ (gradient (F.χ j)) :=
      lipschitzWith_of_nnnorm_fderiv_le hvd (fun x => by
        have hx := hB2 x
        rw [← NNReal.coe_le_coe, coe_nnnorm]
        exact hx)
    have hkernel : IsBoundedPairKernel p.s ((p.s + 1) * (F.K * b j))
        (commutatorKernel p.d p.s (gradient (F.χ j))) := by
      have hk := S99.s99_comm_isBounded (d := p.d) p.hs0 Λ hLip
      change IsBoundedPairKernel p.s ((p.s + 1) * (Λ : ℝ)) _ at hk
      rw [show (Λ : ℝ) = F.K * b j from rfl] at hk
      exact hk
    have hBk := fp81s21_initial_Bkernel hδ hδh R E hγ hφ F hG hkernel
    obtain ⟨N0, hN0⟩ := hBk ε hε
    refine ⟨max N0 2, fun N hN f hf => ?_⟩
    have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
    have hN0' : N0 ≤ N := (le_max_left _ _).trans hN
    simp only [hN2, ite_true]
    exact hN0 N hN0' hN2 (ψ := S99.pd f j) (S99.SteinCl.pd hf j)
  have hu : ∀ j N f, SteinCl f →
      |(if 2 ≤ N then fp81s21_initial_Bterm R φ N
          (commutatorKernel p.d p.s (gradient (F.χ j))) (S99.pd f j) else 0)| ≤ M j := by
    intro j N f hf
    by_cases hN : 2 ≤ N
    · simp only [hN, ite_true]
      exact hBt N hN j (S99.pd f j) (S99.SteinCl.pd hf j)
    · simp only [hN, ite_false, abs_zero]
      exact hM0 j
  have hL : ∀ j f, SteinCl f →
      |(1 / 2) * ∑' l, ∑' q,
        fp81s21_initial_Qk R φ
          (commutatorKernel p.d p.s (gradient (F.χ j))) l q *
          ∫ z, S99.pd (S99.pd (S99.pd f j) l) q z ∂G| ≤ M j := by
    intro j f hf
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨N0, hN0⟩ := hlimj j ε hε
    have hN := hN0 (max N0 2) (le_max_left _ _) f hf
    have hN2 : 2 ≤ max N0 2 := le_max_right _ _
    simp only [hN2, ite_true] at hN
    have hB := hBt (max N0 2) hN2 j (S99.pd f j) (S99.SteinCl.pd hf j)
    have hAbs :
        |(1 / 2) * ∑' l, ∑' q,
          fp81s21_initial_Qk R φ
            (commutatorKernel p.d p.s (gradient (F.χ j))) l q *
            ∫ z, S99.pd (S99.pd (S99.pd f j) l) q z ∂G| ≤
          |fp81s21_initial_Bterm R φ (max N0 2)
              (commutatorKernel p.d p.s (gradient (F.χ j))) (S99.pd f j)| + ε := by
      have hh := abs_sub_abs_le_abs_sub
        ((1 / 2) * ∑' l, ∑' q,
          fp81s21_initial_Qk R φ
            (commutatorKernel p.d p.s (gradient (F.χ j))) l q *
            ∫ z, S99.pd (S99.pd (S99.pd f j) l) q z ∂G)
        (fp81s21_initial_Bterm R φ (max N0 2)
          (commutatorKernel p.d p.s (gradient (F.χ j))) (S99.pd f j))
      rw [abs_sub_comm] at hh
      linarith
    have hMj : 0 ≤ M j := hM0 j
    linarith [hAbs, hB]
  have hmain := S99.s99_ULim_tsum hMs hu hL hlimj
  refine S99.ULim.congr (fun N f hf => ?_) hmain
  by_cases hN : 2 ≤ N
  · simp only [hN, ite_true]
  · simp [hN]

#print axioms fp81s21_initial_ULimB

end HRS.Fp81.S21

end
