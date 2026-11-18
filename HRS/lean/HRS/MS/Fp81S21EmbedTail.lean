import HRS.MS.Fp81S21EmbedMom3

/-! Quantitative projection tails for embedded coefficient fields. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- A single chart-dependent profile controls the projection tails of every
strong-chart moment representative after embedding. The same estimate gives
a fixed-time almost-everywhere pointwise bound by the strong representative's
coefficient norm. -/
theorem fp81s21_embedField_projectionTail
    {d q : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw)
    (hPs : (d : ℝ) < 2 * (Pw + 2))
    (Es : r26t6_WeightedChart d q (Pw + 2))
    (E : r26t6_WeightedChart d (q + 2) Pw) :
    ∃ ε : ℕ → ℝ,
      (∀ m, 0 ≤ ε m) ∧
      Tendsto ε atTop (𝓝 0) ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω]
        (P : Measure Ω)
        (Q : ℝ → Ω → (Euc d → ℝ) → ℝ)
        (qs : ℝ → Ω → r26t6_Coeff) (M : ℝ),
        fp81s21_MomentRep Es P Q qs M →
        ∀ m u, 0 ≤ u →
          Integrable
            (fun ω => ‖fp81s21_embedField hP hPs Es E (qs u ω) -
              fp81s21_projectField m
                (fp81s21_embedField hP hPs Es E (qs u ω))‖ ^ 2) P ∧
          (∫ ω, ‖fp81s21_embedField hP hPs Es E (qs u ω) -
              fp81s21_projectField m
                (fp81s21_embedField hP hPs Es E (qs u ω))‖ ^ 2 ∂P) ≤
            M * (ε m) ^ 2 ∧
          ∀ᵐ ω ∂P,
            ‖fp81s21_embedField hP hPs Es E (qs u ω) -
                fp81s21_projectField m
                  (fp81s21_embedField hP hPs Es E (qs u ω))‖ ≤
              ε m * ‖qs u ω‖ := by
  obtain ⟨ε, hε, hεlim, hprofile⟩ :=
    fp81s21_embedField_projectionProfile hP hPs Es E
  refine ⟨ε, hε, hεlim, ?_⟩
  intro Ω _ P Q qs M hrep m u hu
  let K : r26t6_Coeff →L[ℝ] r26t6_Coeff :=
    fp81s21_embedField hP hPs Es E
  let T : r26t6_Coeff →L[ℝ] r26t6_Coeff :=
    K - (fp81s21_projectField m).comp K
  have hTnorm : ‖T‖ ≤ ε m := by
    simpa [T, K] using hprofile m
  rcases hrep.2 u hu with ⟨hmem, hsecond, _⟩
  have hsourceSq : Integrable (fun ω => ‖qs u ω‖ ^ 2) P :=
    hmem.norm.integrable_sq
  have htailMem : MemLp (fun ω => T (qs u ω)) 2 P :=
    hmem.continuousLinearMap_comp T
  have htailSq : Integrable
      (fun ω => ‖K (qs u ω) -
        fp81s21_projectField m (K (qs u ω))‖ ^ 2) P := by
    simpa [T, K] using htailMem.norm.integrable_sq
  have hpoint : ∀ ω,
      ‖K (qs u ω) - fp81s21_projectField m (K (qs u ω))‖ ≤
        ε m * ‖qs u ω‖ := by
    intro ω
    calc
      ‖K (qs u ω) - fp81s21_projectField m (K (qs u ω))‖ =
          ‖T (qs u ω)‖ := by simp [T]
      _ ≤ ‖T‖ * ‖qs u ω‖ := T.le_opNorm _
      _ ≤ ε m * ‖qs u ω‖ :=
        mul_le_mul_of_nonneg_right hTnorm (norm_nonneg _)
  have hpointSq : ∀ ω,
      ‖K (qs u ω) - fp81s21_projectField m (K (qs u ω))‖ ^ 2 ≤
        (ε m) ^ 2 * ‖qs u ω‖ ^ 2 := by
    intro ω
    calc
      ‖K (qs u ω) - fp81s21_projectField m (K (qs u ω))‖ ^ 2 ≤
          (ε m * ‖qs u ω‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (hε m) (norm_nonneg _))).2
          (hpoint ω)
      _ = (ε m) ^ 2 * ‖qs u ω‖ ^ 2 := by ring
  have hscaledSq : Integrable
      (fun ω => (ε m) ^ 2 * ‖qs u ω‖ ^ 2) P :=
    hsourceSq.const_mul _
  refine ⟨htailSq, ?_, ?_⟩
  · calc
      (∫ ω, ‖K (qs u ω) -
          fp81s21_projectField m (K (qs u ω))‖ ^ 2 ∂P) ≤
          ∫ ω, (ε m) ^ 2 * ‖qs u ω‖ ^ 2 ∂P :=
        integral_mono_ae htailSq hscaledSq
          (Filter.Eventually.of_forall hpointSq)
      _ = (ε m) ^ 2 * ∫ ω, ‖qs u ω‖ ^ 2 ∂P := integral_const_mul _ _
      _ ≤ (ε m) ^ 2 * M :=
        mul_le_mul_of_nonneg_left hsecond (sq_nonneg _)
      _ = M * (ε m) ^ 2 := by ring
  · filter_upwards [] with ω
    exact hpoint ω

#print axioms HRS.Fp81.S21.fp81s21_embedField_projectionTail

end HRS.Fp81.S21
