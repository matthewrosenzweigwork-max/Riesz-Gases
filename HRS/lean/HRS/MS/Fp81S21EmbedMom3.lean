import HRS.MS.Fp81S21EmbedMom2
import HRS.MS.Fp81S21WeightedMoments

/-! A strong-chart moment representation transfers to the physical chart. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- Transport a `MomentRep` through the adjoint compact chart embedding.
The moment constant remains unchanged because the embedding is contractive. -/
theorem fp81s21_MomentRep_embedField
    {d q : ℕ} {Pw : ℝ}
    {Ω : Type*} [MeasurableSpace Ω]
    (hP : (d : ℝ) < 2 * Pw)
    (hPs : (d : ℝ) < 2 * (Pw + 2))
    (Es : r26t6_WeightedChart d q (Pw + 2))
    (E : r26t6_WeightedChart d (q + 2) Pw)
    (P : Measure Ω)
    (Q : ℝ → Ω → (Euc d → ℝ) → ℝ)
    (qs : ℝ → Ω → r26t6_Coeff) (M : ℝ)
    (hrep : fp81s21_MomentRep Es P Q qs M) :
    fp81s21_MomentRep E P Q
      (fun u ω => fp81s21_embedField hP hPs Es E (qs u ω)) M := by
  let K := fp81s21_embedField hP hPs Es E
  have hKnorm : ‖K‖ ≤ 1 := by
    simpa [K] using fp81s21_embedField_norm_le_one hP hPs Es E
  refine ⟨?_, ?_⟩
  · change Measurable (K ∘ Function.uncurry qs)
    exact K.continuous.measurable.comp hrep.1
  · intro u hu
    obtain ⟨hmem, hsecond, hfield⟩ := hrep.2 u hu
    have hKmem : MemLp (fun ω => K (qs u ω)) 2 P :=
      hmem.continuousLinearMap_comp K
    have hKsq : Integrable (fun ω => ‖K (qs u ω)‖ ^ 2) P :=
      hKmem.norm.integrable_sq
    have hsourceSq : Integrable (fun ω => ‖qs u ω‖ ^ 2) P :=
      hmem.norm.integrable_sq
    have hnorm_le : ∀ ω, ‖K (qs u ω)‖ ≤ ‖qs u ω‖ := by
      intro ω
      calc
        ‖K (qs u ω)‖ ≤ ‖K‖ * ‖qs u ω‖ := K.le_opNorm _
        _ ≤ 1 * ‖qs u ω‖ :=
          mul_le_mul_of_nonneg_right hKnorm (norm_nonneg _)
        _ = ‖qs u ω‖ := one_mul _
    have hsq : ∀ ω, ‖K (qs u ω)‖ ^ 2 ≤ ‖qs u ω‖ ^ 2 := by
      intro ω
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (hnorm_le ω)
    refine ⟨hKmem, ?_, ?_⟩
    · calc
        (∫ ω, ‖K (qs u ω)‖ ^ 2 ∂P) ≤
            ∫ ω, ‖qs u ω‖ ^ 2 ∂P :=
          integral_mono_ae hKsq hsourceSq (Filter.Eventually.of_forall hsq)
        _ ≤ M := hsecond
    · filter_upwards [hfield] with ω hω
      refine ⟨?_, ?_⟩
      · intro f hf
        calc
          fp81s21_chartAction E (K (qs u ω)) f =
              fp81s21_chartAction Es (qs u ω) f :=
            fp81s21_embedField_action hP hPs Es E (qs u ω) f hf
          _ = Q u ω f := hω.1 f hf
      · simpa [K] using
          fp81s21_embedField_dualNorm_transfer hP hPs Es E (qs u ω)
            (Q u ω) hω.1

#print axioms HRS.Fp81.S21.fp81s21_MomentRep_embedField

end HRS.Fp81.S21
