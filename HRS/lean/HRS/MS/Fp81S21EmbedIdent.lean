import HRS.MS.Fp81S21EmbedMom3
import HRS.MS.Fp81S21PredMap2

/-! Uniqueness of coefficient representatives in a weighted chart, and
extension of a represented physical functional to weighted tests. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.R2Interp HRS.MS.ProClosureS111

/-- Two `MomentRep` coefficient families for the same compact-test
functional agree almost everywhere at each fixed nonnegative time. -/
theorem fp81s21_MomentRep_eq_ae
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (hP : (d : ℝ) < 2 * Pw)
    (E : r26t6_WeightedChart d r Pw) (P : Measure Ω)
    (Q : ℝ → Ω → (Euc d → ℝ) → ℝ)
    (q₁ q₂ : ℝ → Ω → r26t6_Coeff) (M₁ M₂ : ℝ)
    (hq₁ : fp81s21_MomentRep E P Q q₁ M₁)
    (hq₂ : fp81s21_MomentRep E P Q q₂ M₂) :
    ∀ u, 0 ≤ u → (fun ω => q₁ u ω) =ᵐ[P] (fun ω => q₂ u ω) := by
  intro u hu
  obtain ⟨_, _, hfield₁⟩ := hq₁.2 u hu
  obtain ⟨_, _, hfield₂⟩ := hq₂.2 u hu
  filter_upwards [hfield₁, hfield₂] with ω hω₁ hω₂
  have hcompact : ∀ f, IsR2Test f →
      fp81s21_chartAction E (q₁ u ω - q₂ u ω) f = 0 := by
    intro f hf
    have hlin : fp81s21_chartAction E (q₁ u ω - q₂ u ω) f =
        fp81s21_chartAction E (q₁ u ω) f -
          fp81s21_chartAction E (q₂ u ω) f := by
      simp [fp81s21_chartAction, inner_sub_left]
    rw [hlin, hω₁.1 f hf, hω₂.1 f hf]
    ring
  have hdual :
      dualNormE r Pw (fp81s21_chartAction E (q₁ u ω - q₂ u ω)) = 0 := by
    unfold dualNormE
    apply le_antisymm
    · refine iSup_le fun f => iSup_le fun hf => ?_
      have htest : IsR2Test f := ⟨hf.1, hf.2.1⟩
      rw [hcompact f htest]
      simp
    · exact bot_le
  have hnorm : ENNReal.ofReal ‖q₁ u ω - q₂ u ω‖ = 0 := by
    rw [← fp81s21_chartAction_dualNorm hP E (q₁ u ω - q₂ u ω)]
    exact hdual
  have hnorm' : ‖q₁ u ω - q₂ u ω‖ = 0 := by
    have h := congrArg ENNReal.toReal hnorm
    rw [ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_zero] at h
    exact h
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm')

/-- The embedded strong representative is the target representative in the
physical chart, almost everywhere at every fixed nonnegative time. -/
theorem fp81s21_embedField_eq_MomentRep
    {d q : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (hP : (d : ℝ) < 2 * Pw)
    (hPs : (d : ℝ) < 2 * (Pw + 2))
    (Es : r26t6_WeightedChart d q (Pw + 2))
    (E : r26t6_WeightedChart d (q + 2) Pw)
    (P : Measure Ω) (Q : ℝ → Ω → (Euc d → ℝ) → ℝ)
    (qs q₀ : ℝ → Ω → r26t6_Coeff) (M M₀ : ℝ)
    (hqs : fp81s21_MomentRep Es P Q qs M)
    (hq₀ : fp81s21_MomentRep E P Q q₀ M₀) :
    ∀ u, 0 ≤ u →
      (fun ω => fp81s21_embedField hP hPs Es E (qs u ω)) =ᵐ[P]
        (fun ω => q₀ u ω) := by
  have hEmbed := fp81s21_MomentRep_embedField hP hPs Es E P Q qs M hqs
  exact fp81s21_MomentRep_eq_ae hP E P Q
    (fun u ω => fp81s21_embedField hP hPs Es E (qs u ω)) q₀ M M₀ hEmbed hq₀

/-- A represented functional with `S102Z` regularity agrees with its chart
action on every weighted test, almost everywhere at each fixed time. -/
theorem fp81s21_MomentRep_weightedTest_agreement
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (hP : (d : ℝ) < 2 * Pw)
    (E : r26t6_WeightedChart d r Pw) (P : Measure Ω)
    (Q : ℝ → Ω → (Euc d → ℝ) → ℝ)
    (q : ℝ → Ω → r26t6_Coeff) (M : ℝ)
    (hrep : fp81s21_MomentRep E P Q q M)
    (hQ : ∀ u ω, S102Z r Pw (Q u ω)) :
    ∀ u, 0 ≤ u → ∀ᵐ ω ∂P, ∀ f, IsR2WeightedTest r Pw f →
      fp81s21_chartAction E (q u ω) f = Q u ω f := by
  intro u hu
  obtain ⟨_, _, hfield⟩ := hrep.2 u hu
  filter_upwards [hfield] with ω hω
  intro f hf
  exact fp81s21_chartAction_eq_of_compact_agreement hP E (q u ω)
    (Q u ω) (hQ u ω) hω.1 f hf

/-- Weighted-test agreement also transfers to an embedded strong family when
a target `MomentRep` for the same functional has `S102Z` regularity. -/
theorem fp81s21_embedField_weightedTest_agreement
    {d q : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (hP : (d : ℝ) < 2 * Pw)
    (hPs : (d : ℝ) < 2 * (Pw + 2))
    (Es : r26t6_WeightedChart d q (Pw + 2))
    (E : r26t6_WeightedChart d (q + 2) Pw)
    (P : Measure Ω) (Q : ℝ → Ω → (Euc d → ℝ) → ℝ)
    (qs q₀ : ℝ → Ω → r26t6_Coeff) (M M₀ : ℝ)
    (hqs : fp81s21_MomentRep Es P Q qs M)
    (hq₀ : fp81s21_MomentRep E P Q q₀ M₀)
    (hQ : ∀ u ω, S102Z (q + 2) Pw (Q u ω)) :
    ∀ u, 0 ≤ u → ∀ᵐ ω ∂P, ∀ f, IsR2WeightedTest (q + 2) Pw f →
      fp81s21_chartAction E
        (fp81s21_embedField hP hPs Es E (qs u ω)) f = Q u ω f := by
  intro u hu
  have hsame := fp81s21_embedField_eq_MomentRep hP hPs Es E P Q qs q₀ M M₀ hqs hq₀ u hu
  have hweighted := fp81s21_MomentRep_weightedTest_agreement hP E P Q q₀ M₀ hq₀ hQ u hu
  filter_upwards [hsame, hweighted] with ω hω hagree
  intro f hf
  simpa [hω] using hagree f hf

#print axioms HRS.Fp81.S21.fp81s21_MomentRep_eq_ae
#print axioms HRS.Fp81.S21.fp81s21_embedField_eq_MomentRep
#print axioms HRS.Fp81.S21.fp81s21_MomentRep_weightedTest_agreement
#print axioms HRS.Fp81.S21.fp81s21_embedField_weightedTest_agreement

end HRS.Fp81.S21
