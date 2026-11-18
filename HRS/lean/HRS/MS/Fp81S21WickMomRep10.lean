import HRS.MS.Fp81S21WickMomRep9
import HRS.MS.Fp81S21EmbedTail

/-! A common spatial projection profile for time sections. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T6

/-- One chart-dependent profile works for every probability law and every
strong representative with the given moment bound. The projection has finitely
many spatial coordinates; this does not assert finite rank on time-L². -/
theorem fp81s21_wick_time_projection_profile
    {d r : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw) (hPs : (d : ℝ) < 2 * (Pw + 2))
    (Es : r26t6_WeightedChart d r (Pw + 2))
    (E : r26t6_WeightedChart d (r + 2) Pw) :
    ∃ ε : ℕ → ℝ, (∀ m, 0 ≤ ε m) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ M : ℝ, 0 ≤ M → ∀ {Ω : Type*} [MeasurableSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P]
        (Q : ℝ → Ω → (Euc d → ℝ) → ℝ)
        (qs : ℝ → Ω → r26t6_Coeff),
        fp81s21_MomentRep Es P Q qs M →
        ∀ a : ℝ, 0 ≤ a → ∀ H : ℝ, 0 ≤ H →
          ∃ U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)),
            let qe : ℝ → Ω → r26t6_Coeff := fun u ω =>
              fp81s21_embedField hP hPs Es E (qs u ω)
            fp81s21_TimeL2Rep P qe M a H U ∧
            fp81s21_TimeRep E P (fun u ω => fp81s21_chartAction E (qe u ω))
              qe M a H U ∧
            ∀ m, fp81s21_SqErr P U (fun ω => fp81s21_timeProject H m (U ω))
              (Real.sqrt (H * M) * ε m) ∧
              ∀ ρ : ℝ, 0 < ρ →
                P {ω | ρ < ‖U ω - fp81s21_timeProject H m (U ω)‖} ≤
                  ENNReal.ofReal (H * M * (ε m) ^ 2 / ρ ^ 2) := by
  obtain ⟨ε, hε, hεlim, htail⟩ := fp81s21_embedField_projectionTail hP hPs Es E
  refine ⟨ε, hε, hεlim, ?_⟩
  intro M hM Ω _ P _ Q qs hs a ha H hH
  let qe : ℝ → Ω → r26t6_Coeff := fun u ω => fp81s21_embedField hP hPs Es E (qs u ω)
  have hw := fp81s21_MomentRep_embedField hP hPs Es E P Q qs M hs
  obtain ⟨U, hcore⟩ := fp81s21_MomentRep_time_section E P Q qe M a H hw ha hH
  have htime : fp81s21_TimeRep E P
      (fun u ω => fp81s21_chartAction E (qe u ω)) qe M a H U := by
    apply fp81s21_TimeRep_of_TimeL2Rep_product hP E P _ qe M a H U hcore
    · exact Filter.Eventually.of_forall (fun _ _ _ => rfl)
    · exact Filter.Eventually.of_forall (fun z => fp81s21_chartAction_S102Z E (qe (a + z.1) z.2))
  refine ⟨U, hcore, htime, ?_⟩
  apply fp81s21_time_projection_tails P qe M a H U hw.1 hcore hM ha hH ε hε
  intro m u hu
  exact ⟨(htail P Q qs M hs m u hu).1, (htail P Q qs M hs m u hu).2.1⟩

#print axioms fp81s21_wick_time_projection_profile
end HRS.Fp81.S21
end
