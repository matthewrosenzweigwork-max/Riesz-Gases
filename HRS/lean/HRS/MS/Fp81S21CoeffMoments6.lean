import HRS.MS.Fp81S21CoeffMoments2
import HRS.MS.Fp81S21CoeffMoments3
import HRS.MS.Fp81S21CoeffMoments4
import HRS.MS.Fp81S21CoeffMoments5
import HRS.MS.Fp81S21EmbedMom3
import HRS.MS.Fp81S21WeightedMoments

/-! Transport the coefficient sixth moment through the contractive strong to physical chart map. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- Increasing a coefficient second-moment bound preserves `MomentRep`. -/
theorem fp81s21_MomentRep_mono
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (E : r26t6_WeightedChart d r Pw) (P : Measure Ω)
    (Q : ℝ → Ω → (Euc d → ℝ) → ℝ)
    (q : ℝ → Ω → r26t6_Coeff) {M M' : ℝ}
    (hrep : fp81s21_MomentRep E P Q q M) (hMM' : M ≤ M') :
    fp81s21_MomentRep E P Q q M' := by
  refine ⟨hrep.1, ?_⟩
  intro u hu
  rcases hrep.2 u hu with ⟨hmem, hbound, hfield⟩
  exact ⟨hmem, hbound.trans hMM', hfield⟩

/-- Increasing a sixth-moment bound preserves `Moment6`. -/
theorem fp81s21_Moment6_mono
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [MeasurableSpace E] (P : Measure Ω) (q : Ω → E)
    {M M' : ℝ} (hSix : fp81s21_Moment6 P q M) (hMM' : M ≤ M') :
    fp81s21_Moment6 P q M' := by
  rcases hSix with ⟨hMeas, hInt, hbound⟩
  exact ⟨hMeas, hInt, hbound.trans hMM'⟩

/-- Increasing the uniform sixth-moment bound preserves `Six`. -/
theorem fp81s21_Six_mono
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (q : ℝ → Ω → r26t6_Coeff)
    {M M' : ℝ} (hSix : fp81s21_Six P q M) (hMM' : M ≤ M') :
    fp81s21_Six P q M' := by
  intro u hu
  exact fp81s21_Moment6_mono P (q u) (hSix u hu) hMM'

/-- The sixth coefficient moment is preserved by the contractive chart
embedding. The same moment constant works in the physical chart. -/
theorem fp81s21_Six_embedField
    {d q : ℕ} {Pw : ℝ}
    {Ω : Type*} [MeasurableSpace Ω]
    (hP : (d : ℝ) < 2 * Pw)
    (hPs : (d : ℝ) < 2 * (Pw + 2))
    (Es : r26t6_WeightedChart d q (Pw + 2))
    (E : r26t6_WeightedChart d (q + 2) Pw)
    (P : Measure Ω) (qs : ℝ → Ω → r26t6_Coeff) (M : ℝ)
    (hSix : fp81s21_Six P qs M) :
    fp81s21_Six P
      (fun u ω => fp81s21_embedField hP hPs Es E (qs u ω)) M := by
  let K := fp81s21_embedField hP hPs Es E
  have hKnorm : ‖K‖ ≤ 1 := by
    simpa [K] using fp81s21_embedField_norm_le_one hP hPs Es E
  intro u hu
  obtain ⟨hMeas, hInt, hBound⟩ := hSix u hu
  have hKMeas : AEMeasurable (fun ω => K (qs u ω)) P :=
    K.continuous.measurable.comp_aemeasurable hMeas
  have hnorm : ∀ ω, ‖K (qs u ω)‖ ≤ ‖qs u ω‖ := by
    intro ω
    calc
      ‖K (qs u ω)‖ ≤ ‖K‖ * ‖qs u ω‖ := K.le_opNorm _
      _ ≤ 1 * ‖qs u ω‖ :=
        mul_le_mul_of_nonneg_right hKnorm (norm_nonneg _)
      _ = ‖qs u ω‖ := one_mul _
  have hpow : ∀ ω, ‖K (qs u ω)‖ ^ 6 ≤ ‖qs u ω‖ ^ 6 := by
    intro ω
    exact pow_le_pow_left₀ (norm_nonneg _) (hnorm ω) 6
  have hTargetMeas : AEMeasurable
      (fun ω => ‖K (qs u ω)‖ ^ 6) P :=
    (measurable_norm.pow_const 6).comp_aemeasurable hKMeas
  have hTargetInt : Integrable (fun ω => ‖K (qs u ω)‖ ^ 6) P := by
    exact hInt.mono_nonneg hTargetMeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by positivity)
      (Filter.Eventually.of_forall hpow)
  have hTargetBound :
      (∫ ω, ‖K (qs u ω)‖ ^ 6 ∂P) ≤ M := by
    calc
      _ ≤ ∫ ω, ‖qs u ω‖ ^ 6 ∂P :=
        integral_mono_ae hTargetInt hInt
          (Filter.Eventually.of_forall hpow)
      _ ≤ M := hBound
  exact ⟨hKMeas, hTargetInt, hTargetBound⟩

/-- Transport both parts of a coefficient moment certificate to the physical
chart. `fp81s21_MomentRep_embedField` supplies the representation and
second-moment bound; `fp81s21_Six_embedField` supplies the sixth moment. -/
theorem fp81s21_MomentRepSix_embedField
    {d q : ℕ} {Pw : ℝ}
    {Ω : Type*} [MeasurableSpace Ω]
    (hP : (d : ℝ) < 2 * Pw)
    (hPs : (d : ℝ) < 2 * (Pw + 2))
    (Es : r26t6_WeightedChart d q (Pw + 2))
    (E : r26t6_WeightedChart d (q + 2) Pw)
    (P : Measure Ω)
    (Q : ℝ → Ω → (Euc d → ℝ) → ℝ)
    (qs : ℝ → Ω → r26t6_Coeff) (M2 M6 : ℝ)
    (hRep : fp81s21_MomentRep Es P Q qs M2)
    (hSix : fp81s21_Six P qs M6) :
    fp81s21_MomentRep E P Q
      (fun u ω => fp81s21_embedField hP hPs Es E (qs u ω)) M2 ∧
    fp81s21_Six P
      (fun u ω => fp81s21_embedField hP hPs Es E (qs u ω)) M6 := by
  exact ⟨fp81s21_MomentRep_embedField hP hPs Es E P Q qs M2 hRep,
    fp81s21_Six_embedField hP hPs Es E P qs M6 hSix⟩

/-- A single pair of constants bounds the raw empirical, raw commutator, and
exactly centered quadratic coefficient representatives in the strong chart.
The constants are chosen after `R` and before `N`, `A`, and the field choice. -/
theorem fp81s21_particleCoeffMoments_strong (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4)) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ M2 M6 : ℝ, 0 ≤ M2 ∧ 0 ≤ M6 ∧
          ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
            ∀ Q ∈ ({fp81s21_particleEmpField R N A,
              fp81s21_particleQuadRawField R N A,
              fp81s21_particleQuadField R N A} :
              Set (ℝ → A.Ω → (Euc p.d → ℝ) → ℝ)),
              ∃ qs : ℝ → A.Ω → r26t6_Coeff,
                fp81s21_MomentRep Es A.P Q qs M2 ∧
                fp81s21_Six A.P qs M6 := by
  obtain ⟨δe, hδe, hδehalf, hEmp⟩ :=
    fp81s21_particleEmp_six_momentRep_strong p Es
  obtain ⟨δr, hδr, hδrhalf, hRaw⟩ :=
    fp81s21_particleQuadRaw_six_momentRep_strong p Es
  obtain ⟨δc, hδc, hδchalf, hCenter⟩ :=
    fp81s21_particleQuad_six_momentRep_strong p Es
  let δ0 : ℝ := min δe (min δr δc)
  have hδ0 : 0 < δ0 := lt_min hδe (lt_min hδr hδc)
  have hδ0half : δ0 ≤ 1 / 2 := by
    dsimp [δ0]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans hδchalf)
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  have hδle' : δ ≤ min δe (min δr δc) := by simpa [δ0] using hδle
  obtain ⟨M2e, M6e, hM2e, hM6e, hEmpR⟩ :=
    hEmp δ hδ (hδle'.trans (min_le_left _ _)) R
  obtain ⟨M2r, M6r, hM2r, hM6r, hRawR⟩ :=
    hRaw δ hδ (hδle'.trans ((min_le_right _ _).trans (min_le_left _ _))) R
  obtain ⟨M2c, M6c, hM2c, hM6c, hCenterR⟩ :=
    hCenter δ hδ (hδle'.trans ((min_le_right _ _).trans (min_le_right _ _))) R
  let M2 : ℝ := max M2e (max M2r M2c)
  let M6 : ℝ := max M6e (max M6r M6c)
  have hM2 : 0 ≤ M2 := by dsimp [M2]; positivity
  have hM6 : 0 ≤ M6 := by dsimp [M6]; positivity
  refine ⟨M2, M6, hM2, hM6, ?_⟩
  intro N hN A Q hQ
  have hQ' : Q = fp81s21_particleEmpField R N A ∨
      Q = fp81s21_particleQuadRawField R N A ∨
      Q = fp81s21_particleQuadField R N A := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hQ
  rcases hQ' with hQη | hQB0 | hQB
  · subst Q
    obtain ⟨qs, hrep, hsix⟩ := hEmpR N hN A
    refine ⟨qs, ?_, ?_⟩
    · exact fp81s21_MomentRep_mono Es A.P _ qs hrep (by
        dsimp [M2]
        exact le_max_left _ _)
    · exact fp81s21_Six_mono A.P qs hsix (by
        dsimp [M6]
        exact le_max_left _ _)
  · subst Q
    obtain ⟨qs, hrep, hsix⟩ := hRawR N hN A
    refine ⟨qs, ?_, ?_⟩
    · exact fp81s21_MomentRep_mono Es A.P _ qs hrep (by
        dsimp [M2]
        exact (le_max_left _ _).trans (le_max_right _ _))
    · exact fp81s21_Six_mono A.P qs hsix (by
        dsimp [M6]
        exact (le_max_left _ _).trans (le_max_right _ _))
  · subst Q
    obtain ⟨qs, hrep, hsix⟩ := hCenterR N hN A
    refine ⟨qs, ?_, ?_⟩
    · exact fp81s21_MomentRep_mono Es A.P _ qs hrep (by
        dsimp [M2]
        exact (le_max_right _ _).trans (le_max_right _ _))
    · exact fp81s21_Six_mono A.P qs hsix (by
        dsimp [M6]
        exact (le_max_right _ _).trans (le_max_right _ _))

#print axioms HRS.Fp81.S21.fp81s21_Six_embedField
#print axioms HRS.Fp81.S21.fp81s21_MomentRepSix_embedField
#print axioms HRS.Fp81.S21.fp81s21_MomentRep_mono
#print axioms HRS.Fp81.S21.fp81s21_Moment6_mono
#print axioms HRS.Fp81.S21.fp81s21_Six_mono
#print axioms HRS.Fp81.S21.fp81s21_particleCoeffMoments_strong

end HRS.Fp81.S21

end
