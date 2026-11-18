import HRS.MS.Fp81S21EmpFour3
import HRS.MS.Fp81S21CoeffMoments6

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21

open HRS HRS.MS.R26T3 HRS.MS.R26T6

private theorem fp81s21_versionN_six_normalized
    {d r r' : ℕ} {Pw Ps : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (hr : r + 2 = r') (hp : Pw + 2 = Ps)
    (hP : (d : ℝ) < 2 * Pw) (hPs : (d : ℝ) < 2 * Ps)
    (Es : r26t6_WeightedChart d r Ps) (E : r26t6_WeightedChart d r' Pw)
    (P : Measure Ω) (qs : ℝ → Ω → r26t6_Coeff) (M : ℝ)
    (hSix : fp81s21_Six P qs M) :
    fp81s21_Six P
      (fun u ω => fp81s21_embedField_normalized hr hp hP hPs Es E (qs u ω)) M := by
  subst r'
  subst Ps
  exact fp81s21_Six_embedField hP hPs Es E P qs M hSix

/-- The embedded selected particle representative has the measurable sections
and initial fourth-moment data required by the Holder-version theorem. -/
theorem fp81s21_embedded_initial_fourth
    (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (qs : ℝ → Ω → r26t6_Coeff) (M6 : ℝ)
    (hqsJoint : Measurable (Function.uncurry qs))
    (hqsSix : fp81s21_Six P qs M6)
    (a : ℝ) (ha : 0 ≤ a) :
    (∀ t, Measurable (fun ω =>
      fp81s21_gaussian_chartEmbed p Es E (qs t ω))) ∧
    MemLp (fun ω => fp81s21_gaussian_chartEmbed p Es E (qs a ω)) 4 P ∧
    (∫ ω, ‖fp81s21_gaussian_chartEmbed p Es E (qs a ω)‖ ^ 4 ∂P) ≤ 1 + M6 := by
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by nlinarith [p.hd]
  have hPs : (p.d : ℝ) < 2 * ((p.d : ℝ) + 4) := by nlinarith [p.hd]
  have hWeakSix : fp81s21_Six P
      (fun u ω => fp81s21_gaussian_chartEmbed p Es E (qs u ω)) M6 := by
    simpa [fp81s21_gaussian_chartEmbed] using
      fp81s21_versionN_six_normalized (by omega) (by ring) hP hPs Es E
        P qs M6 hqsSix
  let qη : ℝ → Ω → r26t6_Coeff :=
    fun u ω => fp81s21_gaussian_chartEmbed p Es E (qs u ω)
  have hqηJoint : Measurable (Function.uncurry qη) := by
    exact (fp81s21_gaussian_chartEmbed p Es E).continuous.measurable.comp hqsJoint
  have hqηMeas : ∀ t, Measurable (qη t) := by
    intro t
    exact hqηJoint.comp (measurable_const.prodMk measurable_id)
  have hfour := fp81s21_empFour_Moment6_to_fourth (qη a) M6 (hWeakSix a ha)
  have hMem : MemLp (qη a) 4 P := by
    exact (integrable_norm_rpow_iff (hqηMeas a).aestronglyMeasurable
      (by norm_num) (by norm_num)).1 (by simpa using hfour.1)
  refine ⟨?_, ?_, ?_⟩
  · intro t
    simpa [qη] using hqηMeas t
  · simpa [qη] using hMem
  · simpa [qη] using hfour.2

#print axioms HRS.Fp81.S21.fp81s21_embedded_initial_fourth

end HRS.Fp81.S21
