import HRS.MS.Fp81S21DualMeas

/-! `IsR2L1F` corollaries for individual, summed, and scaled fields. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HRS.Fp81.S21

open HRS HRS.Whole

/-- The full `IsR2L1F` hypothesis implies a.e. measurability of its
physical weighted-dual norm. -/
theorem fp81s21_dualNormE_aemeasurable_of_IsR2L1F
    {d r : ℕ} {Pw T : ℝ} (hd : 0 < d) (hP : (d : ℝ) < 2 * Pw)
    {z : ℝ → (Euc d → ℝ) → ℝ} (hz : IsR2L1F r Pw T z) :
    AEMeasurable (fun u => dualNormE r Pw (z u))
      (volume.restrict (Icc (0 : ℝ) T)) := by
  rcases hz with ⟨hlin, hmeas, _⟩
  exact fp81s21_dualNormE_aemeasurable_of_L1F hd hP hlin hmeas

/-- The sum of two `IsR2L1F` fields has an a.e.-measurable weighted-dual
norm. -/
theorem fp81s21_dualNormE_aemeasurable_add_of_IsR2L1F
    {d r : ℕ} {Pw T : ℝ} (hd : 0 < d) (hP : (d : ℝ) < 2 * Pw)
    {z z' : ℝ → (Euc d → ℝ) → ℝ}
    (hz : IsR2L1F r Pw T z) (hz' : IsR2L1F r Pw T z') :
    AEMeasurable (fun u => dualNormE r Pw ((z + z') u))
      (volume.restrict (Icc (0 : ℝ) T)) := by
  rcases hz with ⟨hzlin, hzmeas, _⟩
  rcases hz' with ⟨hz'lin, hz'meas, _⟩
  have hlin : ∀ u ∈ Icc (0 : ℝ) T,
      (∀ f g, IsR2WeightedTest r Pw f → IsR2WeightedTest r Pw g →
        (z + z') u (f + g) = (z + z') u f + (z + z') u g) ∧
      (∀ c f, IsR2WeightedTest r Pw f → (z + z') u (c • f) =
        c * (z + z') u f) ∧
      ∃ M, ∀ f, IsR2WeightedTest r Pw f →
        |(z + z') u f| ≤ M * (weightedSobolevE r Pw f).toReal := by
    intro u hu
    obtain ⟨hadd, hsmul, M, hM⟩ := hzlin u hu
    obtain ⟨hadd', hsmul', M', hM'⟩ := hz'lin u hu
    refine ⟨?_, ?_, M + M', ?_⟩
    · intro f g hf hg
      simp only [Pi.add_apply]
      rw [hadd f g hf hg, hadd' f g hf hg]
      ring
    · intro c f hf
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hsmul c f hf, hsmul' c f hf]
      ring
    · intro f hf
      simp only [Pi.add_apply]
      calc
        |z u f + z' u f| ≤ |z u f| + |z' u f| := abs_add_le _ _
        _ ≤ M * (weightedSobolevE r Pw f).toReal +
            M' * (weightedSobolevE r Pw f).toReal := add_le_add (hM f hf) (hM' f hf)
        _ = (M + M') * (weightedSobolevE r Pw f).toReal := by ring
  have hmeas : ∀ f, IsR2WeightedTest r Pw f →
      Measurable (fun u => (z + z') u f) := by
    intro f hf
    change Measurable (fun u : ℝ => z u f + z' u f)
    exact (hzmeas f hf).add (hz'meas f hf)
  exact fp81s21_dualNormE_aemeasurable_of_L1F hd hP hlin hmeas

/-- A scalar multiple of an `IsR2L1F` field has an a.e.-measurable
weighted-dual norm. -/
theorem fp81s21_dualNormE_aemeasurable_smul_of_IsR2L1F
    {d r : ℕ} {Pw T c : ℝ} (hd : 0 < d) (hP : (d : ℝ) < 2 * Pw)
    {z : ℝ → (Euc d → ℝ) → ℝ} (hz : IsR2L1F r Pw T z) :
    AEMeasurable (fun u => dualNormE r Pw ((c • z) u))
      (volume.restrict (Icc (0 : ℝ) T)) := by
  rcases hz with ⟨hzlin, hzmeas, _⟩
  have hlin : ∀ u ∈ Icc (0 : ℝ) T,
      (∀ f g, IsR2WeightedTest r Pw f → IsR2WeightedTest r Pw g →
        (c • z) u (f + g) = (c • z) u f + (c • z) u g) ∧
      (∀ b f, IsR2WeightedTest r Pw f → (c • z) u (b • f) =
        b * (c • z) u f) ∧
      ∃ M, ∀ f, IsR2WeightedTest r Pw f →
        |(c • z) u f| ≤ M * (weightedSobolevE r Pw f).toReal := by
    intro u hu
    obtain ⟨hadd, hsmul, M, hM⟩ := hzlin u hu
    refine ⟨?_, ?_, |c| * |M|, ?_⟩
    · intro f g hf hg
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hadd f g hf hg]
      ring
    · intro b f hf
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hsmul b f hf]
      ring
    · intro f hf
      simp only [Pi.smul_apply, smul_eq_mul]
      have hM' : M * (weightedSobolevE r Pw f).toReal ≤
          |M| * (weightedSobolevE r Pw f).toReal :=
        mul_le_mul_of_nonneg_right (le_abs_self M) ENNReal.toReal_nonneg
      calc
        |c * z u f| = |c| * |z u f| := abs_mul _ _
        _ ≤ |c| * (M * (weightedSobolevE r Pw f).toReal) :=
          mul_le_mul_of_nonneg_left (hM f hf) (abs_nonneg _)
        _ ≤ |c| * (|M| * (weightedSobolevE r Pw f).toReal) :=
          mul_le_mul_of_nonneg_left hM' (abs_nonneg _)
        _ = (|c| * |M|) * (weightedSobolevE r Pw f).toReal := by ring
  have hmeas : ∀ f, IsR2WeightedTest r Pw f →
      Measurable (fun u => (c • z) u f) := by
    intro f hf
    change Measurable (fun u : ℝ => c * z u f)
    exact (hzmeas f hf).const_mul c
  exact fp81s21_dualNormE_aemeasurable_of_L1F hd hP hlin hmeas

#print axioms HRS.Fp81.S21.fp81s21_dualNormE_aemeasurable_of_IsR2L1F
#print axioms HRS.Fp81.S21.fp81s21_dualNormE_aemeasurable_add_of_IsR2L1F
#print axioms HRS.Fp81.S21.fp81s21_dualNormE_aemeasurable_smul_of_IsR2L1F

end HRS.Fp81.S21
end
