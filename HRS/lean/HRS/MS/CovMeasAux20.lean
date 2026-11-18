import HRS.MS.CovMeasAux19

/-!
# S10.1 (worker S101B), part 20: linearity in `z` of the covariance density

`S101Adm'` (`S101Adm` and `S101Tr`) is the weak admissibility used to define `Jm`; it is closed under sums and scalar multiples
(`IsR2L1F` alone is not obviously closed under `+`: `∫⁻ dualNormE` of a sum of non-measurable densities), and implied by
`IsR2L1F ∧ R2JIntegrandMeas`.  `s101_D_add`, `s101_D_smul`: `D^{z+z'}_τ = D^z_τ + D^{z'}_τ`, `D^{cz}_τ = c D^z_τ`.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.MS.Go HRS.MS.FixEq
open Classical

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {Pw : ℝ} {z z' : ℝ → (Euc d → ℝ) → ℝ}

lemma S101Lin.add (h : S101Lin r Pw T z) (h' : S101Lin r Pw T z') : S101Lin r Pw T (z + z') := by
  intro u hu
  obtain ⟨a1, s1, M1, hM1⟩ := h u hu
  obtain ⟨a2, s2, M2, hM2⟩ := h' u hu
  refine ⟨fun f g hf hg => ?_, fun c f hf => ?_, M1 + M2, fun f hf => ?_⟩
  · simp only [Pi.add_apply]; rw [a1 f g hf hg, a2 f g hf hg]; ring
  · simp only [Pi.add_apply]; rw [s1 c f hf, s2 c f hf]; ring
  · simp only [Pi.add_apply]
    calc |z u f + z' u f| ≤ |z u f| + |z' u f| := abs_add_le _ _
      _ ≤ M1 * (weightedSobolevE r Pw f).toReal + M2 * (weightedSobolevE r Pw f).toReal :=
          add_le_add (hM1 f hf) (hM2 f hf)
      _ = (M1 + M2) * (weightedSobolevE r Pw f).toReal := by ring

lemma S101Lin.smul (c : ℝ) (h : S101Lin r Pw T z) : S101Lin r Pw T (c • z) := by
  intro u hu
  obtain ⟨a1, s1, M1, hM1⟩ := h u hu
  refine ⟨fun f g hf hg => ?_, fun a f hf => ?_, |c| * |M1|, fun f hf => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]; rw [a1 f g hf hg]; ring
  · simp only [Pi.smul_apply, smul_eq_mul]; rw [s1 a f hf]; ring
  · simp only [Pi.smul_apply, smul_eq_mul]
    calc |c * z u f| = |c| * |z u f| := abs_mul _ _
      _ ≤ |c| * (M1 * (weightedSobolevE r Pw f).toReal) := mul_le_mul_of_nonneg_left (hM1 f hf) (abs_nonneg _)
      _ ≤ |c| * (|M1| * (weightedSobolevE r Pw f).toReal) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self _) ENNReal.toReal_nonneg)
            (abs_nonneg _)
      _ = |c| * |M1| * (weightedSobolevE r Pw f).toReal := by ring

lemma s101_meas_add (h : R2JIntegrandMeas C m T z) (h' : R2JIntegrandMeas C m T z') :
    R2JIntegrandMeas C m T (z + z') := by
  intro ta tb φa φb ha hb hta htb
  have := (h ta tb φa φb ha hb hta htb).add (h' ta tb φa φb ha hb hta htb)
  exact this

lemma s101_meas_smul (c : ℝ) (h : R2JIntegrandMeas C m T z) : R2JIntegrandMeas C m T (c • z) := by
  intro ta tb φa φb ha hb hta htb
  exact (h ta tb φa φb ha hb hta htb).const_mul c

lemma S101Adm.add (A : S101Adm C m T r Pw z) (A' : S101Adm C m T r Pw z') : S101Adm C m T r Pw (z + z') :=
  ⟨A.hd, A.hP, A.horb, A.hz.add A'.hz, s101_meas_add A.hmeas A'.hmeas⟩

lemma S101Adm.smul (c : ℝ) (A : S101Adm C m T r Pw z) : S101Adm C m T r Pw (c • z) :=
  ⟨A.hd, A.hP, A.horb, A.hz.smul c, s101_meas_smul c A.hmeas⟩

/-- `F_{u⊗v}` is a weighted test function. -/
lemma s101_Fm_isTest (A : S101Adm C m T r Pw z) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) (u v : KSpace d m T) :
    IsR2WeightedTest r Pw (s101Fm (s101Gamma C m T τ) (s101Rk u v)) := by
  obtain ⟨c, hD⟩ := s101_data_of_horb A.hd A.horb
  obtain ⟨B, hB0, hB⟩ := s101_gamma_smooth A.hd hD
  obtain ⟨hΓ, hΓb⟩ := hB τ hτ
  exact s101_Fm_test A.hP hΓ hΓb (s101Rk u v)

theorem s101_D_add (A : S101Adm C m T r Pw z) (A' : S101Adm C m T r Pw z') {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) T) :
    s101D C m T (z + z') τ = s101D C m T z τ + s101D C m T z' τ := by
  ext u v
  rw [s101_D_apply (A.add A') hτ, add_apply, add_apply,
    s101_D_apply A hτ, s101_D_apply A' hτ]
  simp only [Pi.add_apply]
  ring

theorem s101_D_smul (c : ℝ) (A : S101Adm C m T r Pw z) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) :
    s101D C m T (c • z) τ = c • s101D C m T z τ := by
  ext u v
  rw [s101_D_apply (A.smul c) hτ, smul_apply, smul_apply,
    s101_D_apply A hτ]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end HRS.MS.CovMeas
