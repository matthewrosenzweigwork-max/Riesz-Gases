import HRS.MS.CovMeasAux6

/-!
# S10.1 (worker S101B), part 7: the covariance density `D_τ` of an admissible `z`

`s101D C m T z τ` is the bounded symmetric bilinear form `(u,v) ↦ 2ν z^τ(F^τ_{u⊗v})` on `𝒦` (`0` outside `[0,T]` or if `z^τ` is not
bounded linear).  `s101_D_data`: there is a constant `K0` (depending on `C,m,T,r,P` only) such that for every `z` with
`S101Lin r Pw T z` and every `τ ∈ [0,T]`: `D_τ` is the bilinear form of its defining formula, symmetric, has bounded trace sums and
`‖D_τ‖_{𝔖₁} ≤ 2|ν| dualNormE(z^τ) K0` (in `ℝ≥0∞`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.MS.Go HRS.MS.FixEq

variable {d : ℕ}

open Classical in
/-- The covariance density of `z` at time `τ` as a bilinear form on `𝒦`. -/
def s101D (C : WholeCoeff d) (m T : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) (τ : ℝ) :
    KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ :=
  if h : ∃ Dc : KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ,
      ∀ u v, Dc u v = 2 * C.ν * z τ (s101Fm (s101Gamma C m T τ) (s101Rk u v)) then h.choose else 0

lemma s101_dualNormE_smul_le {r : ℕ} {P : ℝ} (a : ℝ) (η : (Euc d → ℝ) → ℝ) :
    dualNormE r P (fun f => a * η f) ≤ ENNReal.ofReal |a| * dualNormE r P η := by
  unfold dualNormE
  refine iSup_le fun f => iSup_le fun hf => ?_
  calc ENNReal.ofReal |a * η f| / weightedSobolevE r P f
      = ENNReal.ofReal |a| * (ENNReal.ofReal |η f| / weightedSobolevE r P f) := by
        rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _), mul_div_assoc]
    _ ≤ ENNReal.ofReal |a| * (⨆ (f : Euc d → ℝ) (_ : ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
          0 < weightedSobolevE r P f ∧ weightedSobolevE r P f < ⊤),
          ENNReal.ofReal |η f| / weightedSobolevE r P f) :=
        mul_le_mul' le_rfl (le_iSup₂_of_le f hf le_rfl)

/-- The pointwise linearity and boundedness part of `IsR2L1F`. -/
def S101Lin (r : ℕ) (Pw T : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) : Prop :=
  ∀ u ∈ Icc (0 : ℝ) T, (∀ f g, IsR2WeightedTest r Pw f → IsR2WeightedTest r Pw g →
      z u (f + g) = z u f + z u g) ∧
    (∀ (c : ℝ) f, IsR2WeightedTest r Pw f → z u (c • f) = c * z u f) ∧
    ∃ M : ℝ, ∀ f, IsR2WeightedTest r Pw f → |z u f| ≤ M * (weightedSobolevE r Pw f).toReal

lemma s101_isBounded_of_lin {r : ℕ} {Pw T : ℝ} {z : ℝ → (Euc d → ℝ) → ℝ} (hz : S101Lin r Pw T z)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) (a : ℝ) :
    IsBoundedLinearOnE r Pw (fun f => a * z τ f) := by
  obtain ⟨hadd, hsmul, M, hM⟩ := hz τ hτ
  refine ⟨fun f g hf hf' hg hg' c => ⟨?_, ?_⟩, ?_⟩
  · have := hadd f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    simp only [this]; ring
  · have := hsmul c f ⟨hf, hf'⟩
    simp only [this]; ring
  · refine ⟨|a| * |M|, fun f hf hf' => ?_⟩
    have := hM f ⟨hf, hf'⟩
    calc |a * z τ f| = |a| * |z τ f| := abs_mul _ _
      _ ≤ |a| * (M * (weightedSobolevE r Pw f).toReal) := mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ ≤ |a| * (|M| * (weightedSobolevE r Pw f).toReal) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self _) ENNReal.toReal_nonneg)
            (abs_nonneg _)
      _ = |a| * |M| * (weightedSobolevE r Pw f).toReal := by ring

theorem s101_D_data (hd : 1 ≤ d) {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {Pw : ℝ}
    (hP : (d : ℝ) < 2 * Pw) (horb : R2OrbitSummable C m T r) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ z : ℝ → (Euc d → ℝ) → ℝ, S101Lin r Pw T z → ∀ τ ∈ Icc (0 : ℝ) T,
      (∀ u v, s101D C m T z τ u v = 2 * C.ν * z τ (s101Fm (s101Gamma C m T τ) (s101Rk u v))) ∧
      (∀ u v, s101D C m T z τ u v = s101D C m T z τ v u) ∧
      BddAbove (Set.range fun p : HRS.OrthonormalPairs (KSpace d m T) =>
        ∑ i, |s101D C m T z τ (p.1.2.1 i) (p.1.2.2 i)|) ∧
      ENNReal.ofReal (HRS.traceNormForm (s101D C m T z τ)) ≤
        ENNReal.ofReal |2 * C.ν| * dualNormE r Pw (z τ) * ENNReal.ofReal K0 := by
  obtain ⟨c, hD⟩ := s101_data_of_horb hd horb
  obtain ⟨B, hB0, hB⟩ := s101_gamma_smooth hd hD
  refine ⟨s57pC d r Pw * s101Cf d r B, mul_nonneg (s57pC_nonneg d r Pw) (s101Cf_nonneg hB0 r),
    fun z hz τ hτ => ?_⟩
  have hη := s101_isBounded_of_lin hz hτ (2 * C.ν)
  obtain ⟨hΓ, hΓb⟩ := hB τ hτ
  obtain ⟨Dc, hDc, hsym, hbdd, htr⟩ := s101_Dform_data hP hΓ hΓb hη
  have hex : ∃ Dc : KSpace d m T →L[ℝ] KSpace d m T →L[ℝ] ℝ,
      ∀ u v, Dc u v = 2 * C.ν * z τ (s101Fm (s101Gamma C m T τ) (s101Rk u v)) := ⟨Dc, hDc⟩
  have hEq : s101D C m T z τ = Dc := by
    have hspec := (by unfold s101D; rw [dif_pos hex]; exact hex.choose_spec :
      ∀ u v, s101D C m T z τ u v = 2 * C.ν * z τ (s101Fm (s101Gamma C m T τ) (s101Rk u v)))
    ext u v
    rw [hspec, hDc]
  rw [hEq]
  refine ⟨hDc, hsym, hbdd, htr.trans ?_⟩
  exact mul_le_mul' (s101_dualNormE_smul_le (r := r) (P := Pw) (2 * C.ν) (z τ)) le_rfl

end HRS.MS.CovMeas
