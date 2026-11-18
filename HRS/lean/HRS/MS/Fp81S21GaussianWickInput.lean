import HRS.MS.Fp81S21GaussianW0
import HRS.MS.Fp81S21GaussianWickTime4
import HRS.MS.Fp81S21GaussianWickPhysical2
import HRS.MS.Fp81S21Skeleton

/-! Packet 37, unit 9: the exact WickInput on one radius before every physical
selection. The proposed Rad and WickAll abbreviations are expanded below.
The letI binders install existing instances, adding no hypotheses. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3

/-- All four WickInput fields for every retained physical selection and every
supplied cross-density satisfying ChiClause, on a common positive radius. -/
theorem fp81s21_gaussian_wick_input (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      letI := fp81s21_initialMeasure_isProbability p R
      ∀ Q : fp81s21_Physical35 p R,
      letI : MeasurableSpace Q.src.G0.Ω := Q.src.G0.mΩ
      letI : IsProbabilityMeasure Q.src.G0.P := Q.src.G0.prob
      ∀ a : ℝ, 0 ≤ a → ∀ (τ : Fin 3 → Icc (0 : ℝ) p.T)
        (φ : Fin 3 → Euc p.d → ℝ) (χ : Fin 3 → ℝ → Euc p.d → ℝ)
        (hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)),
      S21eChiClause p.d p.s p.a p.β p.γ R.ρ p.T a τ φ χ →
      fp81s21_WickInput (d := p.d) (s := p.s) (a := p.a) (β := p.β)
        (β₀ := p.γ) (T := p.T) (a₀ := a) (ρ := R.ρ) Q.src.G0.P
        (initialKappa R a) (fp81s21_physical35_D Q.tofp81s21_Gaussian35Selection Q.OD a)
        (r26t3_Zpath Q.src.G0 a)
        (fun ω => (fp81s21_physical35_J Q.tofp81s21_Gaussian35Selection Q.OJ a ω :
          TensorDual (Window p) 2)) τ φ χ hφ := by
  obtain ⟨δW, hW, hhalf, hW0⟩ := fp81s21_gaussian_W0 p
  obtain ⟨δT, hT, _, htime⟩ := fp81s21_gaussian_wick_time p
  obtain ⟨δP, hP, _, hphysical⟩ := fp81s21_gaussian_wick_physical p
  refine ⟨min δW (min δT δP), lt_min hW (lt_min hT hP),
    (min_le_left _ _).trans hhalf, ?_⟩
  intro δ hδ hδle R Q a ha τ φ χ hφ hχ
  letI := fp81s21_initialMeasure_isProbability p R
  letI : MeasurableSpace Q.src.G0.Ω := Q.src.G0.mΩ
  letI : IsProbabilityMeasure Q.src.G0.P := Q.src.G0.prob
  have hl : δ ≤ δW ∧ δ ≤ δT ∧ δ ≤ δP := by
    simpa only [le_min_iff] using hδle
  obtain ⟨hW1, hW2⟩ := hphysical δ hδ hl.2.2 R Q a ha τ φ χ hφ hχ
  refine ⟨htime δ hδ hl.2.1 R Q a ha τ φ χ hφ hχ, ?_, ?_, ?_⟩
  · simpa only [r26t3_coeff, r26t3_mu] using (hW0 δ hδ hl.1 R a ha τ φ hφ).1
  · simpa only [fp81s21_W1, fp81s21_cross37_X, fp81s21_wick_time_f,
      r26t3_coeff, fp81s21_physical35_D, dif_pos ha] using hW1
  · simpa only [fp81s21_W2, fp81s21_cross37_X, fp81s21_wick_time_f,
      r26t3_coeff, fp81s21_physical35_J, dif_pos ha] using hW2

end HRS.Fp81.S21
end
#print axioms HRS.Fp81.S21.fp81s21_gaussian_wick_input
