import HRS.Commutator.Whole.XLIAux43

/-!
# X-LI part 44: the unconditional fractional Leibniz rule
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

theorem main_uncond (α : ℝ) (hd : 1 ≤ d) (hα : 0 < α) {r p₁ q₁ p₂ q₂ : ℝ≥0∞}
    (hr : 1 < r) (hr' : r < ⊤) (hp₁ : 1 < p₁) (hq₁ : 1 < q₁) (hp₂ : 1 < p₂) (hq₂ : 1 < q₂)
    (h1 : p₁⁻¹ + q₁⁻¹ = r⁻¹) (h2 : p₂⁻¹ + q₂⁻¹ = r⁻¹) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f g : SchwartzMap 𝔼 ℂ,
      eLpNorm (⇑(Fm α (prodS f g))) r volume ≤
        C * (eLpNorm (⇑(Fm α f)) p₁ volume * eLpNorm (⇑g) q₁ volume +
          eLpNorm (⇑(Fm α g)) p₂ volume * eLpNorm (⇑f) q₂ volume) := by
  refine main_cond α hd hα hr hr' hp₁ hq₁ hp₂ hq₂ h1 h2
    (fun u hu => E1At_Ths hd (-α) (by linarith))
    (fun s hs => E1At_rhoT hd hs) (fun r' hr'1 => ?_)
  by_cases h : 2 < r'
  · exact E4_gt α hd h
  · exact E4_le α hd hr'1 (not_lt.1 h)

end HRS.Commutator.Whole.XLI
