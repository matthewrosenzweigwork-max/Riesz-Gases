import HRS.MS.S21H2_W13A
import HRS.MS.S11Q3C3

/-!
# S21H2, packet R26-T3.W13 (part B): the native class tuple at the explicit indices `(1, d/2 + 8)`

`s11q3_cores_tuple` (S11Q3C3) hides its indices behind an existential; its proof chooses `j = 1`, `m = d/2 + 8`.  The same proof, with the indices
exposed: `S113XTupleOK` and `S113XLocalizedI` at `(1, d/2+8)`, and (for `s = 0`) the log-normalizer core `S113XLogNormalizer`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.S21H2W13

open HRS HRS.Whole HRS.MS.S113BD HRS.MS.S113X2C HRS.MS.S11Q2 HRS.MS.S11Q3

variable {d : ℕ}

theorem s21h2_tuple (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (β q : ℝ) (hβ : 0 < β)
    (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) :
    ∃ εstar r c₀ c C₁ : ℝ, S113XTupleOK d s q β ρ₀ 1 (d / 2 + 8) εstar r c₀ c C₁ ∧
      S113XLocalizedI d s q β ρ₀ 1 (d / 2 + 8) εstar r c₀ := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  have hmm : (d : ℝ) / 2 + ((1 : ℕ) : ℝ) + 6 < ((d / 2 + 8 : ℕ) : ℝ) := by
    have : (d : ℝ) ≤ 2 * ((d / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast (by omega : d ≤ 2 * (d / 2) + 1)
    push_cast; linarith
  have hm3 : (d : ℝ) / 2 + 3 < ((d / 2 + 8 : ℕ) : ℝ) := by
    have : ((1 : ℕ) : ℝ) = 1 := by simp
    linarith
  obtain ⟨εstar, r, c₀, c, C, hε, hr, hc₀, hc, hC, hNL, hall⟩ :=
    s11q3_class_data hd hs0 hsd β q hβ hq 1 (d / 2 + 8) le_rfl hmm hm3 ρ₀ hρ
  have hOK : S113XTupleOK d s q β ρ₀ 1 (d / 2 + 8) εstar r c₀ c C :=
    ⟨hε, hr, hc₀, hc, hC, hNL, fun f0 hf0 ρ hρ' => (hall f0 hf0 ρ hρ').1⟩
  refine ⟨εstar, r, c₀, c, C, hOK, ?_⟩
  have hQReg : S11Q2QReg d s q β ρ₀ 1 (d / 2 + 8) εstar r c₀ c C := by
    intro _ _ _ _ _ _ _ _ _ f0 hf0 ρ hρ' N hN T hT K hK hfree
    obtain ⟨-, D, cc, B, R⟩ := hall f0 hf0 ρ hρ'
    have hprob : ∀ t, 0 ≤ t → HRS.Whole.IsProbDensity (ρ t) := fun t ht =>
      (HRS.MS.MovEnt.s66_class_props hNL hf0 hρ' hc₀.le t ht).1
    exact s11q3_QReg_of_Reg hd hs0 hsd hβ R hprob hN T K hK hfree
  exact s11q2_localized_of_cores hd hs0 hs hβ hq hρ hC hc₀ hNL (s11q2_liouville d s q β) hQReg

end HRS.MS.S21H2W13
