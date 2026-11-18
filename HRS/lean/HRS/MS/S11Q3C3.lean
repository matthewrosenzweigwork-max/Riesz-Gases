import HRS.MS.S11Q3C2
import HRS.MS.S11Q2C8

/-!
# S11.3 / S11.4 (worker S11Q3), C3: `r2_moving_Lp` and `r2_moving_moment_transfer` without any hypothesis on the moving reference

`s11q3_QReg_of_data`: the core `S11Q2QReg` holds for the constants constructed in S6.3 (tuple of `s11q3_class_data`), by `s11q3_QReg_of_Reg`.
`s11q3_cores_tuple`, `s11q3_r2_moving_Lp`, `s11q3_r2_moving_moment_transfer`: the frozen types, from the (proved) `S113XLiouville` only.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.S11Q3

open HRS HRS.Whole HRS.MS.S113BD HRS.MS.S113X2C HRS.MS.S11Q2

variable {d : ℕ}

theorem s11q3_cores_tuple (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (β q : ℝ) (hβ : 0 < β)
    (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) :
    ∃ j m : ℕ, 1 ≤ j ∧ (d : ℝ) / 2 + j + 6 < m ∧
      ∃ εstar r c₀ c C₁ : ℝ, S113XTupleOK d s q β ρ₀ j m εstar r c₀ c C₁ ∧
        S113XLocalizedI d s q β ρ₀ j m εstar r c₀ := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  set m : ℕ := ⌊(d : ℝ) / 2⌋₊ + 8 with hm
  have hmm : (d : ℝ) / 2 + (1 : ℕ) + 6 < m := by
    have := Nat.lt_floor_add_one ((d : ℝ) / 2)
    simp only [hm]; push_cast; linarith
  have hm3 : (d : ℝ) / 2 + 3 < m := by
    have : ((1 : ℕ) : ℝ) = 1 := by simp
    linarith
  obtain ⟨εstar, r, c₀, c, C, hε, hr, hc₀, hc, hC, hNL, hall⟩ :=
    s11q3_class_data hd hs0 hsd β q hβ hq 1 m le_rfl hmm hm3 ρ₀ hρ
  have hOK : S113XTupleOK d s q β ρ₀ 1 m εstar r c₀ c C :=
    ⟨hε, hr, hc₀, hc, hC, hNL, fun f0 hf0 ρ hρ' => (hall f0 hf0 ρ hρ').1⟩
  refine ⟨1, m, le_rfl, hmm, εstar, r, c₀, c, C, hOK, ?_⟩
  have hQReg : S11Q2QReg d s q β ρ₀ 1 m εstar r c₀ c C := by
    intro _ _ _ _ _ _ _ _ _ f0 hf0 ρ hρ' N hN T hT K hK hfree
    obtain ⟨-, D, cc, B, R⟩ := hall f0 hf0 ρ hρ'
    have hprob : ∀ t, 0 ≤ t → HRS.Whole.IsProbDensity (ρ t) := fun t ht =>
      (HRS.MS.MovEnt.s66_class_props hNL hf0 hρ' hc₀.le t ht).1
    exact s11q3_QReg_of_Reg hd hs0 hsd hβ R hprob hN T K hK hfree
  exact s11q2_localized_of_cores hd hs0 hs hβ hq hρ hC hc₀ hNL (s11q2_liouville d s q β) hQReg

theorem s11q3_r2_moving_Lp {d : ℕ} (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (β q : ℝ)
    (hβ : 0 < β) (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) (γ : ℝ) (hγ : 0 ≤ γ)
    (hγs : 0 < s → 0 < γ) :
    type_of% (HRS.Whole.r2_moving_Lp hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs) :=
  s113c_r2_moving_Lp_of_X2 hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs
    (s11q3_cores_tuple hd s hs0 hs β q hβ hq ρ₀ hρ)

theorem s11q3_r2_moving_moment_transfer {d : ℕ} (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (β q : ℝ) (hβ : 0 < β) (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) (γ : ℝ)
    (hγ : 0 ≤ γ) (hγs : 0 < s → 0 < γ) :
    type_of% (HRS.Whole.r2_moving_moment_transfer hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs) :=
  s113c_r2_moving_moment_transfer_of_X2 hd s hs0 hs β q hβ hq ρ₀ hρ γ hγ hγs
    (s11q3_cores_tuple hd s hs0 hs β q hβ hq ρ₀ hρ)

end HRS.MS.S11Q3

end
