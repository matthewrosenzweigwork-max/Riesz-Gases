import HRS.MS.SA12K16

/-!
# S.A.12 L8: reduction to two pointwise statements

`weak_operator_convergence` follows from (i) a uniform pointwise decay `|W_L(x)| ≤ c ⟨x⟩^{-(d+3)}` of the periodic
weak operator and of the limit weak operator, and (ii) its locally uniform pointwise convergence.  The `ℓ¹(L²)`
bookkeeping is done here (`sa12y_cell_decay`, `sa12k_cell_small`); (i) and (ii) are the remaining analysis.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd

variable {d : ℕ}

/-- The conclusion of `weak_operator_convergence` from pointwise decay and local uniform convergence. -/
theorem sa12k_L8_of_pointwise (hd : 1 ≤ d) (t : ℝ) (Lmin : ℝ)
    (Wp : ℝ → ℝ → ℝ → Euc d → ℝ) (Wl : ℝ → Euc d → ℝ)
    (hdec : ∃ c : ℝ, 0 ≤ c ∧ ∀ L : ℝ, Lmin ≤ L → ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) 1 → ∀ σ ∈ Icc (0 : ℝ) t,
      ∀ x, |Wp L ε σ x| ≤ c * jbracket x ^ (-((d : ℝ) + 3)))
    (hldec : ∃ c : ℝ, 0 ≤ c ∧ ∀ σ ∈ Icc (0 : ℝ) t, ∀ x, |Wl σ x| ≤ c * jbracket x ^ (-((d : ℝ) + 3)))
    (hconv : ∀ (R δ : ℝ), 0 < δ → ∃ L₁ ε₀ : ℝ, 0 < ε₀ ∧ ∀ L : ℝ, L₁ ≤ L → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ σ ∈ Icc (0 : ℝ) t, ∀ x : Euc d, ‖x‖ ≤ R → |Wp L ε σ x - Wl σ x| ≤ δ) :
    (∃ K : ℝ, ∀ L : ℝ, Lmin ≤ L → ∀ ε : ℝ, ε ∈ Ioc (0 : ℝ) 1 → ∀ σ ∈ Icc (0 : ℝ) t,
      cellL2Sum (Wp L ε σ) ≤ ENNReal.ofReal K) ∧
    ∀ δ : ℝ, 0 < δ → ∃ L₁ ε₀ : ℝ, 0 < ε₀ ∧ ∀ L : ℝ, L₁ ≤ L → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ σ ∈ Icc (0 : ℝ) t, cellL2Sum (fun x => Wp L ε σ x - Wl σ x) ≤ ENNReal.ofReal δ := by
  obtain ⟨c₁, hc₁, h₁⟩ := hdec
  obtain ⟨c₂, hc₂, h₂⟩ := hldec
  obtain ⟨CA, hCA, hcell⟩ := sa12y_cell_decay (d := d) hd
  refine ⟨⟨CA * c₁, fun L hL ε hε σ hσ => hcell _ c₁ hc₁ (h₁ L hL ε hε σ hσ)⟩, fun δ hδ => ?_⟩
  obtain ⟨R, η₀, hη₀, hsmall⟩ := sa12k_cell_small hd (c₁ + c₂) (by positivity) δ hδ
  obtain ⟨L₁, ε₀, hε₀, hc⟩ := hconv R η₀ hη₀
  refine ⟨max L₁ Lmin, min ε₀ 1, lt_min hε₀ one_pos, fun L hL ε hε hεle σ hσ => ?_⟩
  refine hsmall _ (fun x => ?_) (fun x hx => ?_)
  · have e := h₁ L ((le_max_right _ _).trans hL) ε ⟨hε, hεle.trans (min_le_right _ _)⟩ σ hσ x
    have e2 := h₂ σ hσ x
    calc |Wp L ε σ x - Wl σ x| ≤ |Wp L ε σ x| + |Wl σ x| := abs_sub _ _
      _ ≤ (c₁ + c₂) * jbracket x ^ (-((d : ℝ) + 3)) := by linarith
  · exact hc L ((le_max_left _ _).trans hL) ε hε (hεle.trans (min_le_left _ _)) σ hσ x hx

end HRS.MH.AdjointRd.Phase2SA12Limit
