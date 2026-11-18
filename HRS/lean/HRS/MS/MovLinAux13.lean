import HRS.MS.MovLinAux12

/-!
# MOV-LIN, part 4: from short-time smoothing and `L²` decay to `MovSmoothingBounds`

Namespace `HRS.MS.MovLin`, helpers `movlin_`.  Infrastructure for S6.2 (`W:lem:r2mov-linear`); not a manuscript row.

* `movlin_L2_osc`: for `w ∈ L²`, `MemOsc 0 w`, `oscNorm 0 w = ‖w‖` and `ofFun 0 w = Φ⁻¹ w`.
* `movlin_dec_level`: abstract: a semigroup `U` on `L²_0` with `‖U(t)‖ ≤ C₀ e^{-λt}` and the short-time smoothing hypothesis
  `HsOK` (`Σ^{ρ'} → Σ^σ`, `0 ≤ ρ' ≤ σ`, `0 < t ≤ 1`, constant `C t^{-(σ-ρ')/2}`) decays at every level `r ≥ 0`.
* `movlin_abstract`: the same data give `MovSmoothingBounds d s ρ m λ C U` for every `m ≥ a`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovLin

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1

variable {d : ℕ}

section Abstract

lemma movlin_L2_osc (w : Lp ℝ 2 (volume : Measure (Euc d))) :
    MemOsc 0 (⇑w : Euc d → ℝ) ∧ oscNorm 0 (⇑w : Euc d → ℝ) = ‖w‖ ∧
      OscSpace.ofFun 0 (⇑w : Euc d → ℝ) = (mov2d_Phi d).symm w := by
  have hf : MemLp (⇑w : Euc d → ℝ) 2 (volume : Measure (Euc d)) := Lp.memLp w
  have hfo : MemOsc 0 (⇑w : Euc d → ℝ) := ⟨hf, by simpa using mov2b_coeff_sq_summable hf⟩
  have hP : OscSpace.ofFun 0 (⇑w : Euc d → ℝ) = (mov2d_Phi d).symm w := by
    rw [LinearIsometryEquiv.eq_symm_apply, mov2d_Phi_ofFun hf]
    exact Lp.toLp_coeFn w hf
  refine ⟨hfo, ?_, hP⟩
  rw [← OscSpace.norm_ofFun _ hfo, hP, LinearIsometryEquiv.norm_map]

/-- Hypothesis of short-time smoothing for a family `U` on `L²_0`. -/
def HsOK {ρ : Euc d → ℝ} (U : ℝ → (MovL2Zero ρ →L[ℝ] MovL2Zero ρ)) : Prop :=
  ∀ ρ' σ : ℝ, 0 ≤ ρ' → ρ' ≤ σ → ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ v : MovL2Zero ρ,
    MemOsc ρ' (movFun v) → MemOsc σ (movFun (U t v)) ∧
      oscNorm σ (movFun (U t v)) ≤ C * t ^ (-((σ - ρ') / 2)) * oscNorm ρ' (movFun v)

variable {ρ : Euc d → ℝ}

lemma movlin_norm_osc0 (v : MovL2Zero ρ) : MemOsc 0 (movFun v) ∧ oscNorm 0 (movFun v) = ‖v‖ :=
  ⟨(movlin_L2_osc (v : Lp ℝ 2 (volume : Measure (Euc d)))).1,
    (movlin_L2_osc (v : Lp ℝ 2 (volume : Measure (Euc d)))).2.1⟩

end Abstract

end HRS.MS.MovLin
