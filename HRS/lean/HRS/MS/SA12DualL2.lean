import HRS.MH.AdjointRdDefs
import HRS.Whole.AppendixAAdjoint

/-!
# S.A.12: Cauchy–Schwarz and duality for `L²(ℝ^d)` against smooth compactly supported tests
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

variable {d : ℕ}

theorem sa12x_inner_toLp {f g : Euc d → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

/-- Cauchy–Schwarz in `L²`. -/
theorem sa12x_cs {f g : Euc d → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    |∫ x, f x * g x| ≤ (eLpNorm f 2 volume).toReal * (eLpNorm g 2 volume).toReal := by
  rw [← sa12x_inner_toLp hf hg]
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [Lp.norm_toLp, Lp.norm_toLp]

/-- Duality: a function paired boundedly against all smooth compactly supported tests has `L²` norm at
most the bound. -/
theorem sa12x_dual {h : Euc d → ℝ} (hh : MemLp h 2 volume) {A : ℝ} (hA : 0 ≤ A)
    (hpair : ∀ ψ : Euc d → ℝ, IsCcInfty ψ →
      |∫ x, h x * ψ x| ≤ A * (eLpNorm ψ 2 volume).toReal) :
    eLpNorm h 2 volume ≤ ENNReal.ofReal A := by
  set hL : Lp ℝ 2 (volume : Measure (Euc d)) := hh.toLp h with hhL
  have hclosed : IsClosed {g : Lp ℝ 2 (volume : Measure (Euc d)) | |inner ℝ hL g| ≤ A * ‖g‖} :=
    isClosed_le (continuous_const.inner continuous_id).abs (continuous_const.mul continuous_norm)
  have hdense := MeasureTheory.Lp.dense_hasCompactSupport_contDiff (F := ℝ) (E := Euc d)
    (μ := (volume : Measure (Euc d))) (p := 2) (by simp)
  have hsub : {f : Lp ℝ 2 (volume : Measure (Euc d)) |
      ∃ g : Euc d → ℝ, f =ᵐ[volume] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g} ⊆
      {g | |inner ℝ hL g| ≤ A * ‖g‖} := by
    rintro f ⟨g, hfg, hg1, hg2⟩
    have hgm : MemLp g 2 volume := hg2.continuous.memLp_of_hasCompactSupport hg1
    have hfe : f = hgm.toLp g := (Lp.ext (hfg.trans hgm.coeFn_toLp.symm))
    show |inner ℝ hL f| ≤ A * ‖f‖
    rw [hfe, hhL, sa12x_inner_toLp hh hgm, Lp.norm_toLp]
    exact hpair g ⟨hg2, hg1⟩
  have hall : (closure {f : Lp ℝ 2 (volume : Measure (Euc d)) |
      ∃ g : Euc d → ℝ, f =ᵐ[volume] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g}) = Set.univ :=
    hdense.closure_eq
  have hself : |inner ℝ hL hL| ≤ A * ‖hL‖ := by
    have : hL ∈ closure {f : Lp ℝ 2 (volume : Measure (Euc d)) |
        ∃ g : Euc d → ℝ, f =ᵐ[volume] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g} := by
      rw [hall]; trivial
    exact closure_minimal hsub hclosed this
  have hn : ‖hL‖ ≤ A := by
    rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at hself
    by_cases h0 : ‖hL‖ = 0
    · rw [h0]; exact hA
    · have hpos : 0 < ‖hL‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      nlinarith
  have : eLpNorm h 2 volume = ENNReal.ofReal ‖hL‖ := by
    rw [hhL, Lp.norm_toLp, ENNReal.ofReal_toReal hh.eLpNorm_ne_top]
  rw [this]
  exact ENNReal.ofReal_le_ofReal hn

end HRS.MH.AdjointRd.Phase2SA12Limit
