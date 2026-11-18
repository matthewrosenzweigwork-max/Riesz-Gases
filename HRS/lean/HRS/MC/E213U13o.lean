import HRS.MC.E213U13n

/-!
# Packet e213u13, file o: the relocated statement `chaos_data`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U13

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

section Final

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem chaos_data_proof (T : ℝ) (hT : 0 < T) :
    ∃ ξ : ℕ → gd.Ω₀ → ℝ, IsStdGaussianSeq gd.P₀ ξ ∧ ∀ a : ℝ, 0 ≤ a →
      IsCenteredGaussian (law gd.P₀ (gd.Zwin T a)) ∧ InFirstChaos gd.P₀ ξ 2 (gd.Zwin T a) ∧
      (∀ q : ℝ, 3 ≤ q → InSecondChaos gd.P₀ ξ q (gd.Dwin T a)) ∧
      (∀ q : ℝ, 2 ≤ q → InFirstChaos gd.P₀ ξ q (gd.JwinP T a)) := by
  obtain ⟨ξ, hm, hξ, hX⟩ := gd_exists_xi gd
  exact ⟨ξ, hξ, fun a ha => ⟨gd_Z_gaussian gd hX T hT a ha, gd_Z_chaos gd hX T hT a ha le_rfl,
    fun q hq => gd_D_chaos gd hX T hT a ha (by linarith),
    fun q hq => gd_J_chaos gd hX T hT a ha hq⟩⟩

end Final

end HRS.MC.E213U13

end
