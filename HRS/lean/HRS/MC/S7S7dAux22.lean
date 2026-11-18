import HRS.MC.S7S7dAux21
import HRS.MC.S7S7b

/-!
# Packet `s7_S7d_uniform_limits`, helper 22: the constants of the mode data and an `L^1` bound from `L^2`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7d

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux

variable {d : ℕ} {s : ℝ} {r : ℝ}

theorem s7d_b_pos (k : NonzeroLattice d) : 0 < s7_b k := by
  unfold s7_b; have := Torus.jp_pos k.1; positivity

theorem s7d_b_summable : Summable (fun k : NonzeroLattice d => s7_b k) :=
  HRS.MC.Sec7.S7c.s7c_summable_jp (r := (d : ℝ) + 3) (by linarith)

theorem s7d_mode_bounds (hr : r = 2 * (d : ℝ) + 6) {γ : ℝ} {ρ : Torus d → ℝ}
    {a : NonzeroLattice d → Torus d → ℝ} {v : NonzeroLattice d → Fin d → Torus d → ℝ} {C₀ : ℝ}
    (hmode : s7_ModeData d s γ ρ r a v C₀) :
    ∃ C₀' Cd : ℝ, 0 < C₀' ∧ 0 ≤ Cd ∧ (∀ j x, |a j x| ≤ C₀' * s7_b j) ∧
      (∀ k l x, |sed_drift (v k) (s7_phi r l) x| ≤ Cd * (s7_b k * s7_b l)) ∧
      (∀ k j, HRS.KernelGrad.IsLipschitz (C₀' * s7_b k) (v k j)) := by
  set C₀' : ℝ := max C₀ 1 with hC₀'
  have hC₀'pos : 0 < C₀' := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨C₀', d * max C₀ 0 * (2 * Real.sqrt 2), hC₀'pos, by positivity, fun j x => ?_,
    fun k l x => HRS.MC.Sec7.S7b.s7b_drift_bound hr hmode.smooth_v hmode.bound_v k l x, fun k j => ?_⟩
  · have h1 := HRS.PDE.R2Aux.abs_le_cbNorm (HRS.Q66.q66_isCk_of_smooth (hmode.smooth_a j) 1) x
    exact h1.trans ((hmode.bound_a j).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (s7d_b_pos j).le))
  · intro x y
    have h := HRS.PDE.R2Aux.isLipschitz_of_cbNorm
      (HRS.Q66.q66_isCk_of_smooth (hmode.smooth_v k j) 1) x y
    refine h.trans ?_
    have : Torus.cbNorm 1 (v k j) ≤ C₀' * s7_b k :=
      (hmode.bound_v k j).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (s7d_b_pos k).le)
    exact mul_le_mul_of_nonneg_right this (HRS.KernelGrad.tdist_nonneg x y)

/-- `∫ |Y| ≤ (1 + C) T / 2` when `∫ Y² ≤ C T²`. -/
theorem s7d_L1_of_L2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : Ω → ℝ} (hY : Measurable Y) (hY2 : Integrable (fun ω => Y ω ^ 2) P) {C T : ℝ}
    (hC : ∫ ω, Y ω ^ 2 ∂P ≤ C * T ^ 2) (hT : 0 < T) :
    Integrable (fun ω => |Y ω|) P ∧ ∫ ω, |Y ω| ∂P ≤ (1 + C) * T / 2 := by
  have hpt : ∀ ω, |Y ω| ≤ (T + Y ω ^ 2 / T) / 2 := by
    intro ω
    have h2 : Y ω ^ 2 = |Y ω| ^ 2 := (sq_abs _).symm
    rw [h2, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have : T + |Y ω| ^ 2 / T - 2 * |Y ω| = (T - |Y ω|) ^ 2 / T := by field_simp; ring
    have h3 : 0 ≤ (T - |Y ω|) ^ 2 / T := by positivity
    linarith
  have hbd : Integrable (fun ω => (T + Y ω ^ 2 / T) / 2) P :=
    ((integrable_const T).add (hY2.div_const T)).div_const 2
  have hI : Integrable (fun ω => |Y ω|) P :=
    hbd.mono' hY.abs.aestronglyMeasurable (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_abs]; exact hpt ω)
  refine ⟨hI, ?_⟩
  calc ∫ ω, |Y ω| ∂P ≤ ∫ ω, (T + Y ω ^ 2 / T) / 2 ∂P := integral_mono hI hbd hpt
    _ = (T + (∫ ω, Y ω ^ 2 ∂P) / T) / 2 := by
        rw [integral_div, integral_add (integrable_const T) (hY2.div_const T), integral_div,
          integral_const]
        simp
    _ ≤ (1 + C) * T / 2 := by
        have : (∫ ω, Y ω ^ 2 ∂P) / T ≤ C * T := by
          rw [div_le_iff₀ hT]; nlinarith
        linarith

end HRS.MC.Sec7.S7d

end
