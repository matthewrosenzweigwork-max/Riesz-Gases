import HRS.MC.E213U13k

/-!
# E213U13l: moments of the window drift `D_a` of all orders
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U13

section DMoment

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213U11

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem gd_D_integrable_pow (T : ℝ) (hT : 0 < T) (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a →
      Integrable (fun ω => ‖gd.Dwin T a ω‖ ^ n) gd.P₀ := by
  obtain ⟨K, c, hK, hc, hpt⟩ := u11_D_pointwise hE gd T hT
  obtain ⟨A, hA0, hA⟩ := u11_weights_bound c T hc hT
  obtain ⟨CB, hCB0, hCB⟩ := u11_B_moment gd 1 one_pos (n : ℝ) (by exact_mod_cast hn)
  refine ⟨K ^ n * (A ^ n * CB), by positivity, fun a ha => ?_⟩
  have hY := fun k : ℕ => hCB (k : ℝ) (Nat.cast_nonneg k)
  obtain ⟨hI, hM⟩ := u11_wsum_moment (P := gd.P₀) ⌈a + T⌉₊ (fun k => Real.exp (-c * (a - ((k : ℝ) + 1))))
    (fun k ω => ‖toL2 (rLvl d) 1 (fun t => gd.B ((k : ℝ) + t) ω)‖) (fun k => (Real.exp_pos _).le)
    (fun k ω => norm_nonneg _) (fun k => (hY k).1.norm) n hn CB
    (fun k => by simpa [Real.rpow_natCast] using (hY k).2.1)
    (fun k => by simpa [Real.rpow_natCast] using (hY k).2.2)
  have hDm : AEMeasurable (fun ω => ‖gd.Dwin T a ω‖ ^ n) gd.P₀ :=
    (u11_Dwin_aesm gd T hT a ha).norm.aemeasurable.pow_const n
  have hb : ∀ᵐ ω ∂gd.P₀, ‖gd.Dwin T a ω‖ ^ n ≤ K ^ n * (∑ k ∈ Finset.range ⌈a + T⌉₊,
      Real.exp (-c * (a - ((k : ℝ) + 1))) * ‖toL2 (rLvl d) 1 (fun t => gd.B ((k : ℝ) + t) ω)‖) ^ n := by
    filter_upwards [hpt a ha] with ω h
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h n
  refine (hI.const_mul (K ^ n)).mono' hDm.aestronglyMeasurable ?_
  filter_upwards [hb] with ω h
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  exact h

theorem gd_D_memLp (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (r : ℝ) (hr : 1 ≤ r) :
    MemLp (gd.Dwin T a) (ENNReal.ofReal r) gd.P₀ := by
  set n : ℕ := ⌈r⌉₊ with hn
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 (by
    have : 0 < ⌈r⌉₊ := Nat.ceil_pos.2 (by linarith)
    omega)
  have hrn : r ≤ (n : ℝ) := Nat.le_ceil r
  obtain ⟨C, -, hC⟩ := gd_D_integrable_pow gd T hT n hn1
  have hmeas := (u11_Dwin_aesm gd T hT a ha)
  have hn0 : (n : ℝ) = (ENNReal.ofReal (n : ℝ)).toReal := by
    rw [ENNReal.toReal_ofReal (by positivity)]
  have hMem : MemLp (gd.Dwin T a) (ENNReal.ofReal (n : ℝ)) gd.P₀ := by
    refine (integrable_norm_rpow_iff hmeas (by simp; omega) ENNReal.ofReal_ne_top).1 ?_
    rw [ENNReal.toReal_ofReal (by positivity)]
    simpa [Real.rpow_natCast] using hC a ha
  exact hMem.mono_exponent (ENNReal.ofReal_le_ofReal hrn)

end DMoment

end HRS.MC.E213U13
