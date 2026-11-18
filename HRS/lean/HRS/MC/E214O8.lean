import HRS.MC.E214O7
import HRS.MC.E214M3

/-!
# Packet E214O, part 8: `Kwin_relax_cond_proof`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214O

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan

variable {d : ℕ}

theorem o_eLpNorm_three {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] (μ : Measure Ω) (f : Ω → E)
    (hf : AEStronglyMeasurable f μ) (hint : Integrable (fun ω => ‖f ω‖ ^ 3) μ) {C : ℝ}
    (hC : ∫ ω, ‖f ω‖ ^ 3 ∂μ ≤ C) : eLpNorm f 3 μ ≤ ENNReal.ofReal (C ^ (1 / 3 : ℝ)) := by
  have := o_eLpNorm_of_moment μ f hf (q := 3) (by norm_num) (by simpa [Real.rpow_ofNat] using hint)
    (by simpa [Real.rpow_ofNat] using hC)
  simpa using this

theorem o_eLpNorm_two {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] (μ : Measure Ω) (f : Ω → E)
    (hf : AEStronglyMeasurable f μ) (hint : Integrable (fun ω => ‖f ω‖ ^ 2) μ) {C : ℝ}
    (hC : ∫ ω, ‖f ω‖ ^ 2 ∂μ ≤ C) : eLpNorm f 2 μ ≤ ENNReal.ofReal (C ^ (1 / 2 : ℝ)) := by
  have := o_eLpNorm_of_moment μ f hf (q := 2) (by norm_num) (by simpa [Real.rpow_ofNat] using hint)
    (by simpa [Real.rpow_ofNat] using hC)
  simpa using this

section Moments

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m}

theorem o_mom_Z3 (gd : GaussData S β₀ hE) (T : ℝ) (hT : 0 < T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : ℝ, 0 ≤ a → AEStronglyMeasurable (gd.Zwin T a) gd.P₀ ∧
      eLpNorm (gd.Zwin T a) 3 gd.P₀ ≤ ENNReal.ofReal M := by
  obtain ⟨C, hC0, hC⟩ := HRS.MC.E213U11.u11_Z_moment gd T hT 3 (by norm_num)
  refine ⟨C ^ (1 / 3 : ℝ), by positivity, fun a ha => ?_⟩
  obtain ⟨hm, hi, hb⟩ := hC a ha
  exact ⟨hm, o_eLpNorm_three gd.P₀ _ hm (by simpa [Real.rpow_ofNat] using hi)
    (by simpa [Real.rpow_ofNat] using hb)⟩

theorem o_mom_Z2 (gd : GaussData S β₀ hE) (T : ℝ) (hT : 0 < T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : ℝ, 0 ≤ a → AEStronglyMeasurable (gd.Zwin T a) gd.P₀ ∧
      eLpNorm (gd.Zwin T a) 2 gd.P₀ ≤ ENNReal.ofReal M := by
  obtain ⟨C, hC0, hC⟩ := HRS.MC.E213U11.u11_Z_moment gd T hT 2 (by norm_num)
  refine ⟨C ^ (1 / 2 : ℝ), by positivity, fun a ha => ?_⟩
  obtain ⟨hm, hi, hb⟩ := hC a ha
  exact ⟨hm, o_eLpNorm_two gd.P₀ _ hm (by simpa [Real.rpow_ofNat] using hi)
    (by simpa [Real.rpow_ofNat] using hb)⟩

theorem o_mom_D3 (gd : GaussData S β₀ hE) (T : ℝ) (hT : 0 < T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : ℝ, 0 ≤ a → AEStronglyMeasurable (gd.Dwin T a) gd.P₀ ∧
      eLpNorm (gd.Dwin T a) 3 gd.P₀ ≤ ENNReal.ofReal M := by
  obtain ⟨C, hC0, hC⟩ := HRS.MC.E213U11.u11_D_moment3 hE gd T hT
  refine ⟨C ^ (1 / 3 : ℝ), by positivity, fun a ha => ?_⟩
  obtain ⟨hi, hb⟩ := hC a ha
  have hm := HRS.MC.E213U11.u11_Dwin_aesm gd T hT a ha
  exact ⟨hm, o_eLpNorm_three gd.P₀ _ hm hi hb⟩

set_option maxHeartbeats 800000 in
theorem o_mom_J2 (gd : GaussData S β₀ hE) (T : ℝ) (hT : 0 < T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ a : ℝ, 0 ≤ a → AEStronglyMeasurable (gd.Jwin T a) gd.P₀ ∧
      eLpNorm (gd.Jwin T a) 2 gd.P₀ ≤ ENNReal.ofReal M := by
  obtain ⟨C, hC0, hC⟩ := HRS.MC.E213U11.u11_J_moment2 hE gd T hT
  refine ⟨C ^ (1 / 2 : ℝ), by positivity, fun a ha => ?_⟩
  obtain ⟨hi, hb⟩ := hC a ha
  have hm := (HRS.MC.E213U11.u11_Jwin_aesm_mem gd T hT a ha).1
  exact ⟨hm, o_eLpNorm_two (E := TensorDual (PathSpace d m T) 2) gd.P₀ (gd.Jwin T a) hm hi hb⟩

theorem o_init_decay (S : PreparedData d) (β₀ : ℝ) (hE : EdgeworthHyp S β₀ m) (T : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ a : ℝ, 0 ≤ a →
      ‖pushforward3 (Iwin S β₀ hE T a) (Kinit0 S β₀)‖ ≤ C * Real.exp (-c * a) := by
  obtain ⟨CI, c, hCI, hc, hI⟩ := Classical.choose_spec (exists_Iwin S β₀ hE T)
  refine ⟨CI ^ 3 * ‖Kinit0 S β₀‖ + 1, c, by positivity, hc, fun a ha => ?_⟩
  have h1 : ‖Iwin S β₀ hE T a‖ ≤ CI * Real.exp (-c * a) := (hI a ha).2
  have he0 : 0 < Real.exp (-c * a) := Real.exp_pos _
  have he1 : Real.exp (-c * a) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have h2 : ‖Iwin S β₀ hE T a‖ ^ 3 ≤ (CI * Real.exp (-c * a)) ^ 3 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 3
  have h3 : (CI * Real.exp (-c * a)) ^ 3 ≤ CI ^ 3 * Real.exp (-c * a) := by
    rw [mul_pow]
    have : Real.exp (-c * a) ^ 3 ≤ Real.exp (-c * a) := by
      nlinarith [mul_pos he0 he0, mul_nonneg he0.le he0.le]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  refine (HRS.MC.E213U11.u11_norm_pushforward3_apply_le (Iwin S β₀ hE T a) (Kinit0 S β₀)).trans ?_
  calc ‖Iwin S β₀ hE T a‖ ^ 3 * ‖Kinit0 S β₀‖ ≤ CI ^ 3 * Real.exp (-c * a) * ‖Kinit0 S β₀‖ :=
        mul_le_mul_of_nonneg_right (h2.trans h3) (norm_nonneg (Kinit0 S β₀))
    _ ≤ (CI ^ 3 * ‖Kinit0 S β₀‖ + 1) * Real.exp (-c * a) := by nlinarith [mul_nonneg (norm_nonneg (Kinit0 S β₀)) he0.le]

end Moments

end HRS.MC.E214O

end
