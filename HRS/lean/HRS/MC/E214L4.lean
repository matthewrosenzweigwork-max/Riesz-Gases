import HRS.MC.E214PD
import HRS.MC.E214L1
import HRS.MC.E214H3

/-!
# Packet E214L, part 4: `Zwin_relax`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214L

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan

variable {d : ℕ}

theorem eLpNorm_le_of_lintegral_rpow {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (f : Ω → E) (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp0 : 0 < p) {x : ℝ} (hx : 0 ≤ x)
    (h : ∫⁻ ω, ‖f ω‖ₑ ^ p ∂μ ≤ ENNReal.ofReal (x ^ p)) : eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal x := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; exact hp0) (by simp) hf, ENNReal.toReal_ofReal hp0.le]
  calc (∫⁻ ω, ‖f ω‖ₑ ^ p ∂μ) ^ (1 / p) ≤ (ENNReal.ofReal (x ^ p)) ^ (1 / p) :=
        ENNReal.rpow_le_rpow h (by positivity)
    _ = ENNReal.ofReal x := by
        rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), one_div,
          ENNReal.rpow_rpow_inv hp0.ne']

section ZwinRelax

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} {sd : StatDatum S β₀ m hE}

theorem Zwin_relax_proof (pg : PairGD sd) (T : ℝ) (hT : 0 < T) (p : ℝ) (hp : 2 ≤ p) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ a : ℝ, 0 ≤ a →
      eLpNorm (fun ω => pg.gd.Zwin T a ω - pg.gds.Zwin T a ω) (ENNReal.ofReal p) pg.P ≤
        ENNReal.ofReal (C * Real.exp (-c * a)) := by
  obtain ⟨C, κ, hC, hκ, H⟩ := pg.path_sup T hT p hp
  refine ⟨C, κ, hC, hκ, fun a ha => ?_⟩
  have hp0 : 0 < p := by linarith
  obtain ⟨-, -, -, hη, hηs, -⟩ := id pg.pair
  have hae : ∀ᵐ ω ∂pg.P, ‖pg.gd.Zwin T a ω - pg.gds.Zwin T a ω‖ₑ ≤
      ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖pg.η (a + t) ω - pg.ηs (a + t) ω‖ₑ := by
    filter_upwards [(hη (a + T)).cont, (hηs (a + T)).cont] with ω h1 h2
    exact HRS.MC.E214H.enorm_epath_sub_le (rLvl_le hE) ha pg.η pg.ηs ω h1 h2
  have hlin : ∫⁻ ω, ‖pg.gd.Zwin T a ω - pg.gds.Zwin T a ω‖ₑ ^ p ∂pg.P ≤
      ENNReal.ofReal ((C * Real.exp (-κ * a)) ^ p) :=
    (lintegral_mono_ae (hae.mono fun ω h => ENNReal.rpow_le_rpow h hp0.le)).trans (H a ha)
  have hm1 := (HRS.MC.E213U11.u11_Z_moment pg.gd T hT 1 le_rfl).choose_spec.2 a ha
  have hm2 := (HRS.MC.E213U11.u11_Z_moment pg.gds T hT 1 le_rfl).choose_spec.2 a ha
  exact eLpNorm_le_of_lintegral_rpow _ _ (hm1.1.sub hm2.1) hp0 (by positivity) hlin

end ZwinRelax

end HRS.MC.E214L

end
