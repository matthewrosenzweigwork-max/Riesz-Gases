import HRS.Main.A8PAux48

/-!
# Packet A8P, part 49: the zero set of a continuous function is small if `∫ G_ε''` is
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

theorem a8pG1''_le {ε : ℝ} (hε : 0 < ε) (z : ℝ) : a8pG1'' ε z ≤ 1 / ε := by
  unfold a8pG1''
  have hs : ε ≤ Real.sqrt (ε ^ 2 + z ^ 2) := by
    calc ε = Real.sqrt (ε ^ 2) := (Real.sqrt_sq hε.le).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg z])
  have hs3 : ε ^ 3 ≤ Real.sqrt (ε ^ 2 + z ^ 2) ^ 3 := pow_le_pow_left₀ hε.le hs 3
  rw [div_le_div_iff₀ (by positivity) hε]
  nlinarith [hs3, sq_nonneg ε]

theorem a8pG1'_cont {ε : ℝ} (hε : 0 < ε) : Continuous (a8pG1' ε) := by
  unfold a8pG1'
  refine continuous_id.div ((continuous_const.add (continuous_id.pow 2)).sqrt) (fun z => ?_)
  exact (Real.sqrt_pos.2 (a8pG1_pos hε z)).ne'

theorem a8pG1''_cont {ε : ℝ} (hε : 0 < ε) : Continuous (a8pG1'' ε) := by
  unfold a8pG1''
  refine continuous_const.div (((continuous_const.add (continuous_id.pow 2)).sqrt).pow 3) (fun z => ?_)
  have := Real.sqrt_pos.2 (a8pG1_pos hε z)
  positivity

theorem a8p_small_set {g : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hg : ContinuousOn g (Set.Icc 0 T)) {ε : ℝ}
    (hε : 0 < ε) :
    volume {s : ℝ | s ∈ Set.Icc 0 T ∧ g s = 0} ≤
      ENNReal.ofReal (8 * ε * ∫ s in Set.Icc (0 : ℝ) T, a8pG1'' ε (g s)) := by
  set S : Set ℝ := {s : ℝ | s ∈ Set.Icc 0 T ∧ |g s| ≤ ε} with hS
  have hSm : MeasurableSet S := by
    have hc : ContinuousOn (fun s => |g s|) (Set.Icc 0 T) := hg.abs
    have hcl := hc.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Iic (a := ε))
    have : S = Set.Icc 0 T ∩ (fun s => |g s|) ⁻¹' Set.Iic ε := by
      ext s; simp [hS]
    rw [this]
    exact hcl.measurableSet
  have hsub : {s : ℝ | s ∈ Set.Icc 0 T ∧ g s = 0} ⊆ S := fun s hs => ⟨hs.1, by simp [hs.2, hε.le]⟩
  refine (measure_mono hsub).trans ?_
  have hcont : ContinuousOn (fun s => a8pG1'' ε (g s)) (Set.Icc 0 T) := by
    refine ContinuousOn.congr (f := fun s => ε ^ 2 / Real.sqrt (ε ^ 2 + g s ^ 2) ^ 3) ?_ (fun s _ => rfl)
    refine continuousOn_const.div ?_ (fun s _ => ?_)
    · exact ((continuousOn_const.add (hg.pow 2)).sqrt).pow 3
    · have := Real.sqrt_pos.2 (a8pG1_pos hε (g s))
      positivity
  have hint : IntegrableOn (fun s => a8pG1'' ε (g s)) (Set.Icc 0 T) := by
    have hK : IsCompact (Set.Icc (0 : ℝ) T) := isCompact_Icc
    exact hcont.integrableOn_compact hK
  have hle : ∀ s ∈ S, 1 ≤ ENNReal.ofReal (8 * ε * a8pG1'' ε (g s)) := by
    intro s hs
    have h8 := a8pG1''_ge hε hs.2
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have : 1 ≤ 8 * ε * (1 / (8 * ε)) := by field_simp; rfl
    calc (1 : ℝ) ≤ 8 * ε * (1 / (8 * ε)) := this
      _ ≤ 8 * ε * a8pG1'' ε (g s) := mul_le_mul_of_nonneg_left h8 (by positivity)
  calc volume S = ∫⁻ s in S, 1 := by simp
    _ ≤ ∫⁻ s in S, ENNReal.ofReal (8 * ε * a8pG1'' ε (g s)) := setLIntegral_mono' hSm hle
    _ ≤ ∫⁻ s in Set.Icc 0 T, ENNReal.ofReal (8 * ε * a8pG1'' ε (g s)) := by
        refine lintegral_mono_set ?_
        exact fun s hs => hs.1
    _ = ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) T, 8 * ε * a8pG1'' ε (g s)) := by
        rw [ofReal_integral_eq_lintegral_ofReal (hint.const_mul (8 * ε))
          (Filter.Eventually.of_forall fun s => by
            have := a8pG1''_nonneg hε (g s); positivity)]
    _ = _ := by rw [integral_const_mul]

end HRS.Main.A8P
