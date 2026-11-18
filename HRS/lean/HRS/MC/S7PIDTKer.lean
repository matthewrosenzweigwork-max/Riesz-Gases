import HRS.MC.S7PIDTVec
import HRS.MC.S7PIDPPoly
import HRS.MC.S7PIDIIncr

/-!
# Packet PI-D, sub-packet T (part 8): measurability and bounds of the causal kernel in `u`
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDT

open HRS HRS.Sec7 HRS.MC.Sec7.PID HRS.MC.Sec7.PIE

variable {d : ℕ}

theorem S7PIDT_ker (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ c c' : ℝ, 0 ≤ c → c ≤ c' → c' ≤ T → ∀ (e : NegSobolev d m) (t : ℝ),
      c ≤ t → t ≤ c' →
      AEStronglyMeasurable (fun u => causalVec R.D R.ρ m t u e) (volume.restrict (Set.Ioc c c')) ∧
        ∀ u ∈ Set.Ioc c c', ‖causalVec R.D R.ρ m t u e‖ ≤ Cb * ‖e‖ := by
  obtain ⟨J, n₀, H, hn₀, hJ, hm0, hm1⟩ := HRS.MC.Sec7.S7PIDP.S7PIDP_pie R m hm T hT
  have P : PIEData J R.D R.ρ T m n₀ := ⟨H, hn₀, hJ, hm0, hm1⟩
  obtain ⟨Cb, hCb0, hCb⟩ := pie_Vbound H m n₀ hn₀ hJ hm0 hm1
  refine ⟨Cb, hCb0, fun c c' hc hcc hc' e t hct htc' => ⟨?_, ?_⟩⟩
  · by_cases ht0 : t = 0
    · refine (aestronglyMeasurable_const (b := (0 : NegSobolev d m))).congr ?_
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu => ?_)
      have : ¬ u ≤ t := by
        intro h; have := hu.1; rw [ht0] at h; linarith
      show (0 : NegSobolev d m) = causalVec R.D R.ρ m t u e
      unfold causalVec
      rw [if_neg this]
    · have htpos : 0 < t := lt_of_le_of_ne (hc.trans hct) (Ne.symm ht0)
      have htm : t ∈ Set.Ioc 0 T := ⟨htpos, htc'.trans hc'⟩
      have hind : (fun u => causalVec R.D R.ρ m t u e) =
          (Set.Iic t).indicator (fun u => Vprop R.D R.ρ m t u e) := by
        funext u
        unfold causalVec
        by_cases h : u ≤ t
        · rw [if_pos h, Set.indicator_of_mem (show u ∈ Set.Iic t from h)]
        · rw [if_neg h, Set.indicator_of_notMem (show u ∉ Set.Iic t from h)]
      rw [hind, aestronglyMeasurable_indicator_iff measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
      have := pie_V_aesm P htm (S := Set.Iic t ∩ Set.Ioc c c') (measurableSet_Iic.inter measurableSet_Ioc)
        (fun u hu => ⟨hc.trans hu.2.1.le, hu.1⟩) (b := fun _ => e) aestronglyMeasurable_const
      exact this
  · intro u hu
    unfold causalVec
    by_cases h : u ≤ t
    · rw [if_pos h]
      have hu0 : 0 < u := lt_of_le_of_lt hc hu.1
      exact hCb t ⟨hu0.trans_le h, htc'.trans hc'⟩ u ⟨hu0.le, h⟩ e
    · rw [if_neg h, norm_zero]
      positivity

end HRS.MC.Sec7.S7PIDT

end
