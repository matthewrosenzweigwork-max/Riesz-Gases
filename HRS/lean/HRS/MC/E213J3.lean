import HRS.MC.S7PIDTKer
import HRS.MC.E213I2

/-!
# Packet E213J3: family-quantified `S7PIDT_ker` (Theorem 2.13, translation-uniform PI-D)

The constant `Cb` of the causal kernel is chosen before the shift `b ≥ 0`; the regimes are `E213F.shift R b hb` at the
fixed horizon `G`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213J

open HRS HRS.Sec7 HRS.MC.Sec7.PID HRS.MC.Sec7.PIE

variable {d : ℕ}

theorem e213j_ker (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (G : ℝ) (hG : 0 < G) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ b : ℝ, ∀ hb : 0 ≤ b,
      ∀ c c' : ℝ, 0 ≤ c → c ≤ c' → c' ≤ G → ∀ (e : NegSobolev d m) (t : ℝ),
      c ≤ t → t ≤ c' →
      AEStronglyMeasurable (fun u => causalVec (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ m t u e)
          (volume.restrict (Set.Ioc c c')) ∧
        ∀ u ∈ Set.Ioc c c', ‖causalVec (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ m t u e‖ ≤
          Cb * ‖e‖ := by
  obtain ⟨k0, hk1, hk2, hk3, hkst, -⟩ := HRS.MC.Sec7.S7PIDV.S7PIDV_hyp R m hm 1 one_pos
  obtain ⟨L, Ac, Am, Cb, hL, hAc, hAm1, hCb, hU⟩ :=
    HRS.MC.E213I.e213i_V_unif_shift R k0 hk1 hkst m hk2 hk3 G hG
  obtain ⟨Rg, MB, Λ, VB, ν₀, hbundle⟩ := HRS.MC.E213F.adjointData_uniform R (k0 + 3)
  have hd1 : 1 ≤ d := by have := R.hd; omega
  have hn₀ : 1 ≤ k0 + 2 := by omega
  have hJ : k0 + 2 + 1 ≤ k0 + 3 := le_rfl
  have hm0 : ((k0 + 2 : ℕ) : ℝ) < m := by push_cast; exact hk2
  have hm1 : m ≤ ((k0 + 2 : ℕ) : ℝ) + 1 := by push_cast; linarith
  refine ⟨Cb, hCb, fun b₀ hb₀ => ?_⟩
  have H : PIEHyp (k0 + 3) (HRS.MC.E213F.shift R b₀ hb₀).D (HRS.MC.E213F.shift R b₀ hb₀).ρ G :=
    ⟨hd1, by omega, Rg, MB, Λ, VB, ν₀, hbundle G hG b₀ hb₀⟩
  set Rb := HRS.MC.E213F.shift R b₀ hb₀ with hRb
  have P : PIEData (k0 + 3) Rb.D Rb.ρ G m (k0 + 2) := ⟨H, hn₀, hJ, hm0, hm1⟩
  refine fun c c' hc hcc hc' e t hct htc' => ⟨?_, ?_⟩
  · by_cases ht0 : t = 0
    · refine (aestronglyMeasurable_const (b := (0 : NegSobolev d m))).congr ?_
      refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu => ?_)
      have : ¬ u ≤ t := by
        intro h; have := hu.1; rw [ht0] at h; linarith
      show (0 : NegSobolev d m) = causalVec Rb.D Rb.ρ m t u e
      unfold causalVec
      rw [if_neg this]
    · have htpos : 0 < t := lt_of_le_of_ne (hc.trans hct) (Ne.symm ht0)
      have htm : t ∈ Set.Ioc 0 G := ⟨htpos, htc'.trans hc'⟩
      have hind : (fun u => causalVec Rb.D Rb.ρ m t u e) =
          (Set.Iic t).indicator (fun u => Vprop Rb.D Rb.ρ m t u e) := by
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
      exact (hU b₀ hb₀ u u t hu0.le le_rfl h (htc'.trans hc')).2.1 e
    · rw [if_neg h, norm_zero]
      positivity

end HRS.MC.E213J

end
