import HRS.MC.S7FCW9
import HRS.MC.S7UCDefs

/-!
# S7UCAC: the half-line field `B` (UC-C)

`s7_UC_C_field_proof`: take the `t`-free field `B` of the proved C4 (`s7_FC_C4_field_all_t_proof`, Wick for every `t ≥ 0`,
moments uniform in `t ≥ 0`); Tonelli on `(ω,t) ↦ ‖B (a+t) ω‖²` over `[0,T]` as in `S7FCW15.lean`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7UCA

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.S7FCH4
open HRS.MC.Sec7.UCPlan

variable {d : ℕ}

theorem s7_UC_C_field_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η : ℝ → Ω' → NegSobolev d r)
    (hη : IsGaussianLimitField R.D R.ρ (withDensityReal R.ρ₀) R.β₀ r P' η) :
    ∃ B : ℝ → Ω' → NegSobolev d r, UCField R r P' η B := by
  obtain ⟨B, hBm, hWick, hMom⟩ := HRS.MC.Sec7.S7FCW9.s7_FC_C4_field_all_t_proof R r hr P' η hη
  obtain ⟨C, hC⟩ := hMom 2 (by norm_num)
  simp only [Real.rpow_two] at hC
  refine ⟨B, hBm, ?_, ?_⟩
  · exact (ae_restrict_iff' measurableSet_Ici).2 (Eventually.of_forall fun t ht => hWick t ht)
  intro T hT a ha
  have hG : Measurable (fun p : Ω' × ℝ => ENNReal.ofReal (‖B (a + p.2) p.1‖ ^ 2)) := by
    have h1 : Measurable (fun p : Ω' × ℝ => B (a + p.2) p.1) :=
      hBm.comp ((measurable_const.add measurable_snd).prodMk measurable_fst)
    exact ENNReal.measurable_ofReal.comp ((continuous_norm.measurable.comp h1).pow_const 2)
  have hinner : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ENNReal.ofReal (‖B (a + t) ω‖ ^ 2) ∂P' ≤ ENNReal.ofReal C := by
    intro t ht
    obtain ⟨hi, hle⟩ := hC (a + t) (add_nonneg ha ht.1)
    have hnn : 0 ≤ᵐ[P'] fun ω => ‖B (a + t) ω‖ ^ 2 := ae_of_all _ fun ω => sq_nonneg _
    exact (ofReal_integral_eq_lintegral_ofReal hi hnn).symm.trans_le (ENNReal.ofReal_le_ofReal hle)
  have hfin : ∫⁻ _ in Set.Icc (0 : ℝ) T, ENNReal.ofReal C ≠ ⊤ := by
    rw [setLIntegral_const, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hsw : ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal (‖B (a + t) ω‖ ^ 2)) ∂P' ≤
      ∫⁻ _ in Set.Icc (0 : ℝ) T, ENNReal.ofReal C := by
    refine (lintegral_lintegral_swap (f := fun ω t => ENNReal.ofReal (‖B (a + t) ω‖ ^ 2))
      hG.aemeasurable).trans_le ?_
    exact lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Icc hinner)
  have hae : ∀ᵐ ω ∂P', ∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal (‖B (a + t) ω‖ ^ 2) < ⊤ := by
    have hm : Measurable (fun ω => ∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal (‖B (a + t) ω‖ ^ 2)) :=
      hG.lintegral_prod_right'
    exact ae_lt_top hm (ne_top_of_le_ne_top hfin hsw)
  filter_upwards [hae] with ω hω
  have hmeas : Measurable (fun t : ℝ => B (a + t) ω) :=
    hBm.comp ((measurable_const.add measurable_id).prodMk measurable_const)
  have haesm : AEStronglyMeasurable (fun t : ℝ => B (a + t) ω) (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    hmeas.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm haesm]
  exact ⟨(hmeas.norm.pow_const 2).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun t => sq_nonneg _)).2 hω⟩

end HRS.MC.Sec7.S7UCA

end
