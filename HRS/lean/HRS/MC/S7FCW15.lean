import HRS.MC.S7FCW9

/-!
# S7FCW15: relocated proof of `s7_FC_C_limit_field` (FC-C, the limit field on `[0,T]`)

The statement is copied verbatim from `HRS/MC/Sec7Spec.lean` (namespace `HRS.MC.Sec7`, line 568); it is proved here in
namespace `HRS.MC.Sec7.S7FCW15` and tied to the frozen statement in `HRS/MC/S7FCW15Tie.lean`.

Route.  Take the `t`-free field `B` of the proved C4 (`HRS.MC.Sec7.S7FCW9.s7_FC_C4_field_all_t_proof`).  Its Wick
conjunct holds for every `t ≥ 0`, so it holds for a.e. `t ∈ [0,T]`.  For the `L²([0,T];E_r)` conjunct, Tonelli applied
to `(ω,t) ↦ ‖B t ω‖²` (jointly measurable) and the C4 bound with `q = 2` give `E ∫_0^T ‖B t‖² dt ≤ C T < ∞`, hence
`∫_0^T ‖B t ω‖² dt < ∞` for a.e. `ω`; the time section is a.e. strongly measurable since `B` is jointly measurable,
and `NegSobolev d r` is second countable (`NegSobolev.instSCNeg`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCW15

open HRS HRS.Sec7 HRS.MC.SEdge

variable {d : ℕ}

/-- Proof of `HRS.MC.Sec7.s7_FC_C_limit_field` (verbatim statement). -/
theorem s7_FC_C_limit_field_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η : ℝ → Ω' → NegSobolev d r) (hη : IsGaussianLimitField R.D R.ρ (withDensityReal R.ρ₀) R.β₀ r P' η) :
    ∃ B : ℝ → Ω' → NegSobolev d r, Measurable (Function.uncurry B) ∧
      (∀ᵐ ω ∂P', MemLp (fun t => B t ω) 2 (volume.restrict (Set.Icc (0 : ℝ) T))) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        IsWickQuadraticField R.D.s P' (fun ω => η t ω) (withDensityReal (R.ρ t)) (B t)) := by
  obtain ⟨B, hBm, hWick, hMom⟩ := HRS.MC.Sec7.S7FCW9.s7_FC_C4_field_all_t_proof R r hr P' η hη
  obtain ⟨C, hC⟩ := hMom 2 (by norm_num)
  simp only [Real.rpow_two] at hC
  -- joint measurability of `(ω, t) ↦ ‖B t ω‖²` (as an `ℝ≥0∞`-valued function on `Ω' × ℝ`)
  have hG : Measurable (fun p : Ω' × ℝ => ENNReal.ofReal (‖B p.2 p.1‖ ^ 2)) := by
    have h1 : Measurable (fun p : Ω' × ℝ => B p.2 p.1) :=
      hBm.comp (measurable_snd.prodMk measurable_fst)
    exact ENNReal.measurable_ofReal.comp ((continuous_norm.measurable.comp h1).pow_const 2)
  -- the time integral of the squared norm is bounded by `C` times the length of `[0,T]` in expectation
  have hinner : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ENNReal.ofReal (‖B t ω‖ ^ 2) ∂P' ≤ ENNReal.ofReal C := by
    intro t ht
    obtain ⟨hi, hle⟩ := hC t ht.1
    have hnn : 0 ≤ᵐ[P'] fun ω => ‖B t ω‖ ^ 2 := ae_of_all _ fun ω => sq_nonneg _
    exact (ofReal_integral_eq_lintegral_ofReal hi hnn).symm.trans_le (ENNReal.ofReal_le_ofReal hle)
  have hfin : ∫⁻ _ in Set.Icc (0 : ℝ) T, ENNReal.ofReal C ≠ ⊤ := by
    rw [setLIntegral_const, Real.volume_Icc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  -- Tonelli
  have hsw : ∫⁻ ω, (∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal (‖B t ω‖ ^ 2)) ∂P' ≤
      ∫⁻ _ in Set.Icc (0 : ℝ) T, ENNReal.ofReal C := by
    refine (lintegral_lintegral_swap (f := fun ω t => ENNReal.ofReal (‖B t ω‖ ^ 2)) hG.aemeasurable).trans_le ?_
    exact lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Icc hinner)
  have hae : ∀ᵐ ω ∂P', ∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal (‖B t ω‖ ^ 2) < ⊤ := by
    have hm : Measurable (fun ω => ∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal (‖B t ω‖ ^ 2)) :=
      hG.lintegral_prod_right'
    exact ae_lt_top hm (ne_top_of_le_ne_top hfin hsw)
  refine ⟨B, hBm, ?_, ?_⟩
  · filter_upwards [hae] with ω hω
    have hmeas : Measurable (fun t : ℝ => B t ω) := hBm.comp (measurable_id.prodMk measurable_const)
    have haesm : AEStronglyMeasurable (fun t : ℝ => B t ω) (volume.restrict (Set.Icc (0 : ℝ) T)) :=
      hmeas.aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq_norm haesm]
    exact ⟨(hmeas.norm.pow_const 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun t => sq_nonneg _)).2 hω⟩
  · exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun t ht => hWick t ht.1)

end HRS.MC.Sec7.S7FCW15

end
