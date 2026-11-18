import HRS.MS.S113X2A2f

/-!
# S11.3 X2 part A3a: abstract `L¹` convergence of Radon-Nikodym derivatives of an increasing sequence of measures
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MS.S113X2

variable {α : Type*} [MeasurableSpace α]

theorem s113a_rnDeriv_decomp {μ ν Q : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν] [SigmaFinite Q]
    (hle : ν ≤ μ) :
    μ.rnDeriv Q =ᵐ[Q] fun x => ν.rnDeriv Q x + (μ - ν).rnDeriv Q x := by
  haveI : IsFiniteMeasure (μ - ν) := isFiniteMeasure_of_le μ Measure.sub_le
  have h := Measure.rnDeriv_add ν (μ - ν) Q
  rw [add_comm ν, Measure.sub_add_cancel_of_le hle] at h
  exact h

/-- `ν ≤ μ` gives `dν/dQ ≤ dμ/dQ` a.e. -/
theorem s113a_rnDeriv_mono {μ ν Q : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν] [SigmaFinite Q]
    (hle : ν ≤ μ) : ν.rnDeriv Q ≤ᵐ[Q] μ.rnDeriv Q := by
  filter_upwards [s113a_rnDeriv_decomp (Q := Q) hle] with x hx
  rw [hx]; exact le_self_add

/-- **`L¹` convergence.**  If finite measures `ν_n ≤ μ` have masses tending to the mass of `μ` and each `ν_n ≪ Q`
(`Q` σ-finite), then `μ ≪ Q` and `dν_n/dQ → dμ/dQ` in `L¹(Q)`. -/
theorem s113a_L1_of_mass {μ Q : Measure α} [IsFiniteMeasure μ] [SigmaFinite Q] {ν : ℕ → Measure α}
    [∀ n, IsFiniteMeasure (ν n)] (hle : ∀ n, ν n ≤ μ) (hmass : Tendsto (fun n => ν n Set.univ) atTop (𝓝 (μ Set.univ)))
    (hac : ∀ n, ν n ≪ Q) :
    μ ≪ Q ∧ Tendsto (fun n => ∫⁻ x, ‖((ν n).rnDeriv Q x).toReal - (μ.rnDeriv Q x).toReal‖ₑ ∂Q) atTop (𝓝 0) := by
  have hdef : Tendsto (fun n => μ Set.univ - ν n Set.univ) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := μ Set.univ)) hmass (Or.inl (measure_ne_top _ _))
    simpa using this
  have hsub : ∀ n, (μ - ν n) Set.univ = μ Set.univ - ν n Set.univ := fun n =>
    Measure.sub_apply MeasurableSet.univ (hle n)
  have hμQ : μ ≪ Q := by
    intro A hA
    have hAm : ∃ B, MeasurableSet B ∧ A ⊆ B ∧ Q B = 0 := by
      obtain ⟨B, hAB, hB, hQB⟩ := exists_measurable_superset_of_null hA
      exact ⟨B, hB, hAB, hQB⟩
    obtain ⟨B, hB, hAB, hQB⟩ := hAm
    refine le_antisymm ?_ bot_le
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hev : ∀ᶠ n in atTop, μ Set.univ - ν n Set.univ < ε := hdef.eventually (gt_mem_nhds hε)
    obtain ⟨n, hn⟩ := hev.exists
    have h1 : ν n B = 0 := hac n hQB
    have h2 : μ B = ν n B + (μ - ν n) B := by
      conv_lhs => rw [← Measure.sub_add_cancel_of_le (hle n)]
      rw [Measure.add_apply, add_comm]
    calc μ A ≤ μ B := measure_mono hAB
      _ ≤ ν n B + (μ - ν n) B := h2.le
      _ ≤ 0 + (μ - ν n) Set.univ := by rw [h1]; exact add_le_add le_rfl (measure_mono (Set.subset_univ _))
      _ ≤ 0 + ε := by rw [hsub n]; exact add_le_add le_rfl hn.le
  refine ⟨hμQ, ?_⟩
  have hbound : ∀ n, ∫⁻ x, ‖((ν n).rnDeriv Q x).toReal - (μ.rnDeriv Q x).toReal‖ₑ ∂Q ≤
      μ Set.univ - ν n Set.univ := by
    intro n
    haveI : IsFiniteMeasure (μ - ν n) := isFiniteMeasure_of_le μ Measure.sub_le
    have hae : ∀ᵐ x ∂Q, ‖((ν n).rnDeriv Q x).toReal - (μ.rnDeriv Q x).toReal‖ₑ = (μ - ν n).rnDeriv Q x := by
      filter_upwards [s113a_rnDeriv_decomp (Q := Q) (hle n), Measure.rnDeriv_lt_top μ Q,
        Measure.rnDeriv_lt_top (μ - ν n) Q, Measure.rnDeriv_lt_top (ν n) Q] with x h1 h2 h3 h4
      rw [h1, ENNReal.toReal_add h4.ne h3.ne]
      have e : (((ν n).rnDeriv Q x).toReal - (((ν n).rnDeriv Q x).toReal + ((μ - ν n).rnDeriv Q x).toReal)) =
        -(((μ - ν n).rnDeriv Q x).toReal) := by ring
      rw [e, Real.enorm_eq_ofReal_abs, abs_neg, abs_of_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal h3.ne]
    rw [lintegral_congr_ae hae, ← hsub n]
    exact Measure.lintegral_rnDeriv_le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdef (fun _ => bot_le) hbound

end HRS.MS.S113X2

end
