import HRS.PDE.MovCAux6
import HRS.Appendix.B15CAux3

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movc_klDiv_conv {α : Type*} [MetricSpace α] [CompactSpace α] [MeasurableSpace α]
    [BorelSpace α] (Pm : Measure α) [SigmaFinite Pm] {ν : Measure α} [IsProbabilityMeasure ν]
    {Q : Measure α} {Qn : ℕ → Measure α} [IsProbabilityMeasure Q] [∀ n, IsProbabilityMeasure (Qn n)]
    (dd : α → ℝ) (dn : ℕ → α → ℝ) (hm : Measurable dd) (hmn : ∀ n, Measurable (dn n))
    (hpos : ∀ x, 0 < dd x) (hposn : ∀ n x, 0 < dn n x)
    (hQ : Q = Pm.withDensity fun x => ENNReal.ofReal (dd x))
    (hQn : ∀ n, Qn n = Pm.withDensity fun x => ENNReal.ofReal (dn n x))
    (cn : ℕ → ℝ) (hcn : Tendsto cn atTop (𝓝 1)) (hcn0 : ∀ n, 0 < cn n)
    (hle : ∀ n, ∀ᵐ x ∂Pm, cn n * dd x ≤ dn n x)
    (hw : ∀ φ : α → ℝ, Continuous φ →
      Tendsto (fun n => ∫ x, φ x ∂(Qn n)) atTop (𝓝 (∫ x, φ x ∂Q)))
    (hfin : InformationTheory.klDiv ν Q ≠ ⊤) :
    (∀ n, InformationTheory.klDiv ν (Qn n) ≠ ⊤) ∧
      Tendsto (fun n => (InformationTheory.klDiv ν (Qn n)).toReal) atTop
        (𝓝 (InformationTheory.klDiv ν Q).toReal) := by
  have hna : ∫⁻ x, ENNReal.ofReal (dd x) ∂Pm = 1 := by
    have := measure_univ (μ := Q)
    rw [hQ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
    exact this
  have hnb : ∀ n, ∫⁻ x, ENNReal.ofReal (dn n x) ∂Pm = 1 := fun n => by
    have := measure_univ (μ := Qn n)
    rw [hQn n, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
    exact this
  have hmain : ∀ n, InformationTheory.klDiv ν (Qn n) ≠ ⊤ ∧
      (InformationTheory.klDiv ν (Qn n)).toReal ≤
        (InformationTheory.klDiv ν Q).toReal - Real.log (cn n) := by
    intro n
    have := b15c_klDiv_withDensity_le Pm ν dd (dn n) hm (hmn n) (Eventually.of_forall hpos)
      (Eventually.of_forall (hposn n)) hna (hnb n) (hcn0 n) (hle n) (by rw [← hQ]; exact hfin)
    rw [← hQ, ← hQn n] at this
    exact this
  refine ⟨fun n => (hmain n).1, ?_⟩
  -- ENNReal convergence
  have hlow : InformationTheory.klDiv ν Q ≤ liminf (fun n => InformationTheory.klDiv ν (Qn n)) atTop :=
    b15b_klDiv_liminf_le (Pn := fun _ => ν) (fun φ _ => tendsto_const_nhds) hw
  set ub : ℕ → ℝ := fun n => (InformationTheory.klDiv ν Q).toReal - Real.log (cn n) with hub
  have hubt : Tendsto ub atTop (𝓝 (InformationTheory.klDiv ν Q).toReal) := by
    have h1 : Tendsto (fun n => Real.log (cn n)) atTop (𝓝 (Real.log 1)) :=
      (Real.continuousAt_log one_ne_zero).tendsto.comp hcn
    simpa [hub] using (tendsto_const_nhds (x := (InformationTheory.klDiv ν Q).toReal)).sub h1
  have hup : limsup (fun n => InformationTheory.klDiv ν (Qn n)) atTop ≤ InformationTheory.klDiv ν Q := by
    have hle' : ∀ n, InformationTheory.klDiv ν (Qn n) ≤ ENNReal.ofReal (ub n) := fun n =>
      (ENNReal.le_ofReal_iff_toReal_le (hmain n).1
        (ENNReal.toReal_nonneg.trans (hmain n).2)).2 (hmain n).2
    have hT : Tendsto (fun n => ENNReal.ofReal (ub n)) atTop
        (𝓝 (ENNReal.ofReal (InformationTheory.klDiv ν Q).toReal)) :=
      (ENNReal.tendsto_ofReal hubt)
    rw [ENNReal.ofReal_toReal hfin] at hT
    calc _ ≤ limsup (fun n => ENNReal.ofReal (ub n)) atTop := limsup_le_limsup (Eventually.of_forall hle')
      _ = _ := hT.limsup_eq
  have hconv : Tendsto (fun n => InformationTheory.klDiv ν (Qn n)) atTop (𝓝 (InformationTheory.klDiv ν Q)) :=
    tendsto_of_le_liminf_of_limsup_le hlow hup
  exact (ENNReal.tendsto_toReal hfin).comp hconv

end HRS
