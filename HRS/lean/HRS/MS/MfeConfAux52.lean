import HRS.MS.MfeConfAux51

/-!
# S.B.1, packet F6 (part 14): the free energy of the mollified law is a relative entropy; lower semicontinuity

* `sb1_free_klDiv`: for `u = G_v * ν` and a reference `q = exp(-U/θ)` of total mass one,
  `klDiv (u dx) (q dx) ≠ ⊤` and `(klDiv ..).toReal = ∫ (u log u + u U/θ)`;
* `sb1_lsc_mol`: `klDiv μ Q ≤ liminf klDiv (G_{v_n} * μ) Q` for any probability reference `Q` (no confinement needed).
-/

open MeasureTheory Filter Topology InformationTheory
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section
variable {v θ : ℝ} {ν : Measure (EucConfig d N)}

theorem sb1_mol_lintegral (hv : 0 < v) [IsProbabilityMeasure ν] :
    ∫⁻ x, ENNReal.ofReal (p4Mol v ν x) = 1 := p4j_mol_lintegral_one hv ν

theorem sb1_free_klDiv (hv : 0 < v) (hθ : 0 < θ) [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν) {M CV : ℝ}
    (hMν : ∫ y, p4m_q y ∂ν ≤ M) (hM : 0 ≤ M) (hCV : 0 ≤ CV) {U : EucConfig d N → ℝ} (hUc : Continuous U)
    (hU : ∀ x, |U x| ≤ CV * (1 + p4m_q x))
    (hZ : ∫⁻ x, ENNReal.ofReal (Real.exp (-θ⁻¹ * U x)) = 1) :
    klDiv (sb1Dm (p4Mol v ν)) (sb1Dm (fun x => Real.exp (-θ⁻¹ * U x))) ≠ ⊤ ∧
      (klDiv (sb1Dm (p4Mol v ν)) (sb1Dm (fun x => Real.exp (-θ⁻¹ * U x)))).toReal =
        ∫ x, (p4Mol v ν x * Real.log (p4Mol v ν x) + p4Mol v ν x * U x / θ) := by
  have hcu := p4m_cont_u hv hm (ν := ν)
  have hpos := fun x => p4m_mol_pos hv hm x (ν := ν)
  have hint := sb1_integrable_free hv hθ hm hMν hM hCV hUc hU
  have hΦ : Integrable (fun x => p4Mol v ν x * (Real.log (p4Mol v ν x) -
      Real.log (Real.exp (-θ⁻¹ * U x)))) := by
    refine hint.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.log_exp]
    field_simp
    ring
  have hqm : Measurable (fun x => Real.exp (-θ⁻¹ * U x)) :=
    Real.measurable_exp.comp (hUc.measurable.const_mul _)
  obtain ⟨h1, h2⟩ := sb1_klDiv_density (q := fun x => Real.exp (-θ⁻¹ * U x)) hcu.measurable
    (fun x => (hpos x).le) (sb1_mol_lintegral hv) hqm (fun x => Real.exp_pos _) hZ hΦ
  refine ⟨h1, h2.trans ?_⟩
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Real.log_exp]
  field_simp
  ring

theorem sb1_lsc_mol [IsProbabilityMeasure ν] {Q : Measure (EucConfig d N)} [IsProbabilityMeasure Q]
    {w : ℕ → ℝ} (hw : ∀ n, 0 < w n) (hw0 : Tendsto w atTop (𝓝 0)) :
    klDiv ν Q ≤ liminf (fun n => klDiv (sb1Dm (p4Mol (w n) ν)) Q) atTop := by
  haveI : ∀ n, IsProbabilityMeasure (p4m_molMeas (w n) ν) := fun n => p4m_molMeas_prob (hw n) ν
  exact p4m_klDiv_liminf (μn := fun n => p4m_molMeas (w n) ν) (fun ψ hψ hb => by
    obtain ⟨C, hC⟩ := hb
    exact p4m_molMeas_tendsto ν hw hw0 hψ hC)

end

end HRS.MS.MfeConf
