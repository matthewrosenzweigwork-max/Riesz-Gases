import HRS.MC.CepH0Aux2

/-!
# Packet CEPH0, auxiliary 3: the log-likelihood ratio of a mixture with disjoint supports
-/

open MeasureTheory InformationTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.CepH0

section KL

variable {α : Type*} [MeasurableSpace α] {ι : Type*} [Fintype ι]

theorem h0_llr_ae [DecidableEq ι] (ρ : Measure α) [IsProbabilityMeasure ρ] (C : ι → Set α)
    (hCm : ∀ c, MeasurableSet (C c)) (hCd : Pairwise fun c c' => Disjoint (C c) (C c'))
    (ν : ι → Measure α) [∀ c, IsProbabilityMeasure (ν c)] (hν : ∀ c, ν c (C c)ᶜ = 0)
    (p : ι → ℝ) (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) (c : ι) (hc : 0 < p c)
    (hμρ : h0mix p ν ≪ ρ) (hνρ : ν c ≪ ρ) :
    ∀ᵐ x ∂(ν c), llr (h0mix p ν) ρ x = llr (ν c) ρ x + Real.log (p c) := by
  haveI := h0mix_prob p hp0 hp1 ν
  have hres := h0_restrict_mix C hCd ν hν p c (hCm c)
  have hμ : ρ.withDensity ((h0mix p ν).rnDeriv ρ) = h0mix p ν := Measure.withDensity_rnDeriv_eq _ _ hμρ
  have hνc : ρ.withDensity ((ν c).rnDeriv ρ) = ν c := Measure.withDensity_rnDeriv_eq _ _ hνρ
  have hq : ENNReal.ofReal (p c) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hνres : (ν c).restrict (C c) = ν c :=
    Measure.restrict_eq_self_of_ae_mem (by
      rw [ae_iff]; exact hν c)
  have h1 : (ρ.restrict (C c)).withDensity ((h0mix p ν).rnDeriv ρ)
      = (ρ.restrict (C c)).withDensity (ENNReal.ofReal (p c) • (ν c).rnDeriv ρ) := by
    rw [← restrict_withDensity (hCm c), hμ, hres, withDensity_smul' _ _ hq,
      ← restrict_withDensity (hCm c), hνc, hνres]
  have h2 : (h0mix p ν).rnDeriv ρ =ᵐ[ρ.restrict (C c)] ENNReal.ofReal (p c) • (ν c).rnDeriv ρ :=
    (withDensity_eq_iff_of_sigmaFinite (Measure.measurable_rnDeriv _ _).aemeasurable
      ((Measure.measurable_rnDeriv _ _).const_smul _).aemeasurable).mp h1
  have hacr : ν c ≪ ρ.restrict (C c) := by
    have : ν c = (ρ.restrict (C c)).withDensity ((ν c).rnDeriv ρ) := by
      rw [← restrict_withDensity (hCm c), hνc, hνres]
    rw [this]
    exact withDensity_absolutelyContinuous _ _
  have h3 := hacr.ae_le h2
  have h4 : ∀ᵐ x ∂(ν c), 0 < (ν c).rnDeriv ρ x := Measure.rnDeriv_pos hνρ
  have h5 : ∀ᵐ x ∂(ν c), (ν c).rnDeriv ρ x < ⊤ := hνρ.ae_le (Measure.rnDeriv_lt_top _ _)
  filter_upwards [h3, h4, h5] with x hx3 hx4 hx5
  simp only [llr]
  rw [hx3, Pi.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hp0 c),
    Real.log_mul hc.ne' (ENNReal.toReal_pos hx4.ne' hx5.ne).ne', add_comm]

end KL

end HRS.MC.CepH0
