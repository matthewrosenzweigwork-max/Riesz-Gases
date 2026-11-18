import HRS.MC.CepH0Aux3

/-!
# Packet CEPH0, auxiliary 4: Kullback-Leibler divergence of a mixture with disjoint supports
-/

open MeasureTheory InformationTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.CepH0

section KL

variable {α : Type*} [MeasurableSpace α] {ι : Type*} [Fintype ι]

theorem h0_klDiv_mix_top [DecidableEq ι] (ρ : Measure α) [IsProbabilityMeasure ρ] (C : ι → Set α)
    (hCm : ∀ c, MeasurableSet (C c)) (hCd : Pairwise fun c c' => Disjoint (C c) (C c'))
    (ν : ι → Measure α) [∀ c, IsProbabilityMeasure (ν c)] (hν : ∀ c, ν c (C c)ᶜ = 0)
    (p : ι → ℝ) (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1)
    (h : ∃ c, 0 < p c ∧ klDiv (ν c) ρ = ⊤) : klDiv (h0mix p ν) ρ = ⊤ := by
  by_contra hne
  obtain ⟨hac, hint⟩ := klDiv_ne_top_iff.mp hne
  obtain ⟨c, hc, htop⟩ := h
  have hνρ : ν c ≪ ρ := (h0_mix_ac_iff ρ p ν).mp hac c hc
  have hnint : ¬ Integrable (llr (ν c) ρ) (ν c) := fun hi =>
    (klDiv_ne_top hνρ hi) htop
  apply hnint
  have h1 : Integrable (llr (h0mix p ν) ρ) (ENNReal.ofReal (p c) • ν c) :=
    hint.mono_measure (h0_smul_le_mix p ν c)
  have h2 : Integrable (llr (h0mix p ν) ρ) (ν c) :=
    (integrable_smul_measure (by simpa using hc) ENNReal.ofReal_ne_top).mp h1
  have h3 := h0_llr_ae ρ C hCm hCd ν hν p hp0 hp1 c hc hac hνρ
  have h4 : Integrable (fun x => llr (h0mix p ν) ρ x - Real.log (p c)) (ν c) :=
    h2.sub (integrable_const _)
  refine h4.congr ?_
  filter_upwards [h3] with x hx
  rw [hx]; ring

theorem h0_klDiv_mix_finite [DecidableEq ι] (ρ : Measure α) [IsProbabilityMeasure ρ] (C : ι → Set α)
    (hCm : ∀ c, MeasurableSet (C c)) (hCd : Pairwise fun c c' => Disjoint (C c) (C c'))
    (ν : ι → Measure α) [∀ c, IsProbabilityMeasure (ν c)] (hν : ∀ c, ν c (C c)ᶜ = 0)
    (p : ι → ℝ) (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1)
    (h : ∀ c, 0 < p c → klDiv (ν c) ρ ≠ ⊤) :
    klDiv (h0mix p ν) ρ ≠ ⊤ ∧ (klDiv (h0mix p ν) ρ).toReal =
      ∑ c, p c * (klDiv (ν c) ρ).toReal + ∑ c, p c * Real.log (p c) := by
  haveI := h0mix_prob p hp0 hp1 ν
  have hνρ : ∀ c, 0 < p c → ν c ≪ ρ ∧ Integrable (llr (ν c) ρ) (ν c) :=
    fun c hc => klDiv_ne_top_iff.mp (h c hc)
  have hac : h0mix p ν ≪ ρ := (h0_mix_ac_iff ρ p ν).mpr fun c hc => (hνρ c hc).1
  -- integrability of `llr μ ρ` on each piece
  have hpiece : ∀ c, Integrable (llr (h0mix p ν) ρ) (ENNReal.ofReal (p c) • ν c) := by
    intro c
    by_cases hc : 0 < p c
    · refine (integrable_smul_measure (by simpa using hc) ENNReal.ofReal_ne_top).mpr ?_
      have h3 := h0_llr_ae ρ C hCm hCd ν hν p hp0 hp1 c hc hac (hνρ c hc).1
      refine ((hνρ c hc).2.add (integrable_const (Real.log (p c)))).congr ?_
      filter_upwards [h3] with x hx
      exact hx.symm
    · rw [ENNReal.ofReal_of_nonpos (not_lt.mp hc), zero_smul]
      exact integrable_zero_measure
  have hint : Integrable (llr (h0mix p ν) ρ) (h0mix p ν) := by
    unfold h0mix
    exact integrable_finset_sum_measure.mpr fun c _ => hpiece c
  refine ⟨klDiv_ne_top hac hint, ?_⟩
  rw [toReal_klDiv hac hint]
  simp only [probReal_univ, add_sub_cancel_right]
  have e : ∫ a, llr (h0mix p ν) ρ a ∂(h0mix p ν) =
      ∑ c, ∫ a, llr (h0mix p ν) ρ a ∂(ENNReal.ofReal (p c) • ν c) :=
    integral_finset_sum_measure (fun c _ => hpiece c)
  rw [e, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_smul_measure, ENNReal.toReal_ofReal (hp0 c), smul_eq_mul]
  by_cases hc : 0 < p c
  · have h3 := h0_llr_ae ρ C hCm hCd ν hν p hp0 hp1 c hc hac (hνρ c hc).1
    rw [integral_congr_ae h3, integral_add (hνρ c hc).2 (integrable_const _), integral_const,
      toReal_klDiv_of_measure_eq (hνρ c hc).1 (by simp)]
    simp only [probReal_univ, smul_eq_mul, one_mul]
    ring
  · have : p c = 0 := le_antisymm (not_lt.mp hc) (hp0 c)
    simp [this]

end KL

end HRS.MC.CepH0
