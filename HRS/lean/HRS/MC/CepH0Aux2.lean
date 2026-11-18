import HRS.MC.CepH0Aux1

/-!
# Packet CEPH0, auxiliary 2: Kullback-Leibler divergence of a mixture with disjoint supports
-/

open MeasureTheory InformationTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.CepH0

section KL

variable {α : Type*} [MeasurableSpace α] {ι : Type*} [Fintype ι]

/-- The mixture `∑ c, ofReal (p c) • ν c`. -/
def h0mix (p : ι → ℝ) (ν : ι → Measure α) : Measure α := ∑ c, ENNReal.ofReal (p c) • ν c

theorem h0mix_apply (p : ι → ℝ) (ν : ι → Measure α) (S : Set α) :
    h0mix p ν S = ∑ c, ENNReal.ofReal (p c) * ν c S := by
  simp [h0mix, Measure.coe_finset_sum, Finset.sum_apply]

theorem h0_smul_le_mix (p : ι → ℝ) (ν : ι → Measure α) (c : ι) :
    ENNReal.ofReal (p c) • ν c ≤ h0mix p ν := by
  refine Measure.le_iff'.mpr fun S => ?_
  rw [h0mix_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  exact Finset.single_le_sum (f := fun c => ENNReal.ofReal (p c) * ν c S) (fun _ _ => bot_le)
    (Finset.mem_univ c)

theorem h0mix_univ (p : ι → ℝ) (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) (ν : ι → Measure α)
    [∀ c, IsProbabilityMeasure (ν c)] : h0mix p ν Set.univ = 1 := by
  rw [h0mix_apply]
  simp only [measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ => hp0 c), hp1]
  simp

theorem h0mix_prob (p : ι → ℝ) (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) (ν : ι → Measure α)
    [∀ c, IsProbabilityMeasure (ν c)] : IsProbabilityMeasure (h0mix p ν) :=
  ⟨h0mix_univ p hp0 hp1 ν⟩

theorem h0_restrict_mix [DecidableEq ι] (C : ι → Set α)
    (hCd : Pairwise fun c c' => Disjoint (C c) (C c')) (ν : ι → Measure α)
    (hν : ∀ c, ν c (C c)ᶜ = 0) (p : ι → ℝ) (c : ι) (hCm : MeasurableSet (C c)) :
    (h0mix p ν).restrict (C c) = ENNReal.ofReal (p c) • ν c := by
  ext T hT
  rw [Measure.restrict_apply hT, h0mix_apply, Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single c]
  · congr 1
    exact measure_inter_conull (hν c)
  · intro c' _ hc'
    have h0 : ν c' (T ∩ C c) = 0 := by
      refine measure_mono_null (fun x hx => ?_) (hν c')
      intro hx'
      exact Set.disjoint_left.mp (hCd hc'.symm) hx.2 hx'
    rw [h0, mul_zero]
  · simp

theorem h0_mix_ac_iff (ρ : Measure α) (p : ι → ℝ) (ν : ι → Measure α) :
    h0mix p ν ≪ ρ ↔ ∀ c, 0 < p c → ν c ≪ ρ := by
  constructor
  · intro h c hc S hS
    have h1 := h0_smul_le_mix p ν c S
    have h2 : h0mix p ν S = 0 := h hS
    rw [h2] at h1
    have h3 : ENNReal.ofReal (p c) * ν c S = 0 := by
      simpa using le_antisymm h1 bot_le
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 (by simpa using hc)
    · exact h4
  · intro h S hS
    rw [h0mix_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : 0 < p c
    · rw [h c hc hS, mul_zero]
    · rw [ENNReal.ofReal_of_nonpos (not_lt.mp hc), zero_mul]

end KL

end HRS.MC.CepH0
