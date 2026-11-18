import HRS.MS.R2ChaosAux11

/-!
# HRS.MS.R2ChaosAux12 -- fixed-time Wick chaos of an envelope-bounded kernel: existence, basis independence

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

variable {d : ℕ}

theorem s94_integral_sq_le_of_eLpNorm {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f ν) {a : ℝ} (ha : 0 ≤ a) (h : eLpNorm f 2 ν ≤ ENNReal.ofReal a) :
    ∫ x, f x ^ 2 ∂ν ≤ a ^ 2 := by
  have hint : Integrable (fun x => f x ^ 2) ν := by
    have hm : MemLp f 2 ν := h.trans_lt ENNReal.ofReal_lt_top
    exact hm.integrable_sq
  have h1 : ENNReal.ofReal (∫ x, f x ^ 2 ∂ν) = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => sq_nonneg _)]
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
  rw [s94_lintegral_sq_eq hf] at h1
  have h2 : ENNReal.ofReal (∫ x, f x ^ 2 ∂ν) ≤ ENNReal.ofReal (a ^ 2) := by
    rw [h1, ENNReal.ofReal_pow ha]
    gcongr
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

section Kernels

variable {s : ℝ}

theorem s94_finiteRank_integrable_facts {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {m : ℕ}
    {c : Fin m → Fin m → ℝ} {u : Fin m → Euc d → ℝ} (hu : ∀ a, IsR2Test (u a)) :
    (∀ x, Integrable (fun y => r2FiniteRankKernel c u x y) μ) ∧
      (∀ y, Integrable (fun x => r2FiniteRankKernel c u x y) μ) ∧
      Integrable (fun x => ∫ y', r2FiniteRankKernel c u x y' ∂μ) μ := by
  obtain ⟨C, hC⟩ := s94_finiteRank_bounded (c := c) hu
  have hm := s94_finiteRank_measurable (c := c) hu
  refine ⟨fun x => ?_, fun y => ?_, ?_⟩
  · exact Integrable.of_bound (hm.comp measurable_prodMk_left).aestronglyMeasurable C
      (ae_of_all _ fun y => by simpa using hC x y)
  · exact Integrable.of_bound (hm.comp measurable_prodMk_right).aestronglyMeasurable C
      (ae_of_all _ fun x => by simpa using hC x y)
  · refine Integrable.of_bound (hm.stronglyMeasurable.integral_prod_right' (ν := μ)).aestronglyMeasurable C
      (ae_of_all _ fun x => ?_)
    refine (norm_integral_le_of_norm_le_const (C := C) (ae_of_all _ fun y => ?_)).trans (by simp)
    simpa using hC x y

/-- The centered kernel of an envelope-bounded kernel lies in `L²`. -/
theorem s94_center_memLp (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {M L B : ℝ} {ρ : Euc d → ℝ}
    (hρ : IsRound2Density d s M L ρ) {h : Euc d → Euc d → ℝ} (hh : IsBoundedPairKernel s B h) :
    MemLp (fun q : Euc d × Euc d => r2CenterKernel (Whole.withDensityReal ρ) h q.1 q.2) 2
      ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ)) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  have h2 := s94_env_memLp hd hs0 hs hρ hh
  have hle := s94_eLpNorm_center_le (μ := Whole.withDensityReal ρ) hh.measurable
  exact lt_of_le_of_lt hle (ENNReal.mul_lt_top (by norm_num) h2)

theorem s94_center_diff_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {M L B : ℝ} {ρ : Euc d → ℝ}
    (hρ : IsRound2Density d s M L ρ) {h : Euc d → Euc d → ℝ} (hh : IsBoundedPairKernel s B h)
    {m : ℕ} {c : Fin m → Fin m → ℝ} {u : Fin m → Euc d → ℝ} (hu : ∀ a, IsR2Test (u a)) :
    eLpNorm (fun q : Euc d × Euc d => r2CenterKernel (Whole.withDensityReal ρ) h q.1 q.2 -
        r2CenterKernel (Whole.withDensityReal ρ) (r2FiniteRankKernel c u) q.1 q.2) 2
      ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ)) ≤
    4 * eLpNorm (fun q : Euc d × Euc d => h q.1 q.2 - r2FiniteRankKernel c u q.1 q.2) 2
      ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ)) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  obtain ⟨e1, e2, e3⟩ := s94_env_facts hd hs0 hs hρ hh
  obtain ⟨f1, f2, f3⟩ := s94_finiteRank_integrable_facts (μ := Whole.withDensityReal ρ) (c := c) hu
  have hmeas : Measurable fun q : Euc d × Euc d => (fun x y => h x y - r2FiniteRankKernel c u x y) q.1 q.2 :=
    hh.measurable.sub (s94_finiteRank_measurable hu)
  have := s94_eLpNorm_center_le (μ := Whole.withDensityReal ρ)
    (g := fun x y => h x y - r2FiniteRankKernel c u x y) hmeas
  convert this using 2
  funext q
  exact (s94_center_sub e1 f1 e2 f2 e3 f3 q.1 q.2).symm

end Kernels

end HRS.MS.R2Chaos
