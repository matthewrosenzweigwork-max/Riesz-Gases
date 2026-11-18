import HRS.MS.R2ChaosAux48

/-!
# HRS.MS.R2ChaosAux49 -- (e) part 4: uniform `p`-th moments of the particle-side vector in `H`

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

`s94_moment_y`: for every `p ≥ 2` there is `M` with `E ‖(ξ_N(a_1),…,ξ_N(a_k), B_N)‖_H^p ≤ M` for all `N ≥ 2`
(S9.2 pointwise in `t`, `s94_moment_L2path`, power-mean inequality in `H`).
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

section MomentY

variable {s T b p K M L : ℝ} {ρ : Euc d → ℝ} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

theorem s94_moment_y (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hb : 0 < b) (hp : 1 < p)
    (hρ : IsRound2Density d s M L ρ)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) (hT : 0 < T) {B : ℝ}
    {h : ℝ → Euc d → Euc d → ℝ} (hmeas : Measurable fun q : ℝ × Euc d × Euc d => h q.1 q.2.1 q.2.2)
    (hker : ∀ t ∈ Set.Icc (0 : ℝ) T, IsBoundedPairKernel s B (h t))
    {k : ℕ} {aa : Fin k → Euc d → ℝ} (haa : ∀ i, IsR2Test (aa i)) {q : ℝ} (hq : 2 ≤ q) :
    ∃ Mq : ℝ, 0 ≤ Mq ∧ ∀ N : ℕ, 2 ≤ N →
      ∫⁻ ζ, ENNReal.ofReal (‖s94_mkH T (fun i => r2L2Path T (r2EmpFluct (Whole.withDensityReal ρ) (aa i) (X N) ζ))
        (r2L2Path T (fun t => r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ))‖ ^ q) ∂(P N)
        ≤ ENNReal.ofReal Mq := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  obtain ⟨Cl, hCl⟩ := s94_linear_moment hd hs0 hs hb hp hρ hset (r := q) hq1
  obtain ⟨Cq, hCq⟩ := s94_time_bounds hd hs0 hs hb hp hρ hset B (r := q) hq1
  have hA : ∀ i, ∃ A : ℝ, 0 ≤ A ∧ ∀ x, |aa i x| ≤ A := fun i => by
    obtain ⟨A, hA⟩ := s94_test_bounded (haa i)
    exact ⟨A, (abs_nonneg _).trans (hA 0), hA⟩
  choose A hA0 hAb using hA
  have hC0 : ∀ i, 0 ≤ |Cl| * A i := fun i => mul_nonneg (abs_nonneg _) (hA0 i)
  have hCq0 : 0 ≤ |Cq| := abs_nonneg _
  have hterm : ∀ i, 0 ≤ T ^ (q / 2) * (|Cl| * A i) ^ q := fun i =>
    mul_nonneg (Real.rpow_nonneg hT.le _) (Real.rpow_nonneg (hC0 i) _)
  have htermq : 0 ≤ T ^ (q / 2) * |Cq| ^ q := mul_nonneg (Real.rpow_nonneg hT.le _) (Real.rpow_nonneg hCq0 _)
  refine ⟨((k : ℝ) + 1) ^ (q - 1) * (∑ i, T ^ (q / 2) * (|Cl| * A i) ^ q + T ^ (q / 2) * |Cq| ^ q),
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (add_nonneg (Finset.sum_nonneg fun i _ => hterm i) htermq),
    fun N hN => ?_⟩
  set μ := Whole.withDensityReal ρ with hμ
  let fi : Fin k → ℝ × Ω N → ℝ := fun i z => r2EmpFluct μ (aa i) (X N) z.2 z.1
  let fq : ℝ × Ω N → ℝ := fun z => r2QuadFluct μ h (P N) (X N) z.1 z.2
  have hfi : ∀ i, Measurable (fi i) := fun i => s94_empFluct_measurable (haa i) (X N) (hset.measX N)
  have hfq : Measurable fq := s94_quad_measurable (μ := μ) hmeas (X N) (hset.measX N)
  have hmi : ∀ i, ∫⁻ ζ, ENNReal.ofReal (‖r2L2Path T (fun t => fi i (t, ζ))‖ ^ q) ∂(P N) ≤
      ENNReal.ofReal (T ^ (q / 2) * (|Cl| * A i) ^ q) := by
    intro i
    refine s94_moment_L2path hT (hfi i) hq (hC0 i) fun t ht => ?_
    refine (hCl N hN t ht (aa i) (A i) (haa i).1.continuous.measurable (hAb i)).trans ?_
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _) (hA0 i))
  have hmq : ∫⁻ ζ, ENNReal.ofReal (‖r2L2Path T (fun t => fq (t, ζ))‖ ^ q) ∂(P N) ≤
      ENNReal.ofReal (T ^ (q / 2) * |Cq| ^ q) := by
    refine s94_moment_L2path hT hfq hq hCq0 fun t ht => ?_
    refine ((hCq t ht N hN (h t) (hker t ht)).2).trans ?_
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  -- pointwise power-mean bound
  have hpt : ∀ ζ, ENNReal.ofReal (‖s94_mkH T (fun i => r2L2Path T (r2EmpFluct μ (aa i) (X N) ζ))
      (r2L2Path T (fun t => r2QuadFluct μ h (P N) (X N) t ζ))‖ ^ q) ≤
      ENNReal.ofReal (((k : ℝ) + 1) ^ (q - 1)) * (∑ i, ENNReal.ofReal (‖r2L2Path T (fun t => fi i (t, ζ))‖ ^ q) +
        ENNReal.ofReal (‖r2L2Path T (fun t => fq (t, ζ))‖ ^ q)) := by
    intro ζ
    have h1 := s94_normH_pow_le (s94_mkH T (fun i => r2L2Path T (r2EmpFluct μ (aa i) (X N) ζ))
      (r2L2Path T (fun t => r2QuadFluct μ h (P N) (X N) t ζ))) hq1
    rw [Fin.sum_univ_castSucc] at h1
    simp only [s94_mkH_castSucc, s94_mkH_last] at h1
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity), ← ENNReal.ofReal_add (Finset.sum_nonneg fun i _ => by positivity)
      (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal h1
  have hmeasi : ∀ i, Measurable fun ζ => ENNReal.ofReal (‖r2L2Path T (fun t => fi i (t, ζ))‖ ^ q) := fun i =>
    ENNReal.measurable_ofReal.comp ((s94_measurable_r2L2Path T (fi i ∘ Prod.map id id) (hfi i)).norm.pow_const q)
  have hmeasq : Measurable fun ζ => ENNReal.ofReal (‖r2L2Path T (fun t => fq (t, ζ))‖ ^ q) :=
    ENNReal.measurable_ofReal.comp ((s94_measurable_r2L2Path T fq hfq).norm.pow_const q)
  calc _ ≤ ∫⁻ ζ, ENNReal.ofReal (((k : ℝ) + 1) ^ (q - 1)) * (∑ i, ENNReal.ofReal (‖r2L2Path T (fun t => fi i (t, ζ))‖ ^ q) +
        ENNReal.ofReal (‖r2L2Path T (fun t => fq (t, ζ))‖ ^ q)) ∂(P N) := lintegral_mono hpt
    _ = ENNReal.ofReal (((k : ℝ) + 1) ^ (q - 1)) * (∑ i, ∫⁻ ζ, ENNReal.ofReal (‖r2L2Path T (fun t => fi i (t, ζ))‖ ^ q) ∂(P N) +
        ∫⁻ ζ, ENNReal.ofReal (‖r2L2Path T (fun t => fq (t, ζ))‖ ^ q) ∂(P N)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left (Finset.measurable_sum _ fun i _ => hmeasi i),
          lintegral_finset_sum _ fun i _ => hmeasi i]
    _ ≤ ENNReal.ofReal (((k : ℝ) + 1) ^ (q - 1)) * (∑ i, ENNReal.ofReal (T ^ (q / 2) * (|Cl| * A i) ^ q) +
        ENNReal.ofReal (T ^ (q / 2) * |Cq| ^ q)) := by
        refine mul_le_mul_right (add_le_add (Finset.sum_le_sum fun i _ => hmi i) hmq) _
    _ = _ := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hterm i), ← ENNReal.ofReal_add (Finset.sum_nonneg fun i _ => hterm i)
          htermq, ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]

end MomentY

end HRS.MS.R2Chaos
