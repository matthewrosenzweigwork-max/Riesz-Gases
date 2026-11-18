import HRS.MS.R2ChaosAux39

/-!
# HRS.MS.R2ChaosAux40 -- (a) part 2: `P_μ` of the tests has arbitrarily large linearly independent families

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

`s94_poly_indep`: for every `N` there are tests `c_j = φ(x)(x_0)^{j+1}` (`φ` a bump equal to `1` on a ball of positive mass) such that
`∑ g_j P_μ c_j = 0` `μ`-a.e. forces `g = 0` (a nonzero polynomial in `x_0` vanishes only on finitely many `μ`-null hyperplanes).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology ContDiff

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

variable {d : ℕ}

theorem s94_poly_indep {s M L : ℝ} {ρ : Euc d → ℝ} (hd : 2 ≤ d) (hρ : IsRound2Density d s M L ρ) (N : ℕ) :
    ∃ c : Fin N → Euc d → ℝ, (∀ j, IsR2Test (c j)) ∧ ∀ g : Fin N → ℝ,
      (∀ᵐ x ∂(Whole.withDensityReal ρ), ∑ j, g j * Whole.projMean (Whole.withDensityReal ρ) (c j) x = 0) →
      ∀ j, g j = 0 := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  set μ := Whole.withDensityReal ρ with hμ
  let i0 : Fin d := ⟨0, by omega⟩
  have hac : μ ≪ (volume : Measure (Euc d)) :=
    Measure.absolutelyContinuous_of_le_smul (HRS.Whole.U1.u1_le_smul hρ.bdd)
  -- a ball of positive mass
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 0 < μ (Metric.closedBall (0 : Euc d) n) := by
    by_contra hcon
    push Not at hcon
    have h0 : ∀ n : ℕ, μ (Metric.closedBall (0 : Euc d) n) = 0 := fun n => le_antisymm (hcon n) bot_le
    have : μ (⋃ n : ℕ, Metric.closedBall (0 : Euc d) n) = 0 := measure_iUnion_null h0
    have hU : (⋃ n : ℕ, Metric.closedBall (0 : Euc d) n) = Set.univ := by
      ext x
      simp only [Set.mem_iUnion, Metric.mem_closedBall, dist_zero_right, Set.mem_univ, iff_true]
      exact exists_nat_ge _
    rw [hU, measure_univ] at this
    exact one_ne_zero this
  let φ : ContDiffBump (0 : Euc d) := ⟨(n : ℝ) + 1, (n : ℝ) + 2, by positivity, by linarith⟩
  have hφ1 : ∀ x ∈ Metric.closedBall (0 : Euc d) n, (φ : Euc d → ℝ) x = 1 := fun x hx =>
    φ.one_of_mem_closedBall (Metric.closedBall_subset_closedBall (by simp [φ]) hx)
  let π0 : Euc d →L[ℝ] ℝ := EuclideanSpace.proj i0
  refine ⟨fun j x => (φ : Euc d → ℝ) x * (x i0) ^ ((j : ℕ) + 1), fun j => ⟨?_, ?_⟩, ?_⟩
  · exact φ.contDiff.mul (π0.contDiff.pow _)
  · exact φ.hasCompactSupport.mul_right
  · intro g hg j
    set κ : ℝ := ∑ j, g j * ∫ x, (φ : Euc d → ℝ) x * (x i0) ^ ((j : ℕ) + 1) ∂μ with hκ
    let p : Polynomial ℝ := ∑ j : Fin N, Polynomial.C (g j) * Polynomial.X ^ ((j : ℕ) + 1) - Polynomial.C κ
    have hev : ∀ x : Euc d, x ∈ Metric.closedBall (0 : Euc d) n →
        (∑ j, g j * Whole.projMean μ (fun x => (φ : Euc d → ℝ) x * (x i0) ^ ((j : ℕ) + 1)) x = 0 ↔
          p.eval (x i0) = 0) := by
      intro x hx
      have e1 : ∑ j, g j * Whole.projMean μ (fun x => (φ : Euc d → ℝ) x * (x i0) ^ ((j : ℕ) + 1)) x =
          p.eval (x i0) := by
        simp only [Whole.projMean, Whole.pair, hφ1 x hx, p, Polynomial.eval_sub, Polynomial.eval_finset_sum,
          Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, one_mul, hκ,
          mul_sub, Finset.sum_sub_distrib]
      rw [e1]
    have hp0 : p = 0 := by
      by_contra hpne
      have hsub : {x : Euc d | p.eval (x i0) = 0} ⊆ ⋃ r ∈ p.roots.toFinset, {x : Euc d | x i0 = r} := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx
        simp only [Set.mem_iUnion, Set.mem_setOf_eq, Multiset.mem_toFinset]
        exact ⟨x i0, (Polynomial.mem_roots hpne).2 hx, rfl⟩
      have hnull : μ (⋃ r ∈ p.roots.toFinset, {x : Euc d | x i0 = r}) = 0 :=
        (measure_biUnion_null_iff (Finset.countable_toSet _)).2 (fun r _ => hac (s94_hyperplane_null i0 r))
      have h1 : ∀ᵐ x ∂μ, x ∈ Metric.closedBall (0 : Euc d) n → x ∈ ⋃ r ∈ p.roots.toFinset, {x : Euc d | x i0 = r} := by
        filter_upwards [hg] with x hx hxB
        exact hsub ((hev x hxB).1 hx)
      have h2 : μ {x | ¬ (x ∈ Metric.closedBall (0 : Euc d) n →
          x ∈ ⋃ r ∈ p.roots.toFinset, {x : Euc d | x i0 = r})} = 0 := ae_iff.1 h1
      have : μ (Metric.closedBall (0 : Euc d) n) = 0 := by
        refine measure_mono_null (fun x hx => ?_) (measure_union_null h2 hnull)
        by_cases hxU : x ∈ ⋃ r ∈ p.roots.toFinset, {x : Euc d | x i0 = r}
        · exact Or.inr hxU
        · exact Or.inl (fun h' => hxU (h' hx))
      exact hn.ne' this
    have := congrArg (fun q => q.coeff ((j : ℕ) + 1)) hp0
    simpa [p, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_C, Fin.val_inj] using this

end HRS.MS.R2Chaos
