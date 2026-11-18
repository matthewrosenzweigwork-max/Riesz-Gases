import HRS.MS.R2ChaosAux37

/-!
# HRS.MS.R2ChaosAux38 -- R4 (part 3): a jointly measurable limit `F` of the finite-rank Gaussian integrands

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

`s94_exists_F`: for the R1 approximants `(Cm m, u m)` and an orthonormal basis `a` of `L²_0(μ)` by projected tests, there is a
jointly measurable `F : ℝ × Ω' → ℝ` with `F(t,·) ∈ L²(P')` and `s94Flim ξ P' (Cm m) (u m) t · → F(t,·)` in `L²(P')`
for EVERY `t ∈ [0,T]` (`s94_flim_cauchy` + `s94_measurable_L2_limit`).
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

section ExistsF

variable {s T b p K M L : ℝ} {ρ : Euc d → ℝ} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

theorem s94_exists_F (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hρ : IsRound2Density d s M L ρ)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) {Λ : ℝ}
    (hcov : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ a, IsR2Test a →
      ∫ ζ, (r2PathEval T (ξ a ζ) t) ^ 2 ∂P' ≤ Λ * ∫ x, (Whole.projMean (Whole.withDensityReal ρ) a x) ^ 2 ∂(Whole.withDensityReal ρ))
    (hΛ0 : 0 ≤ Λ) {a : ℕ → Euc d → ℝ} (ha : IsR2ZeroMeanONB (Whole.withDensityReal ρ) a) {B C₁ : ℝ}
    {h : ℝ → Euc d → Euc d → ℝ} (hker : ∀ t ∈ Set.Icc (0 : ℝ) T, IsBoundedPairKernel s B (h t))
    {n : ℕ → ℕ} {u : ∀ m, Fin (n m) → Euc d → ℝ} {Cm : ∀ m, ℝ → Fin (n m) → Fin (n m) → ℝ}
    (hu : ∀ m a, IsR2Test (u m a)) (hCm : ∀ m a b, Measurable fun t => Cm m t a b)
    (hCs : ∀ m t a b, Cm m t a b = Cm m t b a)
    (hA : ∀ t ∈ Set.Icc (0 : ℝ) T, IsRound2Approx s C₁ B (Whole.withDensityReal ρ) (h t)
      (fun m => r2FiniteRankKernel (Cm m t) (u m))) :
    ∃ F : ℝ × Ω' → ℝ, Measurable F ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, MemLp (fun ζ => F (t, ζ)) 2 P' ∧
      Tendsto (fun m => eLpNorm (fun ζ => s94Flim ξ P' (Cm m) (u m) t ζ - F (t, ζ)) 2 P') atTop (𝓝 0) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  have hΦ2 : ∀ m, ∀ t ∈ Set.Icc (0 : ℝ) T, MemLp (fun ζ => s94Flim ξ P' (Cm m) (u m) t ζ) 2 P' := by
    intro m t ht
    obtain ⟨ha0, hon, hcomplete⟩ := ha
    have hQ := s94_wick_finiteRank hset hcov hΛ0 ha0 hon hcomplete (Cm m t) (hu m) ht
    have e : (fun ζ => s94Flim ξ P' (Cm m) (u m) t ζ) = fun ζ => (1 / 2 : ℝ) * ∑ α, ∑ β, Cm m t α β *
        (r2PathEval T (ξ (u m α) ζ) t * r2PathEval T (ξ (u m β) ζ) t -
          ∫ ζ', r2PathEval T (ξ (u m α) ζ') t * r2PathEval T (ξ (u m β) ζ') t ∂P') := by
      funext ζ
      unfold s94Flim
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun β _ => ?_
      ring
    rw [e]
    exact hQ.1.const_mul (1 / 2 : ℝ)
  exact s94_measurable_L2_limit measurableSet_Icc (Φ := fun m q => s94Flim ξ P' (Cm m) (u m) q.1 q.2)
    (fun m => s94Flim_measurable hset.measξ P' (hCm m) (u m)) hΦ2
    (fun t ht ε hε => s94_flim_cauchy hd hs0 hs hρ hset hcov hΛ0 ha hker hu hCs hA ht ε hε)

end ExistsF

end HRS.MS.R2Chaos
