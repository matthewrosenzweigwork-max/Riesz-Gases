import HRS.MS.R2InterpAux7

/-!
# S10.2 (worker S102), part 8 (packet F3): the bracket identity `F:eq:bracket-exact`

For the scaled noise integrands `√N (√c/N) ∂_a f(x_p)` (`c = 2ν`) of two observations, the sum over `(p,a)` of their products is
`c μ_N(∇f·∇g)`, which is `c μ(∇f·∇g) + N^{-1/2} c η_N(∇f·∇g)` with `η_N = √N(μ_N - μ)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d N : ℕ}

theorem s102_bracket_sum (hN : 0 < N) {c : ℝ} (hc : 0 ≤ c) (f g : Euc d → ℝ) (X : EucConfig d N) :
    ∑ k : Fin N × Fin d, (Real.sqrt N * (Real.sqrt c / N * gradient f (X k.1) k.2)) *
        (Real.sqrt N * (Real.sqrt c / N * gradient g (X k.1) k.2)) =
      c * HRS.Whole.pair (HRS.Whole.empirical X) (fun y => inner ℝ (gradient f y) (gradient g y)) := by
  rw [HRS.Whole.pair_empirical hN]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hs : Real.sqrt (N : ℝ) * Real.sqrt N = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
  have hc' : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc
  rw [Fintype.sum_prod_type]
  have : ∀ p : Fin N, ∑ a : Fin d, (Real.sqrt N * (Real.sqrt c / N * gradient f (X p) a)) *
      (Real.sqrt N * (Real.sqrt c / N * gradient g (X p) a)) =
      (c / N) * inner ℝ (gradient f (X p)) (gradient g (X p)) := by
    intro p
    have h2 : ∀ a : Fin d, (Real.sqrt N * (Real.sqrt c / N * gradient f (X p) a)) *
        (Real.sqrt N * (Real.sqrt c / N * gradient g (X p) a)) =
        (c / N) * (gradient f (X p) a * gradient g (X p) a) := by
      intro a
      rw [show (Real.sqrt N * (Real.sqrt c / N * gradient f (X p) a)) *
          (Real.sqrt N * (Real.sqrt c / N * gradient g (X p) a)) =
          ((Real.sqrt N * Real.sqrt N) * (Real.sqrt c * Real.sqrt c) / ((N : ℝ) * N)) *
            (gradient f (X p) a * gradient g (X p) a) by ring, hs, hc']
      field_simp
    simp_rw [h2, ← Finset.mul_sum]
    congr 1
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  simp_rw [this, ← Finset.mul_sum]
  field_simp

/-- The decomposition `c μ_N(γ) = c μ(γ) + N^{-1/2} c · √N(μ_N(γ) - μ(γ))` (the bracket of the empirical martingale
is the bracket of the Gaussian future plus the `η_N` correction). -/
theorem s102_bracket_decomp (hN : 0 < N) (c : ℝ) (μ ν : Measure (Euc d)) (γ : Euc d → ℝ) :
    c * HRS.Whole.pair μ γ = c * HRS.Whole.pair ν γ +
      (Real.sqrt N)⁻¹ * (c * (Real.sqrt N * (HRS.Whole.pair μ γ - HRS.Whole.pair ν γ))) := by
  have : Real.sqrt (N : ℝ) ≠ 0 := Real.sqrt_ne_zero'.2 (by exact_mod_cast hN)
  field_simp
  ring

end HRS.MS.R2Interp

end
