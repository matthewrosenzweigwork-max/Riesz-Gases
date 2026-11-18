import HRS.MS.ShiftFldAux4

/-!
# S79: the shift mechanism for paths (a fixed window start `a₀`)

For a canonical realization `(P, X₀, W, X)` (hence `law (X t) = canonicalGibbs` for all `t`, by `GibbsInvariant`):

* `s79_shift_remainder`: `‖√N (m_N - μ) - N^{3/2-p} b‖_{B_m} ≤ K N^{3/2-p-θ}` for the canonical Gibbs first marginal `m_N`
  and any thermal equilibrium `ρβ` (it equals `thermalDensity`, `s78_eq_thermalDensity`).
* `s79_core`: if the exactly centered window `ζ_N^{a₀+·}` is a.e.-measurable and compared with the Gaussian window `Z^{a₀+·}`, then the
  mean-field centered window `η_N^{a₀+·} = ζ_N^{a₀+·} + (constant path)` (valid because `X` is a.s. continuous, so the `windowPathOf`
  dichotomy does not interfere) is a.e.-measurable, and its smooth / `W_1` distance to `Z^{a₀+·} + N^{3/2-p} 𝐛` is at most the
  distance of the centered window plus `K N^{3/2-p-θ}`.  No input from S2.1: the bound for the centered window is a hypothesis of the
  consumer.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Whole.S79

open HRS (Euc)

variable {d : ℕ} {s : ℝ}

theorem s79_shift_remainder (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) {m : ℝ} (hmd : (d : ℝ) < m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 2 ≤ N → ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ →
      IsProbabilityMeasure (canonicalGibbs (rieszKernel d s) (confinement a) N β) ∧
      ‖Real.sqrt N • OscDual.ofMeasureDiff m
          (meanEmpirical (canonicalGibbs (rieszKernel d s) (confinement a) N β))
          (withDensityReal ρ) -
        (N : ℝ) ^ (3 / 2 - biasP d s) • biasField m d s β ρ‖ ≤
        K * (N : ℝ) ^ (3 / 2 - biasP d s - biasTheta d s) := by
  have hs0 : 0 < s := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    linarith
  have hs0' : 0 ≤ s := hs0.le
  obtain ⟨hprob, -, -, hcan, Cb, hCb⟩ := HRS.Whole.S71.sharp_bias_quadratic_proof hd hs hsd a β ha hβ
  obtain ⟨K, hK0, hK⟩ := s79_shift_bound hd hs hsd hmd
  obtain ⟨Cs, -, hS⟩ := S45.s45_static_all hd hs0' hsd ha hβ
  refine ⟨K * max Cb 0, mul_nonneg hK0 (le_max_right _ _), fun N hN ρ hρ => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hSN := hS N hN
  have hρeq : ρ = thermalDensity d s a β := HRS.Whole.S78.s78_eq_thermalDensity hd hs0 hsd ha hβ hρ
  subst hρeq
  refine ⟨hSN.prob, ?_⟩
  haveI := hSN.prob
  have hmean : meanEmpirical (canonicalGibbs (rieszKernel d s) (confinement a) N β) =
      firstMarginal (modulatedGibbs (rieszKernel d s) N β (withDensityReal (thermalDensity d s a β))) := by
    rw [meanEmpirical_eq_firstMarginal _ hSN.exch hN1, hcan N]; rfl
  rw [hmean]
  exact hK β (thermalDensity d s a β) hprob N hN Cb (hCb N hN1)

theorem s79_law_X_eq {N : ℕ} {a β : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → EucConfig d N} (hR : IsCanonicalRealization d s a β N P X₀ W X) (t : ℝ≥0) :
    P.map (X t) = canonicalGibbs (rieszKernel d s) (confinement a) N β :=
  hR.invariant P (t : ℝ) X₀ W X hR.brownian hR.indep hR.init (hR.solution t) t le_rfl

theorem s79_windowPathOf_add_const (m T a : ℝ) (g : ℝ → OscDual d m) (c : OscDual d m)
    (hg : Continuous fun t : Set.Icc (0 : ℝ) T => g (a + t)) :
    windowPathOf m T a (fun t => g t + c) = windowPathOf m T a g + constPath m T c := by
  have h2 : Continuous fun t : Set.Icc (0 : ℝ) T => g (a + t) + c := hg.add continuous_const
  have e1 : windowPathOf m T a g =
      (⟨fun t => g (a + t), hg⟩ : C(Set.Icc (0 : ℝ) T, OscDual d m)) := by
    unfold windowPathOf; exact dif_pos hg
  have e2 : windowPathOf m T a (fun t => g t + c) =
      (⟨fun t => g (a + t) + c, h2⟩ : C(Set.Icc (0 : ℝ) T, OscDual d m)) := by
    unfold windowPathOf; exact dif_pos h2
  rw [e1, e2]
  exact ContinuousMap.ext fun t => rfl

theorem s79_continuous_window {N : ℕ} {m : ℝ} (hN : 0 < N) (hm : (d : ℝ) < m)
    (ν : Measure (Euc d)) [IsFiniteMeasure ν] (a T : ℝ) (x : ℝ≥0 → EucConfig d N)
    (hx : Continuous x) :
    Continuous fun t : Set.Icc (0 : ℝ) T =>
      OscDual.ofMeasureDiff m (empirical (x (Real.toNNReal (a + t)))) ν := by
  have h1 := s79_continuous_ofMeasureDiff_empirical (m := m) hN hm ν
  exact h1.comp (hx.comp (continuous_real_toNNReal.comp (continuous_const.add continuous_subtype_val)))

end HRS.Whole.S79
