import HRS.MS.S21T4ProdBQ

/-!
# S13: common Gaussian witnesses on arbitrary product measures

The product measure can have atoms and its centred L² space can be finite
-dimensional. The case without a countable infinite zero-mean ONB is treated
explicitly; second-chaos membership is never inferred from a vacuous Wick
representation.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_generic_product_wick_finite_all
    (I : ProductGaussian μ) (m : ℕ)
    (h : Fin m → Euc d → Euc d → ℝ)
    (hh : ∀ i, MemLp (fun z : Euc d × Euc d => h i z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ i x y, h i x y = h i y x) :
    ∃ Q : Fin m → I.Ω → ℝ,
      (∀ i, InSecondChaos I.P I.ξ 3 (Q i)) ∧
      (∀ i, MemLp (Q i) 2 I.P) ∧
      (∀ a, IsR2ZeroMeanONB μ a → ∀ i,
        IsR2WickChaos I.P μ a (fun j => I.η (a j))
          (r2CenterKernel μ (h i)) (fun ω => 2 * Q i ω)) := by
  classical
  letI := I.mΩ
  letI := I.prob
  by_cases hex : ∃ a, IsR2ZeroMeanONB μ a
  · obtain ⟨a, ha⟩ := hex
    obtain ⟨Q, hsecond, hwick, hbd⟩ := s21t4_product_wick_finite I m h hh hs
    refine ⟨Q, hsecond, ?_, hwick⟩
    intro i
    have hQi : MemLp (fun ω => 2 * Q i ω) 2 I.P :=
      s21t4_wick_memLp I a ha (r2CenterKernel μ (h i))
        (fun ω => 2 * Q i ω) (hwick a ha i)
    convert hQi.const_mul (1 / 2 : ℝ) using 1
    funext ω
    ring
  · refine ⟨fun _ _ => 0, ?_, (fun i => MemLp.zero), ?_⟩
    · intro i
      refine ⟨aestronglyMeasurable_const, (fun _ => 0), (fun _ _ _ => 0), ?_⟩
      simp
    · intro a ha
      exact False.elim (hex ⟨a, ha⟩)

end HRS.MS.R26T3
