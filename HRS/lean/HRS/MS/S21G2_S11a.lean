import HRS.MS.S21G2_S11aC
import HRS.Whole.Basic

/-!
# S21G2 S11a -- one isonormal Gaussian field after `μ` (R26-T3.S11a)

`ProductGaussian μ` is copied verbatim from the contract (qualified names: `HRS.Whole.projMean`).  `r26t3_product_gaussian` takes a
zero-padded Hilbert basis `e` of `L²(μ)`, the i.i.d. sequence `ξ` and `η f = W (f - μ f)` with `W h = L²-lim ∑ ⟪e_n,h⟫ ξ_n`
(parts A, B, C).  No identity-covariance `L²`-valued random element is asserted.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

structure ProductGaussian {d : ℕ} (μ : Measure (HRS.Euc d)) where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  P : Measure Ω
  [prob : IsProbabilityMeasure P]
  ξ : ℕ → Ω → ℝ
  standard : HRS.IsStdGaussianSeq P ξ
  η : (HRS.Euc d → ℝ) → Ω → ℝ
  meas : ∀ f, MemLp f 2 μ → Measurable (η f)
  first : ∀ f, MemLp f 2 μ → HRS.InFirstChaos P ξ 2 (η f)
  gaussian : ∀ n (f : Fin n → HRS.Euc d → ℝ), (∀ i, MemLp (f i) 2 μ) →
    HRS.IsCenteredGaussian (HRS.law P (fun ω i => η (f i) ω))
  covariance : ∀ f g, MemLp f 2 μ → MemLp g 2 μ →
    ∫ ω, η f ω * η g ω ∂P = ∫ x, HRS.Whole.projMean μ f x * HRS.Whole.projMean μ g x ∂μ
attribute [instance] ProductGaussian.mΩ ProductGaussian.prob

theorem r26t3_product_gaussian {d : ℕ} (μ : Measure (HRS.Euc d)) [IsProbabilityMeasure μ] :
    Nonempty (ProductGaussian μ) := by
  classical
  haveI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  obtain ⟨e, he⟩ := s21g2_s11a_parseval (Lp ℝ 2 μ)
  obtain ⟨Ω, mΩ, P, hPp, ξ, W, hstd, hξ, hWm, hW2, hWlim, hcomb, hcov⟩ := s21g2_s11a_isonormal e he
  let prj : (HRS.Euc d → ℝ) → Lp ℝ 2 μ := fun f =>
    if hf : MemLp f 2 μ then
      (show MemLp (HRS.Whole.projMean μ f) 2 μ from hf.sub (memLp_const _)).toLp _ else 0
  have hprj : ∀ f, MemLp f 2 μ → (prj f : HRS.Euc d → ℝ) =ᵐ[μ] HRS.Whole.projMean μ f := fun f hf => by
    simp only [prj, dif_pos hf]
    exact MemLp.coeFn_toLp _
  refine ⟨⟨Ω, P, ξ, hstd, fun f => W (prj f), fun f _ => hWm _, fun f _ => ?_, fun n f _ => ?_,
    fun f g hf hg => ?_⟩⟩
  · exact s21g2_s11a_firstChaos ξ hξ (fun i => inner ℝ (e i) (prj f)) (hW2 _) (hWlim _)
  · exact s21g2_s11a_gauss_of_laws (aemeasurable_pi_iff.2 fun i => (hWm _).aemeasurable)
      (fun c => ⟨_, hcomb n c (fun i => prj (f i))⟩)
  · show ∫ ω, W (prj f) ω * W (prj g) ω ∂P = _
    rw [hcov, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hprj f hf, hprj g hg] with x h1 h2
    simp [h1, h2, mul_comm]

end HRS.MS.R26T3
