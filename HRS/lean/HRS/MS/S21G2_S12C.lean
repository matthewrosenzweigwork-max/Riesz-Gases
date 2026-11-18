import HRS.MS.S21G2_S11a
import HRS.Prob.Metrics

/-!
# S21G2 S12 (part C) -- a Gaussian vector with the projected covariance of a finite `L²` family (R26-T3.S12)

From `ProductGaussian μ` (S11a): for `g : Fin k → Euc d → ℝ` with `L²(μ)` components there is a probability space and a measurable
`Zv : Ω' → ℝ^k` with centred Gaussian law and `E[(α·Zv)(β·Zv)] = ∫ (α·pm g)(β·pm g) dμ`.  Helpers `s21g2_s12_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

theorem s21g2_s12_expand_one {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] {k : ℕ}
    (C : Fin k → Ω → ℝ) (hC : ∀ i, MemLp (C i) 2 ν) (α β : Fin k → ℝ) :
    ∫ ω, (∑ i, α i * C i ω) * (∑ j, β j * C j ω) ∂ν =
      ∑ i, ∑ j, α i * β j * ∫ ω, C i ω * C j ω ∂ν := by
  have : ∀ ω, (∑ i, α i * C i ω) * (∑ j, β j * C j ω) =
      ∑ i, ∑ j, (α i * β j) * (C i ω * C j ω) := fun ω => by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [this]
  have hi : ∀ i j, Integrable (fun ω => C i ω * C j ω) ν := fun i j => (hC i).integrable_mul (hC j)
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hi i j).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => (hi i j).const_mul _]
  exact Finset.sum_congr rfl fun j _ => by rw [integral_const_mul]

theorem s21g2_s12_cov_expand {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Ω₂ : Type*} [MeasurableSpace Ω₂]
    {Q : Measure Ω₂} {k : ℕ} {A : Fin k → Ω → ℝ} {B : Fin k → Ω₂ → ℝ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hA : ∀ i, MemLp (A i) 2 P) (hB : ∀ i, MemLp (B i) 2 Q)
    (hcov : ∀ i j, ∫ ω, A i ω * A j ω ∂P = ∫ x, B i x * B j x ∂Q) (α β : Fin k → ℝ) :
    ∫ ω, (∑ i, α i * A i ω) * (∑ j, β j * A j ω) ∂P = ∫ x, (∑ i, α i * B i x) * (∑ j, β j * B j x) ∂Q := by
  rw [s21g2_s12_expand_one P A hA, s21g2_s12_expand_one Q B hB]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hcov]

theorem s21g2_s12_gauss_field {d k : ℕ} (μ : Measure (HRS.Euc d)) [IsProbabilityMeasure μ]
    (g : Fin k → HRS.Euc d → ℝ) (hg : ∀ i, MemLp (g i) 2 μ) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (Zv : Ω' → (Fin k → ℝ)), Measurable Zv ∧ HRS.IsCenteredGaussian (P'.map Zv) ∧
      (∀ i, MemLp (fun ω => Zv ω i) 2 P') ∧
      ∀ α β : Fin k → ℝ, ∫ ω, (∑ i, α i * Zv ω i) * (∑ j, β j * Zv ω j) ∂P' =
        ∫ x, (∑ i, α i * HRS.Whole.projMean μ (g i) x) * (∑ j, β j * HRS.Whole.projMean μ (g j) x) ∂μ := by
  obtain ⟨PG⟩ := r26t3_product_gaussian μ
  have hmeas : Measurable (fun ω i => PG.η (g i) ω) := measurable_pi_iff.2 fun i => PG.meas _ (hg i)
  have hG := PG.gaussian k g hg
  have hZ : MemLp (fun ω i => PG.η (g i) ω) 2 PG.P := by
    have := hG.1.memLp_two_id
    exact (memLp_map_measure_iff aestronglyMeasurable_id hmeas.aemeasurable).1 this
  have hcoord : ∀ i, MemLp (fun ω => PG.η (g i) ω) 2 PG.P := fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).comp_memLp' hZ
  have hpm : ∀ i, MemLp (HRS.Whole.projMean μ (g i)) 2 μ := fun i =>
    (hg i).sub (memLp_const (HRS.Whole.pair μ (g i)))
  refine ⟨PG.Ω, PG.mΩ, PG.P, PG.prob, fun ω i => PG.η (g i) ω, hmeas, hG, hcoord, fun α β => ?_⟩
  exact s21g2_s12_cov_expand (A := fun i ω => PG.η (g i) ω) (B := fun i => HRS.Whole.projMean μ (g i))
    hcoord hpm (fun i j => PG.covariance (g i) (g j) (hg i) (hg j)) α β

end HRS.MS.R26T3
