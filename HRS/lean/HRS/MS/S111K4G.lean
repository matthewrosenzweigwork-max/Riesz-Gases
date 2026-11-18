import HRS.MS.S111K4F
import HRS.MS.R2ChaosAux5

/-!
# S11.1 / T01 (S11K4), part G: `L²` limits and Bessel for a merely a.e.-measurable kernel

`k4_l2_limit_bound` is Pro `R26-T6.W05`; `k4_bessel` is the Bessel inequality of `R2ChaosAux5` for a kernel known only
to lie in `L²(μ ⊗ μ)` (a.e.-measurable).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace HRS.MS.S111K4

/-- Uniform second-moment bounds pass through genuine `L²` limits (Pro `R26-T6.W05`). -/
theorem k4_l2_limit_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Qn : ℕ → Ω → ℝ) (Q : Ω → ℝ) (hQn : ∀ n, MemLp (Qn n) 2 P) (hQ : MemLp Q 2 P)
    (hlim : Tendsto (fun n => ∫ ω, (Qn n ω - Q ω) ^ 2 ∂P) atTop (𝓝 0))
    (B : ℝ) (hbound : ∀ n, ∫ ω, Qn n ω ^ 2 ∂P ≤ B) :
    ∫ ω, Q ω ^ 2 ∂P ≤ B := by
  have hB : 0 ≤ B := (integral_nonneg fun ω => sq_nonneg _).trans (hbound 0)
  have key : ∀ t : ℝ, 0 < t → ∫ ω, Q ω ^ 2 ∂P ≤ (1 + t) * B := by
    intro t ht
    have hle : ∀ n, ∫ ω, Q ω ^ 2 ∂P ≤ (1 + t) * B + (1 + 1 / t) * ∫ ω, (Qn n ω - Q ω) ^ 2 ∂P := by
      intro n
      have h1 : Integrable (fun ω => Qn n ω ^ 2) P := (hQn n).integrable_sq
      have h2 : Integrable (fun ω => (Qn n ω - Q ω) ^ 2) P := ((hQn n).sub hQ).integrable_sq
      have h3 : Integrable (fun ω => Q ω ^ 2) P := hQ.integrable_sq
      calc ∫ ω, Q ω ^ 2 ∂P
          ≤ ∫ ω, ((1 + t) * Qn n ω ^ 2 + (1 + 1 / t) * (Qn n ω - Q ω) ^ 2) ∂P := by
            refine integral_mono h3 ((h1.const_mul _).add (h2.const_mul _)) fun ω => ?_
            have h : 0 ≤ (t * Qn n ω + (Qn n ω - Q ω)) ^ 2 / t := by positivity
            have e : (t * Qn n ω + (Qn n ω - Q ω)) ^ 2 / t =
                t * Qn n ω ^ 2 + 2 * Qn n ω * (Qn n ω - Q ω) + (Qn n ω - Q ω) ^ 2 / t := by
              field_simp
              ring
            have e2 : 1 / t * (Qn n ω - Q ω) ^ 2 = (Qn n ω - Q ω) ^ 2 / t := by ring
            nlinarith [h, e, e2]
        _ = (1 + t) * ∫ ω, Qn n ω ^ 2 ∂P + (1 + 1 / t) * ∫ ω, (Qn n ω - Q ω) ^ 2 ∂P := by
            rw [integral_add (h1.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul]
        _ ≤ _ := by
            have := hbound n
            nlinarith [this]
    have hlim' : Tendsto (fun n => (1 + t) * B + (1 + 1 / t) * ∫ ω, (Qn n ω - Q ω) ^ 2 ∂P) atTop
        (𝓝 ((1 + t) * B + (1 + 1 / t) * 0)) := tendsto_const_nhds.add (hlim.const_mul _)
    have := ge_of_tendsto' hlim' hle
    simpa using this
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have := key (ε / (B + 1)) (by positivity)
  have h2 : (1 + ε / (B + 1)) * B ≤ B + ε := by
    have : ε / (B + 1) * B ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith
  linarith

end HRS.MS.S111K4
