import HRS.MS.PROS13CrossKernelSum

/-!
# Generic S13: exact addition of *actual* Gaussian quadratic limits

For arbitrary symmetric product-L² kernels and arbitrary unrelated
finite-rank approximation sequences, we construct a new smooth finite-rank
sequence for their sum, whose centered Gaussian polynomials converge in L²
to the sum of the two original quadratic witnesses on the SAME Gaussian
probability space. This is independent of any infinite centered ONB and
remains true for probability measures with finite support.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem pro_s13_actual_quadratic_additive_approximation
    (I : ProductGaussian μ)
    (h h' : Euc d → Euc d → ℝ)
    (hh : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ))
    (hh' : MemLp (fun z : Euc d × Euc d => h' z.1 z.2) 2 (μ.prod μ))
    (r s : ℕ → ℕ)
    (c : (j : ℕ) → Fin (r j) → Fin (r j) → ℝ)
    (u : (j : ℕ) → Fin (r j) → Euc d → ℝ)
    (c' : (j : ℕ) → Fin (s j) → Fin (s j) → ℝ)
    (v : (j : ℕ) → Fin (s j) → Euc d → ℝ)
    (hd : ∀ j, IsR2FiniteRankData (c j) (u j))
    (hd' : ∀ j, IsR2FiniteRankData (c' j) (v j))
    (Q Q' : I.Ω → ℝ) (hQ : MemLp Q 2 I.P) (hQ' : MemLp Q' 2 I.P)
    (hK : Tendsto (fun j => eLpNorm
      (fun z : Euc d × Euc d =>
        r2FiniteRankKernel (c j) (u j) z.1 z.2 - h z.1 z.2)
      2 (μ.prod μ)) atTop (𝓝 0))
    (hK' : Tendsto (fun j => eLpNorm
      (fun z : Euc d × Euc d =>
        r2FiniteRankKernel (c' j) (v j) z.1 z.2 - h' z.1 z.2)
      2 (μ.prod μ)) atTop (𝓝 0))
    (hlim : Tendsto (fun j : ℕ => ∫ ω : I.Ω,
      (((1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j), c j a b *
          (I.η (u j a) ω * I.η (u j b) ω -
            ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P)) -
         Q ω) ^ 2 ∂I.P) atTop (𝓝 0))
    (hlim' : Tendsto (fun j : ℕ => ∫ ω : I.Ω,
      (((1 / 2 : ℝ) * ∑ a : Fin (s j), ∑ b : Fin (s j), c' j a b *
          (I.η (v j a) ω * I.η (v j b) ω -
            ∫ ζ, I.η (v j a) ζ * I.η (v j b) ζ ∂I.P)) -
         Q' ω) ^ 2 ∂I.P) atTop (𝓝 0)) :
    ∃ (C : (j : ℕ) → Fin (r j + s j) → Fin (r j + s j) → ℝ)
      (w : (j : ℕ) → Fin (r j + s j) → Euc d → ℝ),
      (∀ j, IsR2FiniteRankData (C j) (w j)) ∧
      Tendsto (fun j => eLpNorm
        (fun z : Euc d × Euc d =>
          r2FiniteRankKernel (C j) (w j) z.1 z.2 -
            (h z.1 z.2 + h' z.1 z.2))
        2 (μ.prod μ)) atTop (𝓝 0) ∧
      Tendsto (fun j : ℕ => ∫ ω : I.Ω,
        (((1 / 2 : ℝ) * ∑ a : Fin (r j + s j), ∑ b : Fin (r j + s j), C j a b *
            (I.η (w j a) ω * I.η (w j b) ω -
              ∫ ζ, I.η (w j a) ζ * I.η (w j b) ζ ∂I.P)) -
           (Q ω + Q' ω)) ^ 2 ∂I.P) atTop (𝓝 0) := by
  classical
  letI := I.mΩ
  letI := I.prob
  have hblock : ∀ j, ∃ (C : Fin (r j + s j) → Fin (r j + s j) → ℝ)
      (w : Fin (r j + s j) → Euc d → ℝ),
      IsR2FiniteRankData C w ∧
      (∀ x y, r2FiniteRankKernel C w x y =
        r2FiniteRankKernel (c j) (u j) x y +
        r2FiniteRankKernel (c' j) (v j) x y) ∧
      (∀ ω : I.Ω,
        (1 / 2 : ℝ) * ∑ a : Fin (r j + s j), ∑ b : Fin (r j + s j), C a b *
          (I.η (w a) ω * I.η (w b) ω -
            ∫ ζ, I.η (w a) ζ * I.η (w b) ζ ∂I.P) =
        (1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j), c j a b *
          (I.η (u j a) ω * I.η (u j b) ω -
            ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P) +
        (1 / 2 : ℝ) * ∑ a : Fin (s j), ∑ b : Fin (s j), c' j a b *
          (I.η (v j a) ω * I.η (v j b) ω -
            ∫ ζ, I.η (v j a) ζ * I.η (v j b) ζ ∂I.P)) := by
    intro j
    exact pro_s13_generic_finite_rank_add I (c j) (u j) (c' j) (v j) (hd j) (hd' j)
  choose C w hdata heqKernel heqGaussian using hblock
  let F : ℕ → I.Ω → ℝ := fun j ω =>
    (1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j), c j a b *
      (I.η (u j a) ω * I.η (u j b) ω -
        ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P)
  let G : ℕ → I.Ω → ℝ := fun j ω =>
    (1 / 2 : ℝ) * ∑ a : Fin (s j), ∑ b : Fin (s j), c' j a b *
      (I.η (v j a) ω * I.η (v j b) ω -
        ∫ ζ, I.η (v j a) ζ * I.η (v j b) ζ ∂I.P)
  have hFm : ∀ j, MemLp (F j) 2 I.P := by
    intro j
    have hu : ∀ a, MemLp (u j a) 2 μ :=
      fun a => ((hd j).smooth a).continuous.memLp_of_hasCompactSupport
        ((hd j).compactSupport a)
    exact s21t4_generic_product_finite_rank_quadratic_L2 I (u j) hu (c j)
  have hGm : ∀ j, MemLp (G j) 2 I.P := by
    intro j
    have hv : ∀ a, MemLp (v j a) 2 μ :=
      fun a => ((hd' j).smooth a).continuous.memLp_of_hasCompactSupport
        ((hd' j).compactSupport a)
    exact s21t4_generic_product_finite_rank_quadratic_L2 I (v j) hv (c' j)
  have hL2 : Tendsto (fun j => ∫ ω : I.Ω,
      (F j ω + G j ω - (Q ω + Q' ω)) ^ 2 ∂I.P)
      atTop (𝓝 0) :=
    pro_s13_integral_sq_sum_limits F G Q Q' hFm hGm hQ hQ' hlim hlim'
  have hKernel : Tendsto (fun j => eLpNorm
      (fun z : Euc d × Euc d =>
        (r2FiniteRankKernel (c j) (u j) z.1 z.2 +
          r2FiniteRankKernel (c' j) (v j) z.1 z.2) -
          (h z.1 z.2 + h' z.1 z.2))
      2 (μ.prod μ)) atTop (𝓝 0) :=
    pro_s13_kernel_approximation_add
      (fun j => r2FiniteRankKernel (c j) (u j))
      (fun j => r2FiniteRankKernel (c' j) (v j)) h h' hK hK'
  refine ⟨C, w, hdata, ?_, ?_⟩
  · have heq : (fun j => eLpNorm
        (fun z : Euc d × Euc d =>
          r2FiniteRankKernel (C j) (w j) z.1 z.2 -
            (h z.1 z.2 + h' z.1 z.2))
        2 (μ.prod μ)) =
      (fun j => eLpNorm
        (fun z : Euc d × Euc d =>
          (r2FiniteRankKernel (c j) (u j) z.1 z.2 +
            r2FiniteRankKernel (c' j) (v j) z.1 z.2) -
            (h z.1 z.2 + h' z.1 z.2))
        2 (μ.prod μ)) := by
      funext j
      congr 1
      funext z
      rw [heqKernel j z.1 z.2]
    rw [heq]
    exact hKernel
  · have heq : (fun j : ℕ => ∫ ω : I.Ω,
        (((1 / 2 : ℝ) * ∑ a : Fin (r j + s j), ∑ b : Fin (r j + s j), C j a b *
            (I.η (w j a) ω * I.η (w j b) ω -
              ∫ ζ, I.η (w j a) ζ * I.η (w j b) ζ ∂I.P)) -
           (Q ω + Q' ω)) ^ 2 ∂I.P) =
      (fun j => ∫ ω : I.Ω,
        (F j ω + G j ω - (Q ω + Q' ω)) ^ 2 ∂I.P) := by
      funext j
      apply integral_congr_ae
      exact ae_of_all _ fun ω =>
        congrArg (fun z : ℝ => (z - (Q ω + Q' ω)) ^ 2) (heqGaussian j ω)
    rw [heq]
    exact hL2

end HRS.MS.R26T3
