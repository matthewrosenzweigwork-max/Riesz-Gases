import HRS.Equilibrium.StaticLimits
import HRS.Equilibrium.QuadraticLimit.ChaosAuxA
import HRS.Equilibrium.QuadraticLimit.ChaosAuxB
import HRS.Equilibrium.QuadraticLimit.ChaosAuxC
import HRS.Equilibrium.QuadraticLimit.ChaosAuxD
import HRS.Equilibrium.QuadraticLimit.ChaosAuxE

/-!
# Lemma 7.5 `quadratic_limit`: Gaussian space and second chaos (packet Q08, sub-packet `Chaos`)

Skeleton file (statements only, `sorry`-ed, all TRUE as written). Purely probabilistic and abstract:
no torus. A covariance matrix `C` on `ℕ` (nonnegative, `C ≤ I`), a Hilbert-Schmidt symmetric matrix `H`
and `ℓ²` coefficient vectors `a`. These are instantiated with `q08Cmat`, `q08Hmat`, `q08Coef`.

* `q08_chaos_exists`: the probability space of the conclusion of Lemma 7.5: a family `G_i` that is jointly
  Gaussian with covariance `C` (finite-dimensional marginals), the `L²` limit `Lin_a` of `∑_i a_{ai} G_i`
  and the `L²` limit `Q` of the Wick-centred quadratic forms `½ ∑_{i,j<L} H_ij (G_iG_j - C_ij)`.
  Route: product measure of standard Gaussians (`Measure.infinitePi`) and the consistent Cholesky factors
  of the finite sections of `C`; `L²` Cauchy by `q08_chaos_l2_bound`; pick measurable representatives.
* `q08_chaos_l2_bound`: `E[(½ ∑ A_ij (G_iG_j - C_ij))²] = ½ tr(ACAC) ≤ ½ ‖A‖²_F` for `C ≤ I`
  (Isserlis, via `G = C^{1/2} ξ`, `ξ` standard Gaussian).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Q08

/-- Hypotheses on a covariance matrix `C` on `ℕ`: symmetric, nonnegative and bounded by the identity. -/
structure q08_IsCov (C : ℕ → ℕ → ℝ) : Prop where
  symm : ∀ i j, C i j = C j i
  psd : ∀ (n : ℕ) (v : ℕ → ℝ), 0 ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * C i j
  le_one : ∀ (n : ℕ) (v : ℕ → ℝ),
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * C i j ≤ ∑ i ∈ Finset.range n, v i ^ 2

/-- The probability space, the Gaussian family and the two `L²` limits of the conclusion of Lemma 7.5. -/
theorem q08_chaos_exists {p : ℕ} (C H : ℕ → ℕ → ℝ) (a : Fin p → ℕ → ℝ) (hC : q08_IsCov C)
    (hHs : ∀ i j, H i j = H j i) (hH : Summable (fun ij : ℕ × ℕ => H ij.1 ij.2 ^ 2))
    (ha : ∀ b, Summable (fun i => a b i ^ 2)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (G : ℕ → Ω → ℝ) (Q : Ω → ℝ) (Lin : Fin p → Ω → ℝ),
      (∀ i, Measurable (G i)) ∧ Measurable Q ∧ (∀ b, Measurable (Lin b)) ∧
      (∀ n : ℕ, law P (fun ω => (WithLp.toLp 2 fun i : Fin n => G i ω : EuclideanSpace ℝ (Fin n))) =
        multivariateGaussian 0 (Matrix.of fun i j : Fin n => C i j)) ∧
      (∀ b, Tendsto (fun L => ∫⁻ ω, ‖Lin b ω - ∑ i ∈ Finset.range L, a b i * G i ω‖ₑ ^ 2 ∂P)
        atTop (𝓝 0)) ∧
      Tendsto (fun L => ∫⁻ ω, ‖Q ω - (1 / 2) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
          H i j * (G i ω * G j ω - C i j)‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
  obtain ⟨L, hLs, hLg⟩ := q08c_ch_cholesky C hC.symm hC.psd hC.le_one
  have hset : q08c_ch_Setup (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) (q08c_ch_Gfam L) C :=
    ⟨q08c_ch_Gfam_meas L, hC.symm, hC.psd, hC.le_one,
      fun n => q08c_ch_law C hC.symm hC.psd hC.le_one L hLs hLg n⟩
  obtain ⟨Q, hQm, hQ⟩ := q08c_ch_quad_limit hset H hHs hH
  choose Lin hLinm hLin using fun b => q08c_ch_lin_limit hset (a b) (ha b)
  exact ⟨ℕ → ℝ, inferInstance, Measure.infinitePi fun _ : ℕ => gaussianReal 0 1, inferInstance,
    q08c_ch_Gfam L, Q, Lin, hset.meas, hQm, hLinm, hset.law, hLin, hQ⟩

/-- Measurable version of `q08_chaos_l2_bound` (the stated version also admits non-measurable families
in the degenerate case `C_n = 0`, where `law` of a non-a.e.-measurable map is a junk Dirac mass). -/
theorem q08c_chaos_l2_bound_meas {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ → Ω → ℝ) (hG : ∀ i, Measurable (G i)) (C : ℕ → ℕ → ℝ) (hC : q08_IsCov C) (n : ℕ)
    (hlaw : law P (fun ω => (WithLp.toLp 2 fun i : Fin n => G i ω : EuclideanSpace ℝ (Fin n))) =
      multivariateGaussian 0 (Matrix.of fun i j : Fin n => C i j))
    (A : Fin n → Fin n → ℝ) (hA : ∀ i j, A i j = A j i) :
    ∫ ω, ((1 / 2) * ∑ i : Fin n, ∑ j : Fin n, A i j * (G i ω * G j ω - C i j)) ^ 2 ∂P ≤
      (1 / 2) * ∑ i : Fin n, ∑ j : Fin n, A i j ^ 2 := by
  exact q08c_ch_bound_raw P G hG C hC.symm hC.psd hC.le_one n hlaw A hA

/-- Second-moment bound for the Wick-centred quadratic form of a finite Gaussian vector with covariance
`C ≤ I`: `E[(½ ∑_{ij} A_ij (G_iG_j - C_ij))²] = ½ tr(ACAC) ≤ ½ ∑ A_ij²` for symmetric `A`.
Technical hypothesis: `hG` (measurability of `G`); without it `law P` is a junk value and the bound fails
(docs/ISSUES.md §I, Q08-CHAOS). -/
theorem q08_chaos_l2_bound {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (G : ℕ → Ω → ℝ) (hG : ∀ i, Measurable (G i)) (C : ℕ → ℕ → ℝ) (hC : q08_IsCov C) (n : ℕ)
    (hlaw : law P (fun ω => (WithLp.toLp 2 fun i : Fin n => G i ω : EuclideanSpace ℝ (Fin n))) =
      multivariateGaussian 0 (Matrix.of fun i j : Fin n => C i j))
    (A : Fin n → Fin n → ℝ) (hA : ∀ i j, A i j = A j i) :
    ∫ ω, ((1 / 2) * ∑ i : Fin n, ∑ j : Fin n, A i j * (G i ω * G j ω - C i j)) ^ 2 ∂P ≤
      (1 / 2) * ∑ i : Fin n, ∑ j : Fin n, A i j ^ 2 :=
  q08c_chaos_l2_bound_meas P G hG C hC n hlaw A hA

end HRS.Q08

end
