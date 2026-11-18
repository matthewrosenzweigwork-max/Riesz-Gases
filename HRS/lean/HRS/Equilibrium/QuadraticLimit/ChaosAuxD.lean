import Mathlib
import HRS.Equilibrium.QuadraticLimit.ChaosAuxC

/-!
# Lemma 7.5: the Gaussian family on the infinite product (prefix `q08c_ch_`)

`Ω = ℕ → ℝ` with the product of standard Gaussians `Measure.infinitePi`, and
`G_i = ∑_{k ≤ i} L_ik ξ_k` for the Cholesky factor `L` of `C`; finite-dimensional marginals are
`N(0, C_n)`, checked on characteristic functions.
-/
open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal RealInnerProductSpace MatrixOrder

noncomputable section
namespace HRS.Q08

/-- The Gaussian family built from a lower triangular factor `L`. -/
def q08c_ch_Gfam (L : ℕ → ℕ → ℝ) (i : ℕ) (ω : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range (i + 1), L i k * ω k

theorem q08c_ch_Gfam_meas (L : ℕ → ℕ → ℝ) (i : ℕ) : Measurable (q08c_ch_Gfam L i) := by
  unfold q08c_ch_Gfam; fun_prop

theorem q08c_ch_Gfam_eq (L : ℕ → ℕ → ℝ) (hL : ∀ i k, i < k → L i k = 0) (n : ℕ) (i : Fin n)
    (ω : ℕ → ℝ) : q08c_ch_Gfam L i ω = ∑ k : Fin n, L i k * ω k := by
  unfold q08c_ch_Gfam
  rw [← Finset.sum_range (fun k => L i k * ω k)]
  refine Finset.sum_subset (fun k hk => ?_) (fun k hk hk' => ?_)
  · simp only [Finset.mem_range] at hk ⊢; have := i.2; omega
  · simp only [Finset.mem_range] at hk hk'
    rw [hL i k (by omega), zero_mul]

theorem q08c_ch_std_law (n : ℕ) :
    (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).map
      (fun ω => (WithLp.toLp 2 fun k : Fin n => ω k : EuclideanSpace ℝ (Fin n))) =
        stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  have h1 := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => (gaussianReal 0 1))
    (f := fun k : Fin n => (k : ℕ)) Fin.val_injective
  rw [Measure.infinitePi_eq_pi (μ := fun _ : Fin n => gaussianReal 0 1)] at h1
  rw [← map_pi_eq_stdGaussian, ← h1, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl


theorem q08c_ch_law (C : ℕ → ℕ → ℝ) (hsymm : ∀ i j, C i j = C j i)
    (hpsd : ∀ (n : ℕ) (v : ℕ → ℝ), 0 ≤ ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * C i j)
    (hle : ∀ (n : ℕ) (v : ℕ → ℝ), ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, v i * v j * C i j ≤
      ∑ i ∈ Finset.range n, v i ^ 2)
    (L : ℕ → ℕ → ℝ) (hLs : ∀ i k, i < k → L i k = 0)
    (hLg : ∀ i j N, i < N → j < N → ∑ k ∈ Finset.range N, L i k * L j k = C i j) (n : ℕ) :
    (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).map
      (fun ω => (WithLp.toLp 2 fun i : Fin n => q08c_ch_Gfam L i ω : EuclideanSpace ℝ (Fin n))) =
        multivariateGaussian 0 (Matrix.of fun i j : Fin n => C i j) := by
  set P := Measure.infinitePi fun _ : ℕ => gaussianReal 0 1 with hP
  have hS := (q08c_ch_cov_fin C hsymm hpsd hle n).1
  set ξ : (ℕ → ℝ) → EuclideanSpace ℝ (Fin n) := fun ω => WithLp.toLp 2 fun k : Fin n => ω k with hξ
  set V : (ℕ → ℝ) → EuclideanSpace ℝ (Fin n) :=
    fun ω => WithLp.toLp 2 fun i : Fin n => q08c_ch_Gfam L i ω with hV
  have hξm : Measurable ξ := by rw [hξ]; fun_prop
  have hVm : Measurable V := by
    rw [hV]
    exact (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp (measurable_pi_iff.2 fun i => q08c_ch_Gfam_meas L i)
  refine Measure.ext_of_charFun (funext fun t => ?_)
  set a : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 fun k : Fin n => ∑ i : Fin n, t i * L i k with ha
  have hpt : ∀ ω, ⟪V ω, t⟫ = ⟪ξ ω, a⟫ := by
    intro ω
    simp only [hV, hξ, ha, PiLp.inner_apply, q08c_ch_Gfam_eq L hLs n, RCLike.inner_apply, conj_trivial]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
  have h1 : charFun (P.map V) t = charFun (P.map ξ) a := by
    rw [charFun_apply, charFun_apply, integral_map hVm.aemeasurable (by fun_prop),
      integral_map hξm.aemeasurable (by fun_prop)]
    simp_rw [hpt]
  rw [h1, hP, q08c_ch_std_law n, charFun_stdGaussian, charFun_multivariateGaussian hS]
  have hnorm : ‖a‖ ^ 2 = t.ofLp ⬝ᵥ (Matrix.of fun i j : Fin n => C i j) *ᵥ t.ofLp := by
    rw [← q08c_ch_q_eq, EuclideanSpace.real_norm_sq_eq]
    have e1 : ∀ k : Fin n, (∑ i : Fin n, t i * L i k) ^ 2 =
        ∑ i : Fin n, ∑ j : Fin n, t i * t j * (L i k * L j k) := by
      intro k; rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    simp only [ha, e1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.mul_sum]
    have h := hLg i j n i.2 j.2
    rw [Finset.sum_range] at h
    rw [h]; rfl
  congr 1
  rw [← Complex.ofReal_pow, hnorm]
  simp
  ring

end HRS.Q08
