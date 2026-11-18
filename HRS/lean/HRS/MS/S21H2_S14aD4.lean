import HRS.MS.S21G2_K11bA
import HRS.Whole.Q34Aux15

/-!
# S21H2, packet R26-T3.S14a (part D4): finite-rank partial sums converge in `L²(μ⊗μ)` (Pythagoras)

If `c ∈ L²(μ⊗μ)`, `(e_k)` is orthonormal in `L²(μ)`, `⟪c, e_k⊗e_k⟫ = λ_k` and `‖c‖² = ∑ λ_k²` (summable), then
`‖c - ∑_{k<n} λ_k e_k⊗e_k‖_{L²(μ⊗μ)} → 0` (computed in `L²(μ⊗μ)`: `‖c - S_n‖² = ‖c‖² - ∑_{k<n} λ_k²`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.R26T3

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}

theorem s21h2_L2_inner {f g : α → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂ν := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

theorem s21h2_coeFn_finsum {ι : Type*} (g : ι → ℝ) (w : ι → Lp ℝ 2 ν) (s : Finset ι) :
    ⇑(∑ j ∈ s, g j • w j) =ᵐ[ν] fun x => ∑ j ∈ s, g j * (w j : α → ℝ) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℝ 2 ν] with x hx
    simpa using hx
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (g a • w a) (∑ j ∈ s, g j • w j), Lp.coeFn_smul (g a) (w a), ih] with x h1 h2 h3
    rw [h1]
    simp only [Pi.add_apply, h2, h3, Pi.smul_apply, smul_eq_mul, Finset.sum_insert ha]

theorem s21h2_pyth {C : α → ℝ} (hC : MemLp C 2 ν) {P : ℕ → Lp ℝ 2 ν} (hP : Orthonormal ℝ P)
    (lam : ℕ → ℝ) (hCP : ∀ k, inner ℝ (hC.toLp C) (P k) = lam k)
    (hsum : Summable fun k => lam k ^ 2) (hC2 : ∫ x, C x ^ 2 ∂ν = ∑' k, lam k ^ 2) :
    Tendsto (fun n => ‖hC.toLp C - ∑ k ∈ Finset.range n, lam k • P k‖) atTop (𝓝 0) := by
  set Cl : Lp ℝ 2 ν := hC.toLp C with hCl
  have hnorm : ‖Cl‖ ^ 2 = ∑' k, lam k ^ 2 := by
    rw [← hC2, ← real_inner_self_eq_norm_sq, hCl, s21h2_L2_inner hC hC]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  have hn : ∀ n, ‖Cl - ∑ k ∈ Finset.range n, lam k • P k‖ ^ 2 =
      ∑' k, lam k ^ 2 - ∑ k ∈ Finset.range n, lam k ^ 2 := by
    intro n
    rw [norm_sub_sq_real, hnorm]
    have h1 : inner ℝ Cl (∑ k ∈ Finset.range n, lam k • P k) = ∑ k ∈ Finset.range n, lam k ^ 2 := by
      rw [inner_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [real_inner_smul_right, hCP]; ring
    have h2 : ‖∑ k ∈ Finset.range n, lam k • P k‖ ^ 2 = ∑ k ∈ Finset.range n, lam k ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, inner_sum]
      simp_rw [sum_inner, real_inner_smul_left, real_inner_smul_right]
      have := (orthonormal_iff_ite.1 hP)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k hk => ?_
      simp_rw [this, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq]
      simp [hk, sq]
    rw [h1, h2]; ring
  have ht : Tendsto (fun n => ∑' k, lam k ^ 2 - ∑ k ∈ Finset.range n, lam k ^ 2) atTop (𝓝 0) := by
    have := (hsum.hasSum.tendsto_sum_nat)
    have h := (tendsto_const_nhds (x := ∑' k, lam k ^ 2)).sub this
    rwa [sub_self] at h
  have hs : Tendsto (fun n => Real.sqrt (∑' k, lam k ^ 2 - ∑ k ∈ Finset.range n, lam k ^ 2)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp ht
    rw [Real.sqrt_zero] at h
    exact h
  refine hs.congr fun n => ?_
  rw [← hn n, Real.sqrt_sq (norm_nonneg _)]

end HRS.MS.R26T3
