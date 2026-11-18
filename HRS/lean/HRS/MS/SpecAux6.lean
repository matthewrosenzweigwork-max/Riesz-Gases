import Mathlib

/-!
# S8P: positivity of Cauchy-weighted compressions (generic, for the PSD-root lemma of S8.7)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_cauchy_psd`: for a positive operator `S` and an arbitrary family `b`, positive
numbers `a_i`, a finite index set `F` and real weights `w`, `∑_{i,j∈F} ⟨b_i, S b_j⟩ w_i w_j/(a_i+a_j) ≥ 0`
(since `1/(a_i+a_j) = ∫_0^∞ e^{-s a_i} e^{-s a_j} ds`).
-/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace HRS.MS.Spec

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem s8p_cauchy_psd (S : H →L[ℝ] H) (hSs : ∀ x y, ⟪S x, y⟫ = ⟪x, S y⟫) (hS : ∀ x, 0 ≤ ⟪S x, x⟫)
    {ι : Type*} (b : ι → H) (a : ι → ℝ) (ha : ∀ i, 0 < a i) (F : Finset ι) (w : ι → ℝ) :
    0 ≤ ∑ i ∈ F, ∑ j ∈ F, ⟪b i, S (b j)⟫ * w i * w j / (a i + a j) := by
  classical
  let u : ℝ → H := fun s => ∑ i ∈ F, (w i * Real.exp (-(a i) * s)) • b i
  have key : ∀ s, ⟪u s, S (u s)⟫ =
      ∑ i ∈ F, ∑ j ∈ F, (w i * w j * ⟪b i, S (b j)⟫) * Real.exp ((-(a i + a j)) * s) := by
    intro s
    simp only [u, map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : Real.exp ((-(a i + a j)) * s) = Real.exp (-(a i) * s) * Real.exp (-(a j) * s) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]; ring
  have hnn : ∀ s, 0 ≤ ⟪u s, S (u s)⟫ := fun s => by
    rw [real_inner_comm]; exact hS _
  have hint : ∀ i j, IntegrableOn
      (fun s : ℝ => (w i * w j * ⟪b i, S (b j)⟫) * Real.exp ((-(a i + a j)) * s)) (Ioi 0) :=
    fun i j => (integrableOn_exp_mul_Ioi (by linarith [ha i, ha j]) 0).const_mul _
  have h0 : 0 ≤ ∫ s in Ioi (0 : ℝ), ⟪u s, S (u s)⟫ :=
    setIntegral_nonneg measurableSet_Ioi fun s _ => hnn s
  simp_rw [key] at h0
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j] at h0
  convert h0 using 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith [ha i, ha j])]
  simp only [mul_zero, Real.exp_zero]
  have : a i + a j ≠ 0 := by linarith [ha i, ha j]
  field_simp

end HRS.MS.Spec
