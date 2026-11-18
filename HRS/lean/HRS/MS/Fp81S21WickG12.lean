import HRS.MS.Fp81S21WickG11
import HRS.MS.S21T4ProdX

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open HRS (Euc)

namespace HRS.Fp81.S21

/-- Tensor products of a finite orthonormal family form an orthonormal family
in the product `L²` space; consequently a finite tensor expansion has the
coefficient norm as its exact product-space norm. -/
theorem fp81s21_wickG_orthonormal_tensor_norm
    {d q : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    (e : Fin q → Lp ℝ 2 μ) (he : Orthonormal ℝ e)
    (c : Fin q → Fin q → ℝ) :
    MemLp (fun z : Euc d × Euc d =>
      ∑ a, ∑ b, c a b * (e a) z.1 * (e b) z.2) 2 (μ.prod μ) ∧
    ∫ z : Euc d × Euc d,
      (∑ a, ∑ b, c a b * (e a) z.1 * (e b) z.2) ^ 2 ∂(μ.prod μ) =
      ∑ a, ∑ b, c a b ^ 2 := by
  classical
  let tmem : ∀ a b : Fin q, MemLp
      (fun z : Euc d × Euc d => (e a) z.1 * (e b) z.2) 2 (μ.prod μ) := by
    intro a b
    exact HRS.MS.R26T3.s21t4_separated_kernel_memLp (e a) (e b)
      (Lp.memLp (e a)) (Lp.memLp (e b))
  let T : Fin q → Fin q → Lp ℝ 2 (μ.prod μ) := fun a b =>
    (tmem a b).toLp (fun z => (e a) z.1 * (e b) z.2)
  have hTinner : ∀ a b a' b',
      inner ℝ (T a b) (T a' b') =
        (if a = a' then 1 else 0) * (if b = b' then 1 else 0) := by
    intro a b a' b'
    rw [L2.inner_def]
    have hae : (fun z : Euc d × Euc d => (T a' b') z * (T a b) z) =ᵐ[μ.prod μ]
        fun z => ((e a') z.1 * (e a) z.1) * ((e b') z.2 * (e b) z.2) := by
      filter_upwards [(tmem a b).coeFn_toLp, (tmem a' b').coeFn_toLp]
        with z hz hz'
      rw [hz', hz]
      ring
    simp only [RCLike.inner_apply, conj_trivial]
    rw [integral_congr_ae hae]
    calc
      ∫ z : Euc d × Euc d,
          ((e a') z.1 * (e a) z.1) * ((e b') z.2 * (e b) z.2) ∂(μ.prod μ) =
        (∫ x, (e a') x * (e a) x ∂μ) *
          (∫ y, (e b') y * (e b) y ∂μ) := by
            exact integral_prod_mul
              (fun x => (e a') x * (e a) x)
              (fun y => (e b') y * (e b) y)
      _ = inner ℝ (e a) (e a') * inner ℝ (e b) (e b') := by
            rw [L2.inner_def, L2.inner_def]
            simp only [RCLike.inner_apply, conj_trivial]
      _ = (if a = a' then 1 else 0) * (if b = b' then 1 else 0) := by
            rw [orthonormal_iff_ite.mp he, orthonormal_iff_ite.mp he]
  let V : Fin q × Fin q → Lp ℝ 2 (μ.prod μ) := fun p => T p.1 p.2
  have hV : Orthonormal ℝ V := by
    rw [orthonormal_iff_ite]
    intro p p'
    change inner ℝ (T p.1 p.2) (T p'.1 p'.2) = if p = p' then 1 else 0
    rw [hTinner]
    rcases p with ⟨a, b⟩
    rcases p' with ⟨a', b'⟩
    by_cases h₁ : a = a' <;> by_cases h₂ : b = b' <;>
      simp [Prod.ext_iff, h₁, h₂]
  have hVorth := orthonormal_iff_ite.mp hV
  let D : Fin q × Fin q → ℝ := fun p => c p.1 p.2
  let K : Lp ℝ 2 (μ.prod μ) := ∑ p, D p • V p
  have hKnorm : ‖K‖ ^ 2 = ∑ a, ∑ b, c a b ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    change inner ℝ (∑ p, D p • V p) (∑ p, D p • V p) = _
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real]
    simp [D, hVorth, mul_ite, Fintype.sum_prod_type, sq]
  have hKmem : MemLp (fun z : Euc d × Euc d =>
      ∑ a, ∑ b, c a b * (e a) z.1 * (e b) z.2) 2 (μ.prod μ) := by
    refine memLp_finsetSum _ fun a _ => memLp_finsetSum _ fun b _ => ?_
    simpa [mul_assoc] using (tmem a b).const_mul (c a b)
  have hKae : K =ᵐ[μ.prod μ] fun z : Euc d × Euc d =>
      ∑ a, ∑ b, c a b * (e a) z.1 * (e b) z.2 := by
    have hsum : K =ᵐ[μ.prod μ] fun z => ∑ p, D p * (V p) z := by
      have h1 : K =ᵐ[μ.prod μ] fun z => ∑ p, (D p • V p) z := by
        simpa [K] using HRS.A33.a33_coeFn_sum (P := μ.prod μ) Finset.univ
          (fun p => D p • V p)
      have h2 : ∀ᵐ z ∂(μ.prod μ), ∀ p : Fin q × Fin q,
          (D p • V p) z = D p * (V p) z := by
        rw [ae_all_iff]
        intro p
        filter_upwards [Lp.coeFn_smul (D p) (V p)] with z hz
        simpa [smul_eq_mul] using hz
      filter_upwards [h1, h2] with z hz hp
      rw [hz]
      exact Finset.sum_congr rfl fun p _ => hp p
    have hTae : ∀ p : Fin q × Fin q, (V p) =ᵐ[μ.prod μ]
        fun z => (e p.1) z.1 * (e p.2) z.2 := by
      intro p
      exact (tmem p.1 p.2).coeFn_toLp
    have hprod : ∀ᵐ z ∂(μ.prod μ), ∀ p : Fin q × Fin q,
        (V p) z = (e p.1) z.1 * (e p.2) z.2 := by
      rw [ae_all_iff]
      intro p
      exact hTae p
    filter_upwards [hsum, hprod] with z hz hp
    rw [hz, Fintype.sum_prod_type]
    simp_rw [hp]
    simp [D, mul_assoc]
  refine ⟨hKmem, ?_⟩
  calc
    ∫ z : Euc d × Euc d,
        (∑ a, ∑ b, c a b * (e a) z.1 * (e b) z.2) ^ 2 ∂(μ.prod μ) =
        inner ℝ K K := by
          rw [L2.inner_def]
          simp only [RCLike.inner_apply, conj_trivial]
          exact integral_congr_ae (hKae.mono fun z hz => by
            have h := congrArg (fun r : ℝ => r ^ 2) hz
            simpa [pow_two] using h.symm)
    _ = ‖K‖ ^ 2 := real_inner_self_eq_norm_sq K
    _ = ∑ a, ∑ b, c a b ^ 2 := hKnorm

#print axioms fp81s21_wickG_orthonormal_tensor_norm

end HRS.Fp81.S21

end
