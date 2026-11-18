import HRS.Kernel.ResponseAux

/-!
# Lemma 7.5, `q08_gibbs_approx`: the abstract resolvent estimate (prefix `q08gl_`)

In a real Hilbert space `H`, let `T = 1 + β P K P` (`K` symmetric, `P` an orthogonal projection), with
inverse `R` (a self-adjoint contraction), and let `u_0, …, u_{m-1}` be orthonormal vectors in `ran P`. Put
`K^U_{jk} = ⟨u_j, K u_k⟩`, `Σ_{kl} = ⟨u_k, R u_l⟩`, `w_j = (1 - Π) P K u_j` with `Π` the projection onto
`span u`. Then `(1 + β K^U) Σ - 1 = -β [⟨w_j, R u_l⟩]` and `∑_{jl} ⟨w_j, R u_l⟩² ≤ ∑_j ‖w_j‖²`.
-/

open InnerProductSpace
open scoped BigOperators

noncomputable section

namespace HRS.Q08

section AbstractResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The inverse of a self-adjoint coercive operator is a self-adjoint contraction. -/
theorem q08gl_inv_op (T : H →L[ℝ] H) (hs : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y))
    (hc : ∀ x, ‖x‖ * ‖x‖ ≤ inner ℝ (T x) x) :
    ∃ R : H →L[ℝ] H, (∀ x, T (R x) = x) ∧ (∀ x, R (T x) = x) ∧ (∀ x, ‖R x‖ ≤ ‖x‖) ∧
      (∀ x y, inner ℝ (R x) y = inner ℝ x (R y)) := by
  have hbij := HRS.ResponseAux.bijective_of_coercive T hc
  let e : H ≃L[ℝ] H := ContinuousLinearEquiv.ofBijective T
    (LinearMap.ker_eq_bot.2 hbij.1) (LinearMap.range_eq_top.2 hbij.2)
  have he : ∀ x, e x = T x := fun x => rfl
  refine ⟨(e.symm : H →L[ℝ] H), fun x => ?_, fun x => ?_, fun x => ?_, fun x y => ?_⟩
  · rw [← he]; simp
  · have : e.symm (T x) = x := by rw [← he]; exact e.symm_apply_apply x
    exact this
  · show ‖e.symm x‖ ≤ ‖x‖
    have h1 : ‖e.symm x‖ * ‖e.symm x‖ ≤ ‖x‖ * ‖e.symm x‖ := by
      have h2 := hc (e.symm x)
      have h3 : T (e.symm x) = x := by rw [← he]; simp
      rw [h3] at h2
      exact h2.trans (real_inner_le_norm _ _)
    by_cases h0 : ‖e.symm x‖ = 0
    · rw [h0]; exact norm_nonneg _
    · exact le_of_mul_le_mul_right h1 (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))
  · have h3 : ∀ z, T (e.symm z) = z := fun z => by rw [← he]; simp
    calc inner ℝ (e.symm x) y = inner ℝ (e.symm x) (T (e.symm y)) := by rw [h3]
      _ = inner ℝ (T (e.symm x)) (e.symm y) := (hs _ _).symm
      _ = inner ℝ x (e.symm y) := by rw [h3]

/-- The resolvent identity on `span u` and its Frobenius estimate. -/
theorem q08gl_abstract_est {m : ℕ} (K P R : H →L[ℝ] H) (β : ℝ)
    (hKs : ∀ x y, inner ℝ (K x) y = inner ℝ x (K y))
    (hP2 : ∀ x, P (P x) = P x) (hPs : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y))
    (hR : ∀ x, R x + β • P (K (P (R x))) = x) (hRc : ∀ x, ‖R x‖ ≤ ‖x‖)
    (hRs : ∀ x y, inner ℝ (R x) y = inner ℝ x (R y))
    (u : Fin m → H) (hu : Orthonormal ℝ u) (hPu : ∀ k, P (u k) = u k) :
    ∑ j, ∑ l, ((inner ℝ (u j) (R (u l)) + β * ∑ k, inner ℝ (u j) (K (u k)) * inner ℝ (u k) (R (u l))) -
        (if j = l then 1 else 0)) ^ 2 ≤
      β ^ 2 * ∑ j, ‖P (K (u j)) - ∑ k, inner ℝ (u k) (P (K (u j))) • u k‖ ^ 2 := by
  classical
  set w : Fin m → H := fun j => P (K (u j)) - ∑ k, inner ℝ (u k) (P (K (u j))) • u k with hw
  have hRu : ∀ l, R (u l) = u l - β • P (K (P (R (u l)))) := fun l => eq_sub_of_add_eq (hR (u l))
  have hPV : ∀ l, P (R (u l)) = R (u l) := fun l => by
    have h1 : P (R (u l)) = P (u l - β • P (K (P (R (u l))))) := by rw [← hRu l]
    rw [h1, map_sub, map_smul, hP2, hPu, ← hRu l]
  have hortho : ∀ j l, inner ℝ (u j) (u l) = if j = l then (1 : ℝ) else 0 := fun j l =>
    orthonormal_iff_ite.1 hu j l
  -- Step 1
  have step1 : ∀ j l, inner ℝ (u j) (R (u l)) = (if j = l then (1 : ℝ) else 0) - β * inner ℝ (K (u j)) (R (u l)) := by
    intro j l
    have h := congrArg (fun z => inner ℝ (u j) z) (hR (u l))
    simp only [inner_add_right, real_inner_smul_right, hPV l] at h
    have h2 : inner ℝ (u j) (P (K (R (u l)))) = inner ℝ (K (u j)) (R (u l)) := by
      rw [← hPs, hPu, ← hKs]
    rw [h2, hortho] at h
    linarith
  -- Step 2 and 3
  have step3 : ∀ j l, (inner ℝ (u j) (R (u l)) + β * ∑ k, inner ℝ (u j) (K (u k)) * inner ℝ (u k) (R (u l))) -
      (if j = l then (1 : ℝ) else 0) = -β * inner ℝ (w j) (R (u l)) := by
    intro j l
    have e1 : ∑ k, inner ℝ (u j) (K (u k)) * inner ℝ (u k) (R (u l)) =
        inner ℝ (K (u j)) (∑ k, inner ℝ (u k) (R (u l)) • u k) := by
      rw [inner_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [real_inner_smul_right, ← hKs]; ring
    have e2 : inner ℝ (w j) (R (u l)) = inner ℝ (K (u j)) (R (u l)) -
        inner ℝ (K (u j)) (∑ k, inner ℝ (u k) (R (u l)) • u k) := by
      simp only [hw]
      rw [inner_sub_left, sum_inner, inner_sum, hPs (K (u j)) (R (u l)), hPV l]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [real_inner_smul_left, real_inner_smul_right, ← hPs, hPu, real_inner_comm (u k) (K (u j))]
      ring
    rw [step1 j l, e1, e2]
    ring
  simp_rw [step3]
  -- Bessel
  have hbes : ∀ j, ∑ l, inner ℝ (w j) (R (u l)) ^ 2 ≤ ‖w j‖ ^ 2 := by
    intro j
    have h := hu.sum_inner_products_le (R (w j)) (s := Finset.univ)
    refine le_trans (le_of_eq ?_) (h.trans (pow_le_pow_left₀ (norm_nonneg _) (hRc _) 2))
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Real.norm_eq_abs, sq_abs, real_inner_comm, ← hRs, real_inner_comm]
  calc ∑ j, ∑ l, (-β * inner ℝ (w j) (R (u l))) ^ 2 = ∑ j, β ^ 2 * ∑ l, inner ℝ (w j) (R (u l)) ^ 2 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring
    _ ≤ ∑ j, β ^ 2 * ‖w j‖ ^ 2 :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hbes j) (sq_nonneg _)
    _ = β ^ 2 * ∑ j, ‖w j‖ ^ 2 := by rw [Finset.mul_sum]

end AbstractResolvent

end HRS.Q08

end
