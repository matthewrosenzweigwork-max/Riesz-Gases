import HRS.MC.CepE4
import HRS.MC.CepE2Aux2

/-!
# Packet CEPE5B, auxiliary 1: the Hessian of the pair potential `Φ` on the alcove

`h1 = (a/N)(-π cot πu)` is the derivative of the pair profile; `h1' = (a/N) π² / sin²(πu)`.  On the open alcove
`∇Φ = pairGrad h1` is `C¹` with derivative `H_y u = ∑_{k<l} h1'(y_l - y_k) ⟨e_l - e_k, u⟩ (e_l - e_k)`,
a symmetric positive semidefinite operator.
-/

open Set
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE5b

open HRS.MC.Cepa
open HRS.MC.CepE1 (cepe1_h1 cepe1_pairGrad cepe1_vec cepe1_inner_vec)

variable {N : ℕ}

/-- Derivative of the pair force profile `h1`. -/
def e5b_h1' (a : ℝ) (N : ℕ) (u : ℝ) : ℝ := (a / N) * (Real.pi ^ 2 / Real.sin (Real.pi * u) ^ 2)

theorem e5b_h1'_nonneg {a : ℝ} (ha : 0 ≤ a) (u : ℝ) : 0 ≤ e5b_h1' a N u := by
  unfold e5b_h1'; positivity

theorem e5b_hasDerivAt_h1 (a : ℝ) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (cepe1_h1 a N) (e5b_h1' a N u) u := by
  have hs : Real.sin (Real.pi * u) ≠ 0 := (HRS.MC.CepE2.cepe2_sin_pos hu).ne'
  have h1 : HasDerivAt (fun u : ℝ => Real.pi * u) Real.pi u := by
    simpa using (hasDerivAt_id u).const_mul Real.pi
  have hc : HasDerivAt (fun u : ℝ => Real.cos (Real.pi * u)) (-Real.sin (Real.pi * u) * Real.pi) u :=
    (Real.hasDerivAt_cos _).comp u h1
  have hsn : HasDerivAt (fun u : ℝ => Real.sin (Real.pi * u)) (Real.cos (Real.pi * u) * Real.pi) u :=
    (Real.hasDerivAt_sin _).comp u h1
  have hq := hc.div hsn hs
  have := ((hq.const_mul Real.pi).neg).const_mul (a / N)
  unfold cepe1_h1 e5b_h1'
  convert this using 1
  have hsc := Real.sin_sq_add_cos_sq (Real.pi * u)
  rw [show (-Real.sin (Real.pi * u) * Real.pi * Real.sin (Real.pi * u) -
      Real.cos (Real.pi * u) * (Real.cos (Real.pi * u) * Real.pi)) =
      -Real.pi * (Real.sin (Real.pi * u) ^ 2 + Real.cos (Real.pi * u) ^ 2) by ring, hsc]
  field_simp

theorem e5b_contDiffAt_h1 (a : ℝ) {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 1 (cepe1_h1 a N) u := by
  have hs : Real.sin (Real.pi * u) ≠ 0 := (HRS.MC.CepE2.cepe2_sin_pos hu).ne'
  unfold cepe1_h1
  refine contDiffAt_const.mul (ContDiffAt.neg (contDiffAt_const.mul ?_))
  refine ContDiffAt.div ?_ ?_ hs
  · exact (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)).contDiffAt
  · exact (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).contDiffAt

theorem e5b_gap {y : Ch N} (hy : y ∈ cep_Alcove N) {k l : Fin N} (hkl : k < l) :
    y l - y k ∈ Ioo (0 : ℝ) 1 :=
  HRS.MC.CepE2.cepe2_mem_alcove_iff.1 hy k l hkl

theorem e5b_contDiffAt_pg (a : ℝ) {y : Ch N} (hy : y ∈ cep_Alcove N) :
    ContDiffAt ℝ 1 (cepe1_pairGrad (cepe1_h1 a N)) y := by
  unfold cepe1_pairGrad
  refine ContDiffAt.sum fun k _ => ContDiffAt.sum fun l _ => ?_
  by_cases hkl : k < l
  · simp only [hkl, ite_true]
    have hg : ContDiffAt ℝ 1 (fun z : Ch N => z l - z k) y :=
      (((EuclideanSpace.proj l : Ch N →L[ℝ] ℝ).contDiff).sub
        ((EuclideanSpace.proj k : Ch N →L[ℝ] ℝ).contDiff)).contDiffAt
    have hh := (e5b_contDiffAt_h1 (N := N) a (e5b_gap hy hkl)).comp y hg
    exact hh.smul contDiffAt_const
  · simp only [hkl, ite_false]
    exact contDiffAt_const

/-- The Hessian operator of `Φ` at `y`. -/
def e5b_Hop (a : ℝ) (N : ℕ) (y : Ch N) : Ch N →L[ℝ] Ch N :=
  ∑ k, ∑ l, if k < l then (e5b_h1' a N (y l - y k)) • (innerSL ℝ (cepe1_vec k l)).smulRight (cepe1_vec k l)
    else 0

theorem e5b_hasFDerivAt_pg (a : ℝ) {y : Ch N} (hy : y ∈ cep_Alcove N) :
    HasFDerivAt (cepe1_pairGrad (cepe1_h1 a N)) (e5b_Hop a N y) y := by
  have key : ∀ k l : Fin N, HasFDerivAt
      (fun z : Ch N => if k < l then cepe1_h1 a N (z l - z k) • cepe1_vec k l else 0)
      (if k < l then (e5b_h1' a N (y l - y k)) • (innerSL ℝ (cepe1_vec k l)).smulRight (cepe1_vec k l)
        else 0) y := by
    intro k l
    by_cases hkl : k < l
    · simp only [hkl, ite_true]
      have hd := e5b_hasDerivAt_h1 (N := N) a (e5b_gap hy hkl)
      have hin : HasFDerivAt (fun z : Ch N => z l - z k) (innerSL ℝ (cepe1_vec k l)) y := by
        have := (innerSL ℝ (cepe1_vec k l)).hasFDerivAt (x := y)
        exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => by
          simp [cepe1_inner_vec])
      have := (hd.comp_hasFDerivAt y hin).smul_const (cepe1_vec k l)
      refine this.congr_fderiv ?_
      ext v
      simp [mul_assoc]
    · simp only [hkl, ite_false]
      exact hasFDerivAt_const _ _
  have hs := HasFDerivAt.sum (u := Finset.univ) (x := y)
    (A := fun k : Fin N => ∑ l : Fin N, fun z : Ch N => if k < l then cepe1_h1 a N (z l - z k) • cepe1_vec k l else 0)
    (A' := fun k => ∑ l : Fin N,
      (if k < l then (e5b_h1' a N (y l - y k)) • (innerSL ℝ (cepe1_vec k l)).smulRight (cepe1_vec k l) else 0))
    (fun k _ => HasFDerivAt.sum (fun l _ => key k l))
  have hfun : cepe1_pairGrad (cepe1_h1 a N) = ∑ k : Fin N, ∑ l : Fin N, fun z : Ch N =>
      if k < l then cepe1_h1 a N (z l - z k) • cepe1_vec k l else 0 := by
    funext z
    simp [cepe1_pairGrad, Finset.sum_apply]
  rw [hfun]
  exact hs

/-- The quadratic form of the Hessian. -/
def e5b_hq (a : ℝ) (N : ℕ) (y u v : Ch N) : ℝ :=
  ∑ k, ∑ l, if k < l then e5b_h1' a N (y l - y k) * ((u l - u k) * (v l - v k)) else 0

theorem e5b_inner_Hop (a : ℝ) (y u v : Ch N) : inner ℝ (e5b_Hop a N y u) v = e5b_hq a N y u v := by
  unfold e5b_Hop e5b_hq
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, sum_inner]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hkl : k < l
  · simp only [hkl, ite_true, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply, real_inner_smul_left, cepe1_inner_vec]
  · simp [hkl]

theorem e5b_hq_comm (a : ℝ) (y u v : Ch N) : e5b_hq a N y u v = e5b_hq a N y v u := by
  unfold e5b_hq
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> ring

theorem e5b_hq_nonneg {a : ℝ} (ha : 0 ≤ a) (y u : Ch N) : 0 ≤ e5b_hq a N y u u := by
  unfold e5b_hq
  refine Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => ?_
  split_ifs
  · exact mul_nonneg (e5b_h1'_nonneg ha _) (by nlinarith [sq_nonneg (u l - u k)])
  · exact le_rfl

end HRS.MC.CepE5b
