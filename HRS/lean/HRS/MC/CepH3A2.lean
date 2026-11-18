import HRS.MC.CepH3A1

/-!
# Packet CEPH3, part A2: gradient, tangent inequality and monotonicity of `cep_chamberPot 1 N` on the alcove
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepH3

open HRS HRS.MC.Cepa

variable {N : ℕ}

lemma h3a_pair_mem {z : Ch N} (hz : z ∈ cep_Alcove N) {k l : Fin N} (hkl : k < l) :
    z l - z k ∈ Ioo (0 : ℝ) 1 :=
  ⟨by linarith [hz.1 k l hkl], by linarith [hz.2 k l]⟩

lemma h3a_chamberPot_eq (z : Ch N) :
    cep_chamberPot 1 N z = (1 / (N : ℝ)) * ∑ k : Fin N, ∑ l : Fin N,
      if k < l then h3a_h (z l - z k) else 0 := by
  simp [cep_chamberPot, h3a_h]

/-- The explicit gradient vector of `cep_chamberPot 1 N` on the alcove. -/
def h3a_gam (z : Ch N) : Ch N :=
  (1 / (N : ℝ)) • ∑ k : Fin N, ∑ l : Fin N,
    if k < l then h3a_dh (z l - z k) • (EuclideanSpace.single l (1 : ℝ) - EuclideanSpace.single k (1 : ℝ) : Ch N)
    else 0

lemma h3a_inner_gam (z v : Ch N) :
    ⟪h3a_gam z, v⟫ = (1 / (N : ℝ)) * ∑ k : Fin N, ∑ l : Fin N,
      if k < l then h3a_dh (z l - z k) * (v l - v k) else 0 := by
  unfold h3a_gam
  rw [real_inner_smul_left, sum_inner]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sum_inner]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · rw [inner_smul_left, inner_sub_left]
    simp [EuclideanSpace.inner_single_left, mul_comm]
  · simp

lemma h3a_hasFDerivAt {z : Ch N} (hz : z ∈ cep_Alcove N) :
    HasFDerivAt (cep_chamberPot 1 N) (InnerProductSpace.toDual ℝ (Ch N) (h3a_gam z)) z := by
  have hterm : ∀ k l : Fin N, HasFDerivAt (fun w : Ch N => if k < l then h3a_h (w l - w k) else 0)
      (if k < l then h3a_dh (z l - z k) • ((EuclideanSpace.proj l : Ch N →L[ℝ] ℝ) -
        (EuclideanSpace.proj k : Ch N →L[ℝ] ℝ)) else 0) z := by
    intro k l
    by_cases hkl : k < l
    · simp only [hkl, ite_true]
      have hl : HasFDerivAt (fun w : Ch N => w l - w k)
          ((EuclideanSpace.proj l : Ch N →L[ℝ] ℝ) - (EuclideanSpace.proj k : Ch N →L[ℝ] ℝ)) z :=
        ((EuclideanSpace.proj l : Ch N →L[ℝ] ℝ).hasFDerivAt).sub
          ((EuclideanSpace.proj k : Ch N →L[ℝ] ℝ).hasFDerivAt)
      have key := (h3a_hasDerivAt (h3a_pair_mem hz hkl)).comp_hasFDerivAt z hl
      exact key
    · simp only [hkl, ite_false]
      exact hasFDerivAt_const _ _
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) (fun l _ => hterm k l))
  have hfull := hsum.const_mul (1 / (N : ℝ))
  have e1 : cep_chamberPot 1 N = fun w => (1 / (N : ℝ)) * ∑ k : Fin N, ∑ l : Fin N,
      if k < l then h3a_h (w l - w k) else 0 := by
    funext w; exact h3a_chamberPot_eq w
  rw [e1]
  convert hfull using 1
  ext v
  rw [InnerProductSpace.toDual_apply_apply, h3a_inner_gam]
  simp [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

lemma h3a_hasGradientAt {z : Ch N} (hz : z ∈ cep_Alcove N) :
    HasGradientAt (cep_chamberPot 1 N) (h3a_gam z) z := h3a_hasFDerivAt hz

lemma h3a_gradient_eq {z : Ch N} (hz : z ∈ cep_Alcove N) :
    gradient (cep_chamberPot 1 N) z = h3a_gam z := (h3a_hasGradientAt hz).gradient

/-- Tangent inequality (convexity) of the chamber potential on the alcove. -/
lemma h3a_tangent_pot {x y : Ch N} (hx : x ∈ cep_Alcove N) (hy : y ∈ cep_Alcove N) :
    cep_chamberPot 1 N x + ⟪h3a_gam x, y - x⟫ ≤ cep_chamberPot 1 N y := by
  rw [h3a_inner_gam, h3a_chamberPot_eq, h3a_chamberPot_eq, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun l _ => ?_
  by_cases hkl : k < l
  · simp only [hkl, ite_true]
    have := h3a_tangent (h3a_pair_mem hx hkl) (h3a_pair_mem hy hkl)
    simp only [PiLp.sub_apply]
    have e : (y.ofLp l - x.ofLp l) - (y.ofLp k - x.ofLp k) = (y.ofLp l - y.ofLp k) - (x.ofLp l - x.ofLp k) := by ring
    rw [e]; exact this
  · simp [hkl]

lemma h3a_gam_mono {x y : Ch N} (hx : x ∈ cep_Alcove N) (hy : y ∈ cep_Alcove N) :
    0 ≤ ⟪h3a_gam y - h3a_gam x, y - x⟫ := by
  have h1 := h3a_tangent_pot hx hy
  have h2 := h3a_tangent_pot hy hx
  rw [inner_sub_left]
  have : y - x = -(x - y) := by abel
  have h3 : ⟪h3a_gam y, y - x⟫ = -⟪h3a_gam y, x - y⟫ := by
    rw [← inner_neg_right, neg_sub]
  linarith

lemma h3a_pot_lower {z : Ch N} (hz : z ∈ cep_Alcove N) :
    -((N : ℝ) * Real.log 2) ≤ cep_chamberPot 1 N z := by
  rw [h3a_chamberPot_eq]
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0; simp
  have hterm : ∀ k l : Fin N, -Real.log 2 ≤ (if k < l then h3a_h (z l - z k) else 0) := by
    intro k l
    by_cases hkl : k < l
    · simp only [hkl, ite_true, h3a_h]
      have hs := h3a_sin_pos (h3a_pair_mem hz hkl)
      have : Real.log (2 * Real.sin (Real.pi * (z l - z k))) ≤ Real.log 2 :=
        Real.log_le_log (by positivity) (by nlinarith [Real.sin_le_one (Real.pi * (z l - z k))])
      linarith
    · simp only [hkl, ite_false]; linarith [Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)]
  have hsum : ∑ k : Fin N, ∑ l : Fin N, (-Real.log 2) ≤
      ∑ k : Fin N, ∑ l : Fin N, (if k < l then h3a_h (z l - z k) else 0) :=
    Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hterm k l
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have e : (1 / (N : ℝ)) * (N * (N * (-Real.log 2))) = -((N : ℝ) * Real.log 2) := by
    field_simp
  calc -((N : ℝ) * Real.log 2) = (1 / (N : ℝ)) * (N * (N * (-Real.log 2))) := e.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)

lemma h3a_gam_continuousOn : ContinuousOn (h3a_gam (N := N)) (cep_Alcove N) := by
  unfold h3a_gam
  refine (continuousOn_const (c := (1 / (N : ℝ)))).smul ?_
  refine continuousOn_finset_sum _ fun k _ => continuousOn_finset_sum _ fun l _ => ?_
  by_cases hkl : k < l
  · simp only [hkl, ite_true]
    have hc0 : ContinuousOn (fun _ : Ch N => (EuclideanSpace.single l (1 : ℝ) -
      EuclideanSpace.single k (1 : ℝ) : Ch N)) (cep_Alcove N) := continuousOn_const
    have hc1 : ContinuousOn (fun z : Ch N => h3a_dh (z l - z k)) (cep_Alcove N) := by
      intro z hz
      have hc : ContinuousAt h3a_dh (z l - z k) := h3a_dh_continuousAt (h3a_pair_mem hz hkl)
      have hlin : Continuous fun w : Ch N => w l - w k := by fun_prop
      exact (ContinuousAt.comp (g := h3a_dh) (f := fun w : Ch N => w l - w k) hc hlin.continuousAt).continuousWithinAt
    exact hc1.smul hc0
  · simp only [hkl, ite_false]
    exact continuousOn_const

end HRS.MC.CepH3
