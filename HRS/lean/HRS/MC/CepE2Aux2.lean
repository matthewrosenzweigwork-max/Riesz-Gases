import HRS.MC.CepE2Aux1

/-!
# Packet CEPE2, auxiliary 2: the potential `Φ` on the alcove (convexity, lower bound, barrier)
-/

open Set
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE2

open HRS.MC.CepE1

/-- Copy of `HRS.MC.Cepa.cep_Alcove`. -/
def cep_Alcove (N : ℕ) : Set (Ch N) :=
  {z | (∀ k l : Fin N, k < l → z k < z l) ∧ ∀ k l : Fin N, z l < z k + 1}

variable {N : ℕ}

theorem cepe2_mem_alcove_iff {z : Ch N} :
    z ∈ cep_Alcove N ↔ ∀ k l : Fin N, k < l → z l - z k ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · rintro ⟨h1, h2⟩ k l hkl
    exact ⟨by linarith [h1 k l hkl], by linarith [h2 k l]⟩
  · intro h
    refine ⟨fun k l hkl => by linarith [(h k l hkl).1], fun k l => ?_⟩
    rcases lt_trichotomy l k with hlk | rfl | hkl
    · linarith [(h l k hlk).1]
    · linarith
    · linarith [(h k l hkl).2]

theorem cepe2_isOpen_alcove : IsOpen (cep_Alcove N) := by
  have : cep_Alcove N = {z : Ch N | ∀ k l : Fin N, k < l → z l - z k ∈ Ioo (0 : ℝ) 1} := by
    ext z; exact cepe2_mem_alcove_iff
  rw [this]
  simp only [setOf_forall]
  refine isOpen_iInter_of_finite fun k => isOpen_iInter_of_finite fun l =>
    isOpen_iInter_of_finite fun _ => ?_
  exact isOpen_Ioo.preimage (((EuclideanSpace.proj l : Ch N →L[ℝ] ℝ).continuous).sub
      ((EuclideanSpace.proj k : Ch N →L[ℝ] ℝ).continuous))

/-- The number of pairs. -/
def cepe2_npairs (N : ℕ) : ℝ := ∑ k : Fin N, ∑ l : Fin N, if k < l then (1 : ℝ) else 0

theorem cepe2_npairs_nonneg : 0 ≤ cepe2_npairs N :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num

theorem cepe2_Phi_eq (a : ℝ) (z : Ch N) :
    cep_chamberPot a N z = (a / N) * ∑ k : Fin N, ∑ l : Fin N, if k < l then cepe2_f (z l - z k) else 0 :=
  rfl

theorem cepe2_h1_eq (a : ℝ) (u : ℝ) : cepe1_h1 a N u = (a / N) * cepe2_f' u := rfl

theorem cepe2_inner_pairGrad (a : ℝ) (x w : Ch N) :
    inner ℝ (cepe1_pairGrad (cepe1_h1 a N) x) w =
      (a / N) * ∑ k : Fin N, ∑ l : Fin N, if k < l then cepe2_f' (x l - x k) * (w l - w k) else 0 := by
  unfold cepe1_pairGrad
  rw [sum_inner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sum_inner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hkl : k < l
  · simp only [hkl, ite_true, real_inner_smul_left, cepe1_inner_vec, cepe2_h1_eq]
    ring
  · simp [hkl]

/-- Gradient inequality for `Φ` on the alcove. -/
theorem cepe2_convex {a : ℝ} (ha : 0 ≤ a) {x x' : Ch N} (hx : x ∈ cep_Alcove N) (hx' : x' ∈ cep_Alcove N) :
    cep_chamberPot a N x' + inner ℝ (cepe1_pairGrad (cepe1_h1 a N) x') (x - x') ≤ cep_chamberPot a N x := by
  rw [cepe2_inner_pairGrad, cepe2_Phi_eq, cepe2_Phi_eq, ← mul_add]
  have hc : 0 ≤ a / N := div_nonneg ha (Nat.cast_nonneg _)
  refine mul_le_mul_of_nonneg_left ?_ hc
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun l _ => ?_
  by_cases hkl : k < l
  · simp only [hkl, ite_true]
    have := cepe2_tangent (u := x l - x k) (v := x' l - x' k)
      (cepe2_mem_alcove_iff.1 hx k l hkl) (cepe2_mem_alcove_iff.1 hx' k l hkl)
    simp only [PiLp.sub_apply]
    linarith
  · simp [hkl]

/-- Monotonicity of `∇Φ` on the alcove. -/
theorem cepe2_monotone {a : ℝ} (ha : 0 ≤ a) {x x' : Ch N} (hx : x ∈ cep_Alcove N) (hx' : x' ∈ cep_Alcove N) :
    0 ≤ inner ℝ (cepe1_pairGrad (cepe1_h1 a N) x - cepe1_pairGrad (cepe1_h1 a N) x') (x - x') := by
  have h1 := cepe2_convex ha hx hx'
  have h2 := cepe2_convex ha hx' hx
  rw [inner_sub_left]
  have : inner ℝ (cepe1_pairGrad (cepe1_h1 a N) x) (x' - x) =
      -inner ℝ (cepe1_pairGrad (cepe1_h1 a N) x) (x - x') := by
    rw [← inner_neg_right, neg_sub]
  linarith

theorem cepe2_gradient_eq {a : ℝ} {x : Ch N} (hx : x ∈ cep_Alcove N) :
    gradient (cep_chamberPot a N) x = cepe1_pairGrad (cepe1_h1 a N) x :=
  (cepe1_Phi_hasGradient fun k l hkl => cepe2_mem_alcove_iff.1 hx k l hkl).gradient

theorem cepe2_hasGradient {a : ℝ} {x : Ch N} (hx : x ∈ cep_Alcove N) :
    HasGradientAt (cep_chamberPot a N) (cepe1_pairGrad (cepe1_h1 a N) x) x :=
  cepe1_Phi_hasGradient fun k l hkl => cepe2_mem_alcove_iff.1 hx k l hkl

/-- Lower bound for `Φ`. -/
theorem cepe2_lower {a : ℝ} (ha : 0 ≤ a) {x : Ch N} (hx : x ∈ cep_Alcove N) :
    -((a / N) * cepe2_npairs N * Real.log 2) ≤ cep_chamberPot a N x := by
  rw [cepe2_Phi_eq]
  have hc : 0 ≤ a / N := div_nonneg ha (Nat.cast_nonneg _)
  have : -(cepe2_npairs N * Real.log 2) ≤
      ∑ k : Fin N, ∑ l : Fin N, if k < l then cepe2_f (x l - x k) else 0 := by
    have e : -(cepe2_npairs N * Real.log 2) = ∑ k : Fin N, ∑ l : Fin N, if k < l then -Real.log 2 else 0 := by
      unfold cepe2_npairs
      rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      split_ifs <;> simp
    rw [e]
    refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => ?_
    by_cases hkl : k < l
    · simp only [hkl, ite_true]
      exact cepe2_f_ge (cepe2_mem_alcove_iff.1 hx k l hkl)
    · simp [hkl]
  nlinarith

/-- Barrier: a bound on `Φ` bounds each gap term of `f`. -/
theorem cepe2_gap_bound {a : ℝ} (ha : 0 < a) {x : Ch N} (hx : x ∈ cep_Alcove N) {k l : Fin N} (hkl : k < l) :
    cepe2_f (x l - x k) ≤ cep_chamberPot a N x / (a / N) + cepe2_npairs N * Real.log 2 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (by rintro rfl; exact k.elim0)
  have hc : 0 < a / N := div_pos ha hN
  rw [cepe2_Phi_eq, mul_div_cancel_left₀ _ hc.ne']
  set t : Fin N → Fin N → ℝ := fun k l => if k < l then cepe2_f (x l - x k) + Real.log 2 else 0 with ht
  have ht0 : ∀ k l, 0 ≤ t k l := by
    intro k l
    by_cases h : k < l
    · simp only [ht, h, ite_true]
      linarith [cepe2_f_ge (cepe2_mem_alcove_iff.1 hx k l h)]
    · simp [ht, h]
  have h1 : t k l ≤ ∑ l', t k l' :=
    Finset.single_le_sum (f := fun l' => t k l') (fun l' _ => ht0 k l') (Finset.mem_univ l)
  have h2 : ∑ l', t k l' ≤ ∑ k', ∑ l', t k' l' :=
    Finset.single_le_sum (f := fun k' => ∑ l', t k' l') (fun k' _ => Finset.sum_nonneg fun l' _ => ht0 k' l')
      (Finset.mem_univ k)
  have h3 : ∑ k', ∑ l', t k' l' =
      (∑ k' : Fin N, ∑ l' : Fin N, if k' < l' then cepe2_f (x l' - x k') else 0) + cepe2_npairs N * Real.log 2 := by
    unfold cepe2_npairs
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l' _ => ?_
    by_cases h : k' < l'
    · simp [ht, h]
    · simp [ht, h]
  have h4 : t k l = cepe2_f (x l - x k) + Real.log 2 := by simp [ht, hkl]
  have h5 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  linarith

end HRS.MC.CepE2
