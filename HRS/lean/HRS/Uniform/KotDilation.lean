import HRS.Prob.HilbertMartingale

/-!
# Lemma 3.17, dissipative alternative: an explicit (Sz.-Nagy type) dilation of a time-ordered product of
contractions (packet KOTELENEZ)

For contractions `C_0, …, C_{n-1}` on a Hilbert space `H` and the time-ordered products
`P(k,i) = C_{k-1} ⋯ C_i`, we construct isometries `B_j : H → 𝒦` and contractions `Q_k : 𝒦 → H`
(`𝒦 = H^{n+1}`, `ℓ²` sum) with `Q_k B_j = P(k,j)` for `j ≤ k ≤ n`.  Consequently
`∑_{j<k} P(k,j) Δ_j = Q_k ∑_{j<k} B_j Δ_j`: the discrete stochastic convolution is a contraction of a *martingale
transform* with deterministic operators (no random integrands are needed).
-/

noncomputable section

open scoped ENNReal NNReal

namespace HRS
namespace Uniform
namespace Kot

section Dilation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The defect operator `(1 - C C^*)^{1/2}`. -/
def defectOp (C : H →L[ℝ] H) : H →L[ℝ] H :=
  sqrtOp 1 (1 - C * ContinuousLinearMap.adjoint C)

theorem defectOp_spec (C : H →L[ℝ] H) (hC : ‖C‖ ≤ 1) :
    (∀ x y, inner ℝ (defectOp C x) y = inner ℝ x (defectOp C y)) ∧
      defectOp C * defectOp C = 1 - C * ContinuousLinearMap.adjoint C := by
  have hsym : ∀ x y, inner ℝ (((1 : H →L[ℝ] H) - C * ContinuousLinearMap.adjoint C) x) y =
      inner ℝ x (((1 : H →L[ℝ] H) - C * ContinuousLinearMap.adjoint C) y) := by
    intro x y
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.mul_apply, inner_sub_left, inner_sub_right]
    rw [← ContinuousLinearMap.adjoint_inner_right C, ← ContinuousLinearMap.adjoint_inner_left C]
  have hnorm : ∀ x, ‖(ContinuousLinearMap.adjoint C) x‖ ≤ ‖x‖ := by
    intro x
    have h1 : ‖(ContinuousLinearMap.adjoint C)‖ = ‖C‖ := by
      simp
    calc ‖(ContinuousLinearMap.adjoint C) x‖ ≤ ‖(ContinuousLinearMap.adjoint C)‖ * ‖x‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖x‖ := by rw [h1]; exact mul_le_mul_of_nonneg_right hC (norm_nonneg _)
      _ = ‖x‖ := one_mul _
  have hdiag : ∀ x, inner ℝ (((1 : H →L[ℝ] H) - C * ContinuousLinearMap.adjoint C) x) x =
      ‖x‖ ^ 2 - ‖(ContinuousLinearMap.adjoint C) x‖ ^ 2 := by
    intro x
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.mul_apply, inner_sub_left, real_inner_self_eq_norm_sq]
    rw [← ContinuousLinearMap.adjoint_inner_right C, real_inner_self_eq_norm_sq]
  have hpsd : HilbertCLTAux.IsPSDOp ((1 : H →L[ℝ] H) - C * ContinuousLinearMap.adjoint C) :=
    ⟨hsym, fun x => by
      rw [hdiag]
      nlinarith [hnorm x, norm_nonneg x, norm_nonneg ((ContinuousLinearMap.adjoint C) x)]⟩
  have hle : ∀ x, inner ℝ (((1 : H →L[ℝ] H) - C * ContinuousLinearMap.adjoint C) x) x ≤
      1 * ‖x‖ ^ 2 := by
    intro x
    rw [hdiag, one_mul]
    nlinarith [sq_nonneg ‖(ContinuousLinearMap.adjoint C) x‖]
  obtain ⟨h1, h2⟩ := sqrtOp_spec hpsd one_pos hle
  exact ⟨h1.symm, h2⟩

theorem defectOp_adjoint (C : H →L[ℝ] H) (hC : ‖C‖ ≤ 1) :
    ContinuousLinearMap.adjoint (defectOp C) = defectOp C := by
  ext x
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm, (defectOp_spec C hC).1 x y]
  exact real_inner_comm _ _

theorem defectOp_star (C : H →L[ℝ] H) (hC : ‖C‖ ≤ 1) : star (defectOp C) = defectOp C :=
  defectOp_adjoint C hC

/-- `ℓ²` direct sum of `n + 1` copies of `H`. -/
abbrev DSpace (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] (n : ℕ) :=
  PiLp 2 (fun _ : Fin (n + 1) => H)

variable (C : ℕ → H →L[ℝ] H) (Pk : ℕ → ℕ → H →L[ℝ] H)

/-- Slot coefficients: slot `0 ↦ P(k,0)`, slot `i+1 ↦ P(k,i+1) R_i` for `i < k` (else `0`). -/
def slotOp (k : ℕ) : ℕ → (H →L[ℝ] H)
  | 0 => Pk k 0
  | i + 1 => if i < k then Pk k (i + 1) * defectOp (C i) else 0

/-- The contraction `Q_k : 𝒦 → H`. -/
def Qop (n k : ℕ) : DSpace H n →L[ℝ] H :=
  ∑ m : Fin (n + 1), (slotOp C Pk k m.val).comp (PiLp.proj 2 (fun _ : Fin (n + 1) => H) m)

/-- The isometry `B_j : H → 𝒦` (adjoint of `Q_j`). -/
def Bop (n j : ℕ) : H →L[ℝ] DSpace H n :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => H)).symm : _ →L[ℝ] _).comp
    (ContinuousLinearMap.pi fun m : Fin (n + 1) => star (slotOp C Pk j m.val))

theorem Bop_apply (n j : ℕ) (h : H) (m : Fin (n + 1)) :
    (Bop C Pk n j h) m = star (slotOp C Pk j m.val) h := rfl

theorem Qop_apply (n k : ℕ) (x : DSpace H n) :
    Qop C Pk n k x = ∑ m : Fin (n + 1), slotOp C Pk k m.val (x m) := by
  simp [Qop]

theorem Qop_Bop_eq_sum (n j k : ℕ) (h : H) :
    Qop C Pk n k (Bop C Pk n j h) =
      (∑ m : Fin (n + 1), slotOp C Pk k m.val * star (slotOp C Pk j m.val)) h := by
  rw [Qop_apply, ContinuousLinearMap.sum_apply]
  rfl

theorem slot_sum (n : ℕ) (hC : ∀ i, i < n → ‖C i‖ ≤ 1) (h1 : ∀ k, k ≤ n → Pk k k = 1)
    (h2 : ∀ i k, i < k → k ≤ n → Pk k i = Pk k (i + 1) * C i) {j k : ℕ} (hjk : j ≤ k) (hkn : k ≤ n) :
    ∑ m : Fin (n + 1), slotOp C Pk k m.val * star (slotOp C Pk j m.val) = Pk k j := by
  set a : ℕ → (H →L[ℝ] H) := fun i => Pk k i * star (Pk j i) with ha
  have hterm : ∀ i, i < j → slotOp C Pk k (i + 1) * star (slotOp C Pk j (i + 1)) = a (i + 1) - a i := by
    intro i hij
    have hik : i < k := lt_of_lt_of_le hij hjk
    have hjn : j ≤ n := hjk.trans hkn
    have e1 : slotOp C Pk k (i + 1) = Pk k (i + 1) * defectOp (C i) := by simp [slotOp, hik]
    have e2 : slotOp C Pk j (i + 1) = Pk j (i + 1) * defectOp (C i) := by simp [slotOp, hij]
    have hCi : ‖C i‖ ≤ 1 := hC i (lt_of_lt_of_le hij hjn)
    have hR : star (defectOp (C i)) = defectOp (C i) := defectOp_star _ hCi
    have hRR := (defectOp_spec (C i) hCi).2
    have hk' := h2 i k hik hkn
    have hj' := h2 i j hij hjn
    rw [e1, e2, star_mul, hR]
    simp only [ha]
    rw [hk', hj', star_mul]
    calc Pk k (i + 1) * defectOp (C i) * (defectOp (C i) * star (Pk j (i + 1)))
        = Pk k (i + 1) * (defectOp (C i) * defectOp (C i)) * star (Pk j (i + 1)) := by
          simp only [mul_assoc]
      _ = Pk k (i + 1) * (1 - C i * star (C i)) * star (Pk j (i + 1)) := by
          rw [hRR]; rfl
      _ = _ := by
          simp only [mul_sub, sub_mul, mul_one, mul_assoc]
  have hzero : ∀ i, j ≤ i → slotOp C Pk j (i + 1) = 0 := by
    intro i hi
    simp [slotOp, not_lt.2 hi]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ]
  rw [Fin.sum_univ_eq_sum_range (fun i => slotOp C Pk k (i + 1) * star (slotOp C Pk j (i + 1))) n]
  show Pk k 0 * star (Pk j 0) + _ = _
  have hsum : ∑ i ∈ Finset.range n, slotOp C Pk k (i + 1) * star (slotOp C Pk j (i + 1)) =
      ∑ i ∈ Finset.range j, (a (i + 1) - a i) := by
    have hjn : j ≤ n := hjk.trans hkn
    rw [← Finset.sum_range_add_sum_Ico _ hjn]
    have hz : ∑ i ∈ Finset.Ico j n, slotOp C Pk k (i + 1) * star (slotOp C Pk j (i + 1)) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [hzero i (Finset.mem_Ico.1 hi).1]
      simp
    rw [hz, add_zero]
    exact Finset.sum_congr rfl fun i hi => hterm i (Finset.mem_range.1 hi)
  rw [hsum, Finset.sum_range_sub a j]
  have haj : a j = Pk k j := by simp [ha, h1 j (hjk.trans hkn)]
  rw [haj]
  simp only [ha]
  abel

theorem exists_dilation_aux (n : ℕ) (hC : ∀ i, i < n → ‖C i‖ ≤ 1) (h1 : ∀ k, k ≤ n → Pk k k = 1)
    (h2 : ∀ i k, i < k → k ≤ n → Pk k i = Pk k (i + 1) * C i) :
    (∀ j k, j ≤ k → k ≤ n → ∀ h, Qop C Pk n k (Bop C Pk n j h) = Pk k j h) ∧
      (∀ j, j ≤ n → ∀ h, ‖Bop C Pk n j h‖ = ‖h‖) ∧
      (∀ k, k ≤ n → ∀ x, ‖Qop C Pk n k x‖ ≤ ‖x‖) := by
  have hQB : ∀ j k, j ≤ k → k ≤ n → ∀ h, Qop C Pk n k (Bop C Pk n j h) = Pk k j h := by
    intro j k hjk hkn h
    rw [Qop_Bop_eq_sum, slot_sum C Pk n hC h1 h2 hjk hkn]
  have hiso : ∀ j, j ≤ n → ∀ h, ‖Bop C Pk n j h‖ = ‖h‖ := by
    intro j hj h
    have e1 : inner ℝ h (Qop C Pk n j (Bop C Pk n j h)) = ‖h‖ ^ 2 := by
      rw [hQB j j le_rfl hj, h1 j hj, ContinuousLinearMap.one_apply, real_inner_self_eq_norm_sq]
    have e2 : inner ℝ h (Qop C Pk n j (Bop C Pk n j h)) = ‖Bop C Pk n j h‖ ^ 2 := by
      have key : ∀ S : H →L[ℝ] H, inner ℝ h (S (star S h)) = ‖star S h‖ ^ 2 := by
        intro S
        rw [ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.adjoint_inner_left,
          real_inner_self_eq_norm_sq]
      rw [Qop_apply, inner_sum, PiLp.norm_sq_eq_of_L2]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Bop_apply, key]
    have h3 : ‖Bop C Pk n j h‖ ^ 2 = ‖h‖ ^ 2 := by rw [← e1, e2]
    exact le_antisymm (le_of_sq_le_sq (by rw [h3]) (norm_nonneg _))
      (le_of_sq_le_sq (by rw [h3]) (norm_nonneg _))
  refine ⟨hQB, hiso, fun k hk x => ?_⟩
  have hadj : ∀ h : H, inner ℝ (Bop C Pk n k h) x = inner ℝ h (Qop C Pk n k x) := by
    intro h
    rw [Qop_apply, inner_sum, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Bop_apply, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
  have h1' : ‖Qop C Pk n k x‖ ^ 2 ≤ ‖Qop C Pk n k x‖ * ‖x‖ := by
    calc ‖Qop C Pk n k x‖ ^ 2 = inner ℝ (Qop C Pk n k x) (Qop C Pk n k x) :=
          (real_inner_self_eq_norm_sq _).symm
      _ = inner ℝ (Bop C Pk n k (Qop C Pk n k x)) x := (hadj _).symm
      _ ≤ ‖Bop C Pk n k (Qop C Pk n k x)‖ * ‖x‖ := real_inner_le_norm _ _
      _ = ‖Qop C Pk n k x‖ * ‖x‖ := by rw [hiso k hk]
  by_contra hlt
  push_neg at hlt
  nlinarith [norm_nonneg x, norm_nonneg (Qop C Pk n k x)]

end Dilation

end Kot
end Uniform
end HRS
