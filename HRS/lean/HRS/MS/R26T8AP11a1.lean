import HRS.MS.R26T8AMix

/-!
# S8.2 T8A packet P11 (helper a1): nested Leibniz rule for coefficients depending on both variables
`‖nest p q (B (c Yw) (G Yw))‖ ≤ ‖B‖ 2^(p+q) ∑_{i≤p} ∑_{j≤q} ‖nest i j c‖ ‖nest (p-i) (q-j) G‖` (generalises `r26t8a_nest_bilinear`,
whose coefficient depends on `w` only).
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A

section Mix2

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem r26t8a_nest_bilinear2 : ∀ (q p : ℕ) {F1 F2 F3 : Type} [NormedAddCommGroup F1] [NormedSpace ℝ F1]
    [NormedAddCommGroup F2] [NormedSpace ℝ F2] [NormedAddCommGroup F3] [NormedSpace ℝ F3]
    (B : F1 →L[ℝ] F2 →L[ℝ] F3) (c : E × E → F1) (G : E × E → F2) (X z : E),
    ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) c → ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) G →
    ‖r26t8a_nest p q (fun Yw => B (c Yw) (G Yw)) X z‖ ≤
      ‖B‖ * 2 ^ (p + q) * ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
        ‖r26t8a_nest i j c X z‖ * ‖r26t8a_nest (p - i) (q - j) G X z‖ := by
  intro q
  induction q with
  | zero =>
    intro p F1 F2 F3 _ _ _ _ _ _ B c G X z hc hG
    rw [r26t8a_nest_zero]
    have hcz : ContDiff ℝ (p : WithTop ℕ∞) (fun Y => c (Y, z)) :=
      (by simpa using hc : ContDiff ℝ (p : WithTop ℕ∞) c).comp (contDiff_id.prodMk contDiff_const)
    have hGz : ContDiff ℝ (p : WithTop ℕ∞) (fun Y => G (Y, z)) :=
      (by simpa using hG : ContDiff ℝ (p : WithTop ℕ∞) G).comp (contDiff_id.prodMk contDiff_const)
    have h := B.norm_iteratedFDeriv_le_of_bilinear hcz hGz (x := X) (n := p) (le_refl _)
    refine h.trans ?_
    simp only [zero_add, Finset.sum_range_one, Nat.sub_zero, pow_zero, mul_one]
    have e : ∀ i ∈ Finset.range (p + 1), (p.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun Y => c (Y, z)) X‖ *
        ‖iteratedFDeriv ℝ (p - i) (fun Y => G (Y, z)) X‖ ≤
        2 ^ p * (‖r26t8a_nest i 0 c X z‖ * ‖r26t8a_nest (p - i) 0 G X z‖) := by
      intro i hi
      rw [r26t8a_nest_zero, r26t8a_nest_zero]
      have : (p.choose i : ℝ) ≤ 2 ^ p := by exact_mod_cast Nat.choose_le_two_pow p i
      calc _ ≤ 2 ^ p * ‖iteratedFDeriv ℝ i (fun Y => c (Y, z)) X‖ * ‖iteratedFDeriv ℝ (p - i) (fun Y => G (Y, z)) X‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this (norm_nonneg _)) (norm_nonneg _)
        _ = _ := by ring
    calc ‖B‖ * ∑ i ∈ Finset.range (p + 1), (p.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun Y => c (Y, z)) X‖ *
          ‖iteratedFDeriv ℝ (p - i) (fun Y => G (Y, z)) X‖
        ≤ ‖B‖ * ∑ i ∈ Finset.range (p + 1), 2 ^ p * (‖r26t8a_nest i 0 c X z‖ * ‖r26t8a_nest (p - i) 0 G X z‖) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum e) (norm_nonneg B)
      _ = _ := by rw [← Finset.mul_sum]; ring
  | succ q ih =>
    intro p F1 F2 F3 _ _ _ _ _ _ B c G X z hc hG
    rw [r26t8a_nest_succ]
    have hcd : Differentiable ℝ c := hc.differentiable (by simp)
    have hGd : Differentiable ℝ G := hG.differentiable (by simp)
    have hdw : r26t8a_dw (fun Yw => B (c Yw) (G Yw)) = fun Yw =>
        B.precompR E (c Yw) (r26t8a_dw G Yw) + B.precompL E (r26t8a_dw c Yw) (G Yw) := by
      funext Yw
      unfold r26t8a_dw
      exact B.fderiv_of_bilinear
        ((hcd.comp ((differentiable_const _).prodMk differentiable_id) : Differentiable ℝ fun w : E => c (Yw.1, w)).differentiableAt)
        ((hGd.comp ((differentiable_const _).prodMk differentiable_id) : Differentiable ℝ fun w : E => G (Yw.1, w)).differentiableAt)
    rw [hdw]
    have hc1 : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) c := hc.of_le (by exact_mod_cast Nat.le_succ (p + q))
    have hG1 : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) G := hG.of_le (by exact_mod_cast Nat.le_succ (p + q))
    have hcw : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (r26t8a_dw c) :=
      r26t8a_dw_contDiff (n := p + q) (by simpa [add_assoc] using hc)
    have hGw : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (r26t8a_dw G) :=
      r26t8a_dw_contDiff (n := p + q) (by simpa [add_assoc] using hG)
    have hT1 : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun Yw : E × E => B.precompR E (c Yw) (r26t8a_dw G Yw)) :=
      (B.precompR E).isBoundedBilinearMap.contDiff.comp (hc1.prodMk hGw)
    have hT2 : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun Yw : E × E => B.precompL E (r26t8a_dw c Yw) (G Yw)) :=
      (B.precompL E).isBoundedBilinearMap.contDiff.comp (hcw.prodMk hG1)
    have hadd : ‖r26t8a_nest p q (fun Yw => B.precompR E (c Yw) (r26t8a_dw G Yw) +
          B.precompL E (r26t8a_dw c Yw) (G Yw)) X z‖ ≤
        ‖r26t8a_nest p q (fun Yw => B.precompR E (c Yw) (r26t8a_dw G Yw)) X z‖ +
        ‖r26t8a_nest p q (fun Yw => B.precompL E (r26t8a_dw c Yw) (G Yw)) X z‖ := by
      refine le_trans (le_of_eq ?_) (norm_add_le _ _)
      congr 1
      exact r26t8a_nest_add p q z X hT1 hT2
    have I1 := ih p (B.precompR E) c (r26t8a_dw G) X z hc1 hGw
    have I2 := ih p (B.precompL E) (r26t8a_dw c) G X z hcw hG1
    set T : ℕ → ℕ → ℝ := fun i j => ‖r26t8a_nest i j c X z‖ * ‖r26t8a_nest (p - i) (q + 1 - j) G X z‖ with hT
    have hTn : ∀ i j, 0 ≤ T i j := fun i j => by positivity
    have hn1 : ∀ i j, ‖r26t8a_nest (p - i) (q - j) (r26t8a_dw G) X z‖ =
        ‖r26t8a_nest (p - i) (q - j + 1) G X z‖ := fun i j => (r26t8a_nest_succ _ _ _ _ _).symm
    -- first sum
    have S1 : ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
        ‖r26t8a_nest i j c X z‖ * ‖r26t8a_nest (p - i) (q - j) (r26t8a_dw G) X z‖ ≤
        ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 2), T i j := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Finset.sum_range_succ _ (q + 1)]
      refine le_trans (le_of_eq ?_) (le_add_of_nonneg_right (hTn i (q + 1)))
      refine Finset.sum_congr rfl fun j hj => ?_
      have : q - j + 1 = q + 1 - j := by have := Finset.mem_range.1 hj; omega
      rw [hn1, this]
    have S2 : ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
        ‖r26t8a_nest i j (r26t8a_dw c) X z‖ * ‖r26t8a_nest (p - i) (q - j) G X z‖ ≤
        ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 2), T i j := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Finset.sum_range_succ' _ (q + 1)]
      refine le_trans (le_of_eq ?_) (le_add_of_nonneg_right (hTn i 0))
      refine Finset.sum_congr rfl fun j hj => ?_
      have : q - j = q + 1 - (j + 1) := by omega
      simp only [hT]
      rw [← r26t8a_nest_succ i j c X z, this]
    have hB1 := B.norm_precompR_le E
    have hB2 := B.norm_precompL_le E
    have hP : (0 : ℝ) ≤ 2 ^ (p + q) := by positivity
    have J1 : ‖r26t8a_nest p q (fun Yw => B.precompR E (c Yw) (r26t8a_dw G Yw)) X z‖ ≤
        ‖B‖ * 2 ^ (p + q) * ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 2), T i j := by
      refine I1.trans ?_
      have : 0 ≤ 2 ^ (p + q) * ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
          ‖r26t8a_nest i j c X z‖ * ‖r26t8a_nest (p - i) (q - j) (r26t8a_dw G) X z‖ :=
        mul_nonneg hP (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
      calc _ ≤ ‖B‖ * 2 ^ (p + q) * ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
            ‖r26t8a_nest i j c X z‖ * ‖r26t8a_nest (p - i) (q - j) (r26t8a_dw G) X z‖ := by
            rw [mul_assoc]; rw [mul_assoc]
            exact mul_le_mul_of_nonneg_right hB1 this
        _ ≤ _ := mul_le_mul_of_nonneg_left S1 (by positivity)
    have J2 : ‖r26t8a_nest p q (fun Yw => B.precompL E (r26t8a_dw c Yw) (G Yw)) X z‖ ≤
        ‖B‖ * 2 ^ (p + q) * ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 2), T i j := by
      refine I2.trans ?_
      have : 0 ≤ 2 ^ (p + q) * ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
          ‖r26t8a_nest i j (r26t8a_dw c) X z‖ * ‖r26t8a_nest (p - i) (q - j) G X z‖ :=
        mul_nonneg hP (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
      calc _ ≤ ‖B‖ * 2 ^ (p + q) * ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1),
            ‖r26t8a_nest i j (r26t8a_dw c) X z‖ * ‖r26t8a_nest (p - i) (q - j) G X z‖ := by
            rw [mul_assoc]; rw [mul_assoc]
            exact mul_le_mul_of_nonneg_right hB2 this
        _ ≤ _ := mul_le_mul_of_nonneg_left S2 (by positivity)
    calc _ ≤ _ := hadd
      _ ≤ ‖B‖ * 2 ^ (p + q) * ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 2), T i j +
          ‖B‖ * 2 ^ (p + q) * ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 2), T i j := add_le_add J1 J2
      _ = ‖B‖ * 2 ^ (p + (q + 1)) * ∑ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (q + 1 + 1), T i j := by
          rw [show p + (q + 1) = (p + q) + 1 by ring, pow_succ]; ring

end Mix2

end HRS.MS.R26T8A
