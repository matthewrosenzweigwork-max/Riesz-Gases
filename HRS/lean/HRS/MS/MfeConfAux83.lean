import HRS.MS.MfeConfAux82

/-!
# S.B.1, packet F8 (part 15): growth and Lipschitz bounds of `u` at one density
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d : ℕ}

theorem sb1_lv_norm_le_sum (w : Euc d) : ‖w‖ ≤ ∑ j, |w j| := by
  have h0 : 0 ≤ ∑ j, |w j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  refine le_of_sq_le_sq ?_ h0
  rw [EuclideanSpace.norm_sq_eq]
  have : ∑ j, ‖w j‖ ^ 2 ≤ (∑ j, |w j|) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    calc ∑ j, ‖w j‖ ^ 2 = ∑ j, |w j| * |w j| := Finset.sum_congr rfl fun j _ => by
          rw [Real.norm_eq_abs, sq]
      _ ≤ ∑ i, ∑ j, |w i| * |w j| := Finset.sum_le_sum fun i _ =>
          Finset.single_le_sum (f := fun j => |w i| * |w j|) (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
            (Finset.mem_univ i)
  exact this

section Dens

variable {D : Whole.WholeDyn d} {s r₀ : ℝ} {k : Euc d → ℝ} {h : Euc d → ℝ} {Cρ M1 Lg L2 C B : ℝ}

theorem sb1_lv_u_sub_v (hk4 : IsP4Kernel d D.s r₀ k) (hd : 1 ≤ d) (hs0 : 0 ≤ D.s) (hsd : D.s < d)
    (hR : Sb1KerR d k Lg) (P : Sb1Pot D.V B) (R : Sb1Rho h Cρ M1) (S : Sb1Slice d C h) (hpos : ∀ y, 0 < h y)
    (x : Euc d) (j : Fin d) :
    sb1_lv_u D k h x j - Whole.mfeTransportW D h x j = sb1_lv_a k h j x - sb1F d D.s h j x := by
  have hhd : Differentiable ℝ h := S.decay.1.differentiable (by norm_num)
  have hV : Differentiable ℝ D.V := P.c3.differentiable (by norm_num)
  rw [sb1_lv_u_apply hk4 hd hs0 hsd hR R hpos hhd hV, sb1_lv_v_apply hd hs0 hsd S hpos]
  ring

/-- the growth and Lipschitz bounds of `u` in terms of those of the exact transport `v = mfeTransportW` -/
theorem sb1_lv_u_bounds (hk4 : IsP4Kernel d D.s r₀ k) (hd : 1 ≤ d) (hs0 : 0 ≤ D.s) (hsd : D.s < d)
    (hR : Sb1KerR d k Lg) (hL : ∀ z, ‖fderiv ℝ k z‖ ≤ Lg) (hL2 : ∀ z, ‖fderiv ℝ (fderiv ℝ k) z‖ ≤ L2)
    (P : Sb1Pot D.V B) (R : Sb1Rho h Cρ M1) (S : Sb1Slice d C h) (hpos : ∀ y, 0 < h y) {Kv : ℝ}
    (hv : ∀ x y, ‖Whole.mfeTransportW D h x - Whole.mfeTransportW D h y‖ ≤ Kv * ‖x - y‖) :
    (∀ x, ‖sb1_lv_u D k h x‖ ≤ (‖Whole.mfeTransportW D h 0‖ + d * (Lg + sb1BF d D.s C)) + Kv * ‖x‖) ∧
    (∀ x y, ‖sb1_lv_u D k h x - sb1_lv_u D k h y‖ ≤ (Kv + d * (L2 + sb1BF d D.s C)) * ‖x - y‖) := by
  have he : ∀ x, ‖sb1_lv_u D k h x - Whole.mfeTransportW D h x‖ ≤ d * (Lg + sb1BF d D.s C) := by
    intro x
    refine (sb1_lv_norm_le_sum _).trans ?_
    calc ∑ j, |(sb1_lv_u D k h x - Whole.mfeTransportW D h x) j| ≤ ∑ j : Fin d, (Lg + sb1BF d D.s C) := by
          refine Finset.sum_le_sum fun j _ => ?_
          simp only [PiLp.sub_apply]
          rw [sb1_lv_u_sub_v hk4 hd hs0 hsd hR P R S hpos]
          exact (abs_sub _ _).trans (add_le_add (sb1_lv_a_bound hk4 hd hs0 hsd hR hL R j x)
            (sb1_lv_F_bound hd hs0 hsd S j x))
      _ = _ := by simp; ring
  have hel : ∀ x y, ‖(sb1_lv_u D k h x - Whole.mfeTransportW D h x) - (sb1_lv_u D k h y - Whole.mfeTransportW D h y)‖ ≤
      d * (L2 + sb1BF d D.s C) * ‖x - y‖ := by
    intro x y
    refine (sb1_lv_norm_le_sum _).trans ?_
    calc _ ≤ ∑ j : Fin d, (L2 + sb1BF d D.s C) * ‖x - y‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          simp only [PiLp.sub_apply]
          have e : sb1_lv_u D k h x j - Whole.mfeTransportW D h x j - (sb1_lv_u D k h y j - Whole.mfeTransportW D h y j) =
              (sb1_lv_a k h j x - sb1_lv_a k h j y) - (sb1F d D.s h j x - sb1F d D.s h j y) := by
            rw [sb1_lv_u_sub_v hk4 hd hs0 hsd hR P R S hpos, sb1_lv_u_sub_v hk4 hd hs0 hsd hR P R S hpos]; ring
          rw [e]
          calc _ ≤ |sb1_lv_a k h j x - sb1_lv_a k h j y| + |sb1F d D.s h j x - sb1F d D.s h j y| := abs_sub _ _
            _ ≤ L2 * ‖x - y‖ + sb1BF d D.s C * ‖x - y‖ :=
                add_le_add (sb1_lv_a_lip hk4 hd hs0 hsd hR hL hL2 R j x y) (sb1_lv_F_lip hd hs0 hsd S j x y)
            _ = _ := by ring
      _ = _ := by simp; ring
  constructor
  · intro x
    have h1 : ‖Whole.mfeTransportW D h x‖ ≤ ‖Whole.mfeTransportW D h 0‖ + Kv * ‖x‖ := by
      have := hv x 0
      rw [sub_zero] at this
      have := norm_le_insert' (Whole.mfeTransportW D h x) (Whole.mfeTransportW D h 0)
      linarith [hv x 0, sub_zero x]
    calc ‖sb1_lv_u D k h x‖ ≤ ‖Whole.mfeTransportW D h x‖ + ‖sb1_lv_u D k h x - Whole.mfeTransportW D h x‖ := by
          have := norm_add_le (Whole.mfeTransportW D h x) (sb1_lv_u D k h x - Whole.mfeTransportW D h x)
          simpa [add_comm] using this
      _ ≤ _ := by linarith [he x]
  · intro x y
    calc ‖sb1_lv_u D k h x - sb1_lv_u D k h y‖ ≤ ‖Whole.mfeTransportW D h x - Whole.mfeTransportW D h y‖ +
          ‖(sb1_lv_u D k h x - Whole.mfeTransportW D h x) - (sb1_lv_u D k h y - Whole.mfeTransportW D h y)‖ := by
          have := norm_add_le (Whole.mfeTransportW D h x - Whole.mfeTransportW D h y)
            ((sb1_lv_u D k h x - Whole.mfeTransportW D h x) - (sb1_lv_u D k h y - Whole.mfeTransportW D h y))
          have e : Whole.mfeTransportW D h x - Whole.mfeTransportW D h y +
              ((sb1_lv_u D k h x - Whole.mfeTransportW D h x) - (sb1_lv_u D k h y - Whole.mfeTransportW D h y)) =
              sb1_lv_u D k h x - sb1_lv_u D k h y := by abel
          rwa [e] at this
      _ ≤ _ := by linarith [hv x y, hel x y]

end Dens

end HRS.MS.MfeConf
