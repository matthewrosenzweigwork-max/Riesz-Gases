import HRS.MS.MfeConfAux92

/-!
# S.B.1, packet F8 (part 25): quadratic growth of `ψ` at one density, and boundedness of continuous functions of the clamped time
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d : ℕ}

theorem sb1_lv_bdd_of_cont {T : ℝ} (hT : 0 ≤ T) {f : ℝ → ℝ} (hf : Continuous f)
    (hc : ∀ s, f s = f (sb1_lv_cl' hT s)) : ∃ M : ℝ, 0 ≤ M ∧ ∀ s, |f s| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨|M|, abs_nonneg _, fun s => ?_⟩
  rw [hc s]
  have := hM _ (sb1_lv_cl'_mem hT s)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_abs_self M)

theorem sb1_lv_opNorm_le_sum (L : Euc d →L[ℝ] ℝ) : ‖L‖ ≤ ∑ j, |L (sb1e j)| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun j _ => abs_nonneg _) fun v => ?_
  rw [sb1_clm_expand L v, Real.norm_eq_abs, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  have : |v j| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v j
  nlinarith [abs_nonneg (L (sb1e j))]

section Dens

variable {D : Whole.WholeDyn d} {s r₀ : ℝ} {k : Euc d → ℝ} {h : Euc d → ℝ} {Cρ M1 Lg L2 C B : ℝ}

theorem sb1_lv_psi_growth (hθ : 0 < D.invβ) (P : Sb1Pot D.V B) (hk : Sb1KerU d D.s k) (hd : 1 ≤ d)
    (hs0 : 0 ≤ D.s) (hsd : D.s < d) (R : Sb1Rho h Cρ M1) (S : Sb1Slice d C h)
    (hpos : ∀ y, 0 < h y) {Kv V0 Λ0 : ℝ} (hKv : 0 ≤ Kv)
    (hv : ∀ x y, ‖Whole.mfeTransportW D h x - Whole.mfeTransportW D h y‖ ≤ Kv * ‖x - y‖)
    (hV0 : ‖Whole.mfeTransportW D h 0‖ ≤ V0) (hΛ0 : |Real.log (h 0)| ≤ Λ0) (x : Euc d) :
    |sb1_lv_psi D k h x| ≤ (D.invβ * Λ0 + sb1CG d D.s Cρ M1 + |D.V 0| + (d * (V0 + sb1BF d D.s C + ‖fderiv ℝ D.V 0‖) + 1 +
      ‖fderiv ℝ D.V 0‖ + d * (Kv + B) + B)) * (1 + ‖x‖ ^ 2) := by
  have hθ0 := hθ.le
  have hBF : 0 ≤ sb1BF d D.s C := sb1BF_nonneg hs0 S.C_nonneg
  have hB : 0 ≤ B := P.B_nonneg
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hV00 : 0 ≤ V0 := (norm_nonneg _).trans hV0
  have hhd : Differentiable ℝ h := S.decay.1.differentiable (by norm_num)
  have hVd : Differentiable ℝ D.V := P.c3.differentiable (by norm_num)
  set G0 := ‖fderiv ℝ D.V 0‖ with hG0
  set BF := sb1BF d D.s C with hBFd
  have hvn : ∀ y, ‖Whole.mfeTransportW D h y‖ ≤ V0 + Kv * ‖y‖ := by
    intro y
    have h2 := hv y 0
    rw [sub_zero] at h2
    have := norm_le_insert' (Whole.mfeTransportW D h y) (Whole.mfeTransportW D h 0)
    linarith
  -- increments of θ log h
  have hlogdiff : ∀ y, DifferentiableAt ℝ (fun y => D.invβ * Real.log (h y)) y := fun y =>
    (((hhd y).log (hpos y).ne').const_mul _)
  have hlogd : ∀ y, HasFDerivAt (fun y => D.invβ * Real.log (h y)) (D.invβ • (h y)⁻¹ • fderiv ℝ h y) y := fun y =>
    ((hhd y).hasFDerivAt.log (hpos y).ne').const_mul D.invβ |>.congr_fderiv (by ext v; simp)
  have hcomp : ∀ y j, |(D.invβ • (h y)⁻¹ • fderiv ℝ h y) (sb1e j)| ≤ (V0 + BF + G0) + (Kv + B) * ‖y‖ := by
    intro y j
    have e := sb1_lv_v_apply hd hs0 hsd S hpos y j
    have e2 : (D.invβ • (h y)⁻¹ • fderiv ℝ h y) (sb1e j) = Whole.mfeTransportW D h y j - sb1F d D.s h j y -
        fderiv ℝ D.V y (sb1e j) := by
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [e]; field_simp; ring
    rw [e2]
    have a1 : |Whole.mfeTransportW D h y j| ≤ V0 + Kv * ‖y‖ := by
      have h3 : |Whole.mfeTransportW D h y j| ≤ ‖Whole.mfeTransportW D h y‖ := by
        simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (Whole.mfeTransportW D h y) j
      exact h3.trans (hvn y)
    have a2 := sb1_lv_F_bound hd hs0 hsd S j y
    have a3 : |fderiv ℝ D.V y (sb1e j)| ≤ G0 + B * ‖y‖ := sb1_lv_dV_bound P j y
    calc _ ≤ |Whole.mfeTransportW D h y j - sb1F d D.s h j y| + |fderiv ℝ D.V y (sb1e j)| := abs_sub _ _
      _ ≤ (|Whole.mfeTransportW D h y j| + |sb1F d D.s h j y|) + |fderiv ℝ D.V y (sb1e j)| := by
          have := abs_sub (Whole.mfeTransportW D h y j) (sb1F d D.s h j y); linarith
      _ ≤ _ := by nlinarith
  have hMVT : D.invβ * |Real.log (h x) - Real.log (h 0)| ≤ ‖x‖ * (d * ((V0 + BF + G0) + (Kv + B) * ‖x‖)) := by
    have hb : ∀ y ∈ Metric.closedBall (0 : Euc d) ‖x‖, ‖fderiv ℝ (fun y => D.invβ * Real.log (h y)) y‖ ≤
        d * ((V0 + BF + G0) + (Kv + B) * ‖x‖) := by
      intro y hy
      rw [(hlogd y).fderiv]
      refine (sb1_lv_opNorm_le_sum _).trans ?_
      calc _ ≤ ∑ j : Fin d, ((V0 + BF + G0) + (Kv + B) * ‖x‖) := by
            refine Finset.sum_le_sum fun j _ => (hcomp y j).trans ?_
            have : ‖y‖ ≤ ‖x‖ := by simpa using hy
            nlinarith [add_nonneg hKv hB]
        _ = _ := by simp; ring
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := fun y => D.invβ * Real.log (h y))
      (s := Metric.closedBall (0 : Euc d) ‖x‖) (x := (0 : Euc d)) (y := x) (C := d * ((V0 + BF + G0) + (Kv + B) * ‖x‖))
      (fun y _ => hlogdiff y) hb (convex_closedBall _ _) (Metric.mem_closedBall_self (norm_nonneg x)) (by simp [Metric.mem_closedBall])
    rw [sub_zero, ← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_pos hθ] at this
    rw [mul_comm ‖x‖]
    exact this
  -- G and V
  have hG := sb1_G_abs_le hd hs0 hsd hk R x
  have hlogx := sb1_log_le_norm x
  have hVx : |D.V x - D.V 0| ≤ (G0 + B * ‖x‖) * ‖x‖ := by
    have hb : ∀ y ∈ Metric.closedBall (0 : Euc d) ‖x‖, ‖fderiv ℝ D.V y‖ ≤ G0 + B * ‖x‖ := by
      intro y hy
      have : ‖y‖ ≤ ‖x‖ := by simpa using hy
      refine (sb1_gradV_bound P y).trans ?_
      nlinarith
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := D.V) (s := Metric.closedBall (0 : Euc d) ‖x‖) (x := (0 : Euc d)) (y := x)
      (C := G0 + B * ‖x‖) (fun y _ => hVd y) hb (convex_closedBall _ _) (Metric.mem_closedBall_self (norm_nonneg x)) (by simp [Metric.mem_closedBall])
    rw [sub_zero, Real.norm_eq_abs] at this
    exact this
  have hx := norm_nonneg x
  unfold sb1_lv_psi
  have h1 : |-(D.invβ * Real.log (h x) + sb1G k h x + D.V x)| ≤ D.invβ * |Real.log (h x)| + |sb1G k h x| + |D.V x| := by
    rw [abs_neg]
    refine (abs_add_three _ _ _).trans ?_
    rw [abs_mul, abs_of_pos hθ]
  have h2 : |Real.log (h x)| ≤ |Real.log (h 0)| + |Real.log (h x) - Real.log (h 0)| := by
    have := abs_add_le (Real.log (h 0)) (Real.log (h x) - Real.log (h 0))
    simpa using this
  have h3 : |D.V x| ≤ |D.V 0| + |D.V x - D.V 0| := by
    have := abs_add_le (D.V 0) (D.V x - D.V 0)
    simpa using this
  have key : D.invβ * |Real.log (h x)| + |sb1G k h x| + |D.V x| ≤ (D.invβ * Λ0 + sb1CG d D.s Cρ M1 + |D.V 0|) +
      (d * (V0 + BF + G0) + 1 + G0) * ‖x‖ + (d * (Kv + B) + B) * ‖x‖ ^ 2 := by
    have a := mul_le_mul_of_nonneg_left h2 hθ0
    have b : D.invβ * |Real.log (h 0)| ≤ D.invβ * Λ0 := mul_le_mul_of_nonneg_left hΛ0 hθ0
    nlinarith
  refine h1.trans (key.trans ?_)
  have hx1 : ‖x‖ ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - 1)]
  have hx2 : (1 : ℝ) ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖]
  have hx3 : ‖x‖ ^ 2 ≤ 1 + ‖x‖ ^ 2 := by nlinarith
  have c0 : 0 ≤ D.invβ * Λ0 + sb1CG d D.s Cρ M1 + |D.V 0| := by
    have : 0 ≤ Λ0 := (abs_nonneg _).trans hΛ0
    have := sb1CG_nonneg (d := d) (s := D.s) R
    positivity
  have c1 : 0 ≤ d * (V0 + BF + G0) + 1 + G0 := by positivity
  have c2 : 0 ≤ d * (Kv + B) + B := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hx1 c1, mul_le_mul_of_nonneg_left hx3 c2, mul_le_mul_of_nonneg_left hx2 c0]

end Dens

end HRS.MS.MfeConf
