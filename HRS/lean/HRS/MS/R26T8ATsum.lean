import HRS.MS.R26T8APot3

/-!
# S8.2 nonlocal layer: nested jets of a series (P11e, part 3)
`r26t8a_nest_tsum`: if every `V n` is `C^(p+q)` and the nested jets `nest i j (V n) Y w` (`i <= p`, `j <= q`) are bounded by a summable
`Phi n` for `Y` near `X`, `w` near `z`, then `nest p q (sum_n V n) X z = sum_n nest p q (V n) X z`
(two applications of `r26t8a_iter_integral` for the counting measure on `ℕ`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff

namespace HRS.MS.R26T8A
open HRS

theorem r26t8a_count_integral {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (f : ℕ → W) (h : Summable fun n => ‖f n‖) :
    ∫ n, f n ∂(Measure.count : Measure ℕ) = ∑' n, f n := by
  have hi : Integrable f (Measure.count : Measure ℕ) := integrable_count_iff.2 h
  rw [integral_countable hi]
  congr 1 with n
  simp [Measure.real, Measure.count_singleton]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem r26t8a_nest_tsum {d : ℕ} (p q : ℕ) (V : ℕ → Euc d × Euc d → ℝ)
    (hV : ∀ n, ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (V n)) (X z : Euc d) {r : ℝ} (hr : 0 < r)
    (Φ : ℕ → ℝ) (hΦ0 : ∀ n, 0 ≤ Φ n) (hΦ : Summable Φ)
    (hB : ∀ n, ∀ i ≤ p, ∀ j ≤ q, ∀ Y : Euc d, ‖Y - X‖ < r → ∀ w : Euc d, ‖w - z‖ < r →
      ‖r26t8a_nest i j (V n) Y w‖ ≤ Φ n) :
    ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => ∑' n, V n Yw) X z‖ ≤
      ∑' n, ‖r26t8a_nest p q (V n) X z‖ := by
  have hΦint : Integrable Φ (Measure.count : Measure ℕ) :=
    integrable_count_iff.2 (by simpa [Real.norm_of_nonneg (hΦ0 _)] using hΦ)
  have hVq : ∀ (n : ℕ) (Y : Euc d), ContDiff ℝ (q : WithTop ℕ∞) (fun w => V n (Y, w)) := fun n Y =>
    ((hV n).of_le (by exact_mod_cast Nat.le_add_left q p)).comp
      (contDiff_const.prodMk contDiff_id : ContDiff ℝ (q : WithTop ℕ∞) fun w : Euc d => (Y, w))
  -- stage 1: derivatives in the relative variable
  have hstage1 : ∀ Y : Euc d, ‖Y - X‖ < r →
      iteratedFDeriv ℝ q (fun w => ∑' n, V n (Y, w)) z = ∑' n, iteratedFDeriv ℝ q (fun w => V n (Y, w)) z := by
    intro Y hY
    have hbd : ∀ i ≤ q, ∀ᵐ n ∂(Measure.count : Measure ℕ), ∀ x ∈ ball z r,
        ‖iteratedFDeriv ℝ i (fun w => V n (Y, w)) x‖ ≤ Φ n := by
      intro i hi
      refine Filter.Eventually.of_forall fun n x hx => ?_
      rw [r26t8a_nest_norm_zero]
      exact hB n 0 (Nat.zero_le _) i hi Y hY x (by simpa [dist_eq_norm] using hx)
    have key := r26t8a_iter_integral (E := Euc d) (μ := (Measure.count : Measure ℕ)) (U := ball z r)
      isOpen_ball (fun n w => V n (Y, w)) q
      (Filter.Eventually.of_forall fun n x _ => (hVq n Y).contDiffAt) hΦint hbd
      (fun i hi x hx => AEStronglyMeasurable.of_discrete) q le_rfl z (mem_ball_self hr)
    have hsumm : ∀ w ∈ ball z r, Summable fun n => ‖V n (Y, w)‖ := fun w hw =>
      Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => by
        have := hB n 0 (Nat.zero_le _) 0 (Nat.zero_le _) Y hY w (by simpa [dist_eq_norm] using hw)
        have e : ‖r26t8a_nest 0 0 (V n) Y w‖ = ‖V n (Y, w)‖ := by
          rw [r26t8a_nest_zero, norm_iteratedFDeriv_zero]
        rwa [e] at this) hΦ
    have hev : (fun y => ∫ n, V n (Y, y) ∂(Measure.count : Measure ℕ)) =ᶠ[𝓝 z] fun y => ∑' n, V n (Y, y) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with y hy
      exact r26t8a_count_integral _ (hsumm y hy)
    rw [← (hev.iteratedFDeriv ℝ q).self_of_nhds, key]
    exact r26t8a_count_integral _ (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => by
      have := hB n 0 (Nat.zero_le _) q le_rfl Y hY z (by simpa using hr)
      simpa [r26t8a_nest] using this) hΦ)
  -- stage 2: derivatives in the centre variable
  set J : ℕ → Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin q => Euc d) ℝ :=
    fun n Y => iteratedFDeriv ℝ q (fun w => V n (Y, w)) z with hJ
  have hJc : ∀ n, ContDiff ℝ (p : WithTop ℕ∞) (J n) := fun n => r26t8a_nest_contDiff q p (V n) z (hV n)
  have hbd2 : ∀ i ≤ p, ∀ᵐ n ∂(Measure.count : Measure ℕ), ∀ Y ∈ ball X r, ‖iteratedFDeriv ℝ i (J n) Y‖ ≤ Φ n := by
    intro i hi
    refine Filter.Eventually.of_forall fun n Y hY => ?_
    exact hB n i hi q le_rfl Y (by simpa [dist_eq_norm] using hY) z (by simpa using hr)
  have key2 : iteratedFDeriv ℝ p (fun Y => ∫ n, J n Y ∂(Measure.count : Measure ℕ)) X =
      ∫ n, iteratedFDeriv ℝ p (J n) X ∂(Measure.count : Measure ℕ) :=
    r26t8a_iter_integral (E := Euc d) (F := ContinuousMultilinearMap ℝ (fun _ : Fin q => Euc d) ℝ)
      (μ := (Measure.count : Measure ℕ)) (U := ball X r) isOpen_ball J p
      (Filter.Eventually.of_forall fun n Y _ => (hJc n).contDiffAt) hΦint hbd2
      (fun i hi Y hY => AEStronglyMeasurable.of_discrete) p le_rfl X (mem_ball_self hr)
  have hJsumm : ∀ Y ∈ ball X r, Summable fun n => ‖J n Y‖ := fun Y hY =>
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => by
      have := hB n 0 (Nat.zero_le _) q le_rfl Y (by simpa [dist_eq_norm] using hY) z (by simpa using hr)
      simpa [r26t8a_nest, hJ] using this) hΦ
  have hev2 : (fun Y => ∫ n, J n Y ∂(Measure.count : Measure ℕ)) =ᶠ[𝓝 X]
      fun Y => iteratedFDeriv ℝ q (fun w => ∑' n, V n (Y, w)) z := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with Y hY
    rw [hstage1 Y (by simpa [dist_eq_norm] using hY)]
    exact r26t8a_count_integral _ (hJsumm Y hY)
  have e1 : r26t8a_nest p q (fun Yw : Euc d × Euc d => ∑' n, V n Yw) X z =
      iteratedFDeriv ℝ p (fun Y => ∫ n, J n Y ∂(Measure.count : Measure ℕ)) X := by
    unfold r26t8a_nest
    exact ((hev2.iteratedFDeriv ℝ p).self_of_nhds).symm
  rw [e1, key2]
  have hbn : ∀ n, ‖r26t8a_nest p q (V n) X z‖ ≤ Φ n := fun n =>
    hB n p le_rfl q le_rfl X (by simpa using hr) z (by simpa using hr)
  have hsn : Summable fun n => ‖‖r26t8a_nest p q (V n) X z‖‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => by simpa using hbn n) hΦ
  have hint : Integrable (fun n => r26t8a_nest p q (V n) X z) (Measure.count : Measure ℕ) :=
    integrable_count_iff.2 (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbn hΦ)
  refine (norm_integral_le_integral_norm _).trans ?_
  exact (r26t8a_count_integral (fun n => ‖r26t8a_nest p q (V n) X z‖) hsn).le

end HRS.MS.R26T8A
