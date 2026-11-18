import HRS.MS.R26T8AN1

/-!
# S8.2 local Newton layer, smooth part (N), step 2
`r26t8a_N2_conv_nest`: `‖nest p q (Y,w |-> ∫ K(u) S(Y,w-u) du) X z‖ <= B ∫_{ball ρ} |K|` for the (signed) Newton kernel `K`, `S` vanishing for `|w| > R0`,
`ρ > |z| + R0` and `B` bounding `nest i j S Y w` for `i <= p`, `j <= q`, `|Y-X| < 1`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric Convolution
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_N2_locInt {K : Euc d → ℝ} (hKi : ∀ r : ℝ, IntegrableOn K (ball (0 : Euc d) r)) :
    LocallyIntegrable K (volume : Measure (Euc d)) := by
  rw [locallyIntegrable_iff]
  intro C hC
  obtain ⟨r, hr⟩ := hC.isBounded.subset_ball (0 : Euc d)
  exact (hKi r).mono_set hr

theorem r26t8a_N2_conv_nest (hd : 2 ≤ d) (nu : ℝ) (p q : ℕ) {S : Euc d × Euc d → ℝ}
    (hS : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) S) (R0 : ℝ) (hSv : ∀ Y w : Euc d, R0 < ‖w‖ → S (Y, w) = 0)
    (B : ℝ) (X z : Euc d)
    (hB : ∀ i ≤ p, ∀ j ≤ q, ∀ Y : Euc d, ‖Y - X‖ < 1 → ∀ w : Euc d, ‖r26t8a_nest i j S Y w‖ ≤ B)
    (ρ : ℝ) (hρ : ‖z‖ + R0 < ρ) :
    ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => ∫ u, newtonKernel d nu u * S (Yw.1, Yw.2 - u)) X z‖ ≤
      B * ∫ u in ball (0 : Euc d) ρ, |newtonKernel d nu u| := by
  set K : Euc d → ℝ := newtonKernel d nu with hK
  set Kp : Euc d → ℝ := fun u => max (K u) 0 with hKp
  set Km : Euc d → ℝ := fun u => max (-K u) 0 with hKm
  have hKm0 : Measurable K := r26t8a_K_measurable nu
  have hKi : ∀ r : ℝ, IntegrableOn K (ball (0 : Euc d) r) := fun r => r26t8a_K_integrableOn hd nu r
  have hKpi : ∀ r : ℝ, IntegrableOn Kp (ball (0 : Euc d) r) := fun r => (hKi r).pos_part
  have hKmi : ∀ r : ℝ, IntegrableOn Km (ball (0 : Euc d) r) := fun r => (hKi r).neg_part
  have hKp0 : ∀ u, 0 ≤ Kp u := fun u => le_max_right _ _
  have hKm0' : ∀ u, 0 ≤ Km u := fun u => le_max_right _ _
  have hKpm : Measurable Kp := hKm0.max measurable_const
  have hKmm : Measurable Km := hKm0.neg.max measurable_const
  have hlp : LocallyIntegrable Kp (volume : Measure (Euc d)) := r26t8a_N2_locInt hKpi
  have hlm : LocallyIntegrable Km (volume : Measure (Euc d)) := r26t8a_N2_locInt hKmi
  have hSc : Continuous S := hS.continuous
  -- pointwise decomposition of the convolution
  have hdec : (fun Yw : Euc d × Euc d => ∫ u, K u * S (Yw.1, Yw.2 - u)) =
      fun Yw => (∫ u, Kp u * S (Yw.1, Yw.2 - u)) + (-(∫ u, Km u * S (Yw.1, Yw.2 - u))) := by
    funext Yw
    have hcs : HasCompactSupport (fun u : Euc d => S (Yw.1, Yw.2 - u)) := by
      refine HasCompactSupport.of_support_subset_isCompact (K := closedBall Yw.2 R0) (isCompact_closedBall _ _) ?_
      intro u hu
      by_contra hn
      rw [mem_closedBall, dist_eq_norm, not_le] at hn
      apply hu
      have : ‖Yw.2 - u‖ = ‖u - Yw.2‖ := norm_sub_rev _ _
      exact hSv _ _ (by linarith)
    have hcont : Continuous (fun u : Euc d => S (Yw.1, Yw.2 - u)) :=
      hSc.comp (continuous_const.prodMk (continuous_const.sub continuous_id))
    have i1 : Integrable (fun u => Kp u * S (Yw.1, Yw.2 - u)) :=
      hlp.integrable_smul_right_of_hasCompactSupport hcont hcs
    have i2 : Integrable (fun u => Km u * S (Yw.1, Yw.2 - u)) :=
      hlm.integrable_smul_right_of_hasCompactSupport hcont hcs
    have i2' : Integrable (fun u => -(Km u * S (Yw.1, Yw.2 - u))) := i2.neg
    rw [← integral_neg, ← integral_add i1 i2']
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hKp, hKm]
    have : K u = max (K u) 0 - max (-K u) 0 := (max_zero_sub_eq_self (K u)).symm
    rw [show K u * S (Yw.1, Yw.2 - u) = (max (K u) 0 - max (-K u) 0) * S (Yw.1, Yw.2 - u) by rw [← this]]
    ring
  have hCp := r26t8a_N1_conv_contDiff (n := p + q) (r26t8a_N2_locInt hKpi) hS R0 hSv
  have hCm := r26t8a_N1_conv_contDiff (n := p + q) (r26t8a_N2_locInt hKmi) hS R0 hSv
  have hCm' : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞)
      (fun Yw : Euc d × Euc d => -(∫ u, Km u * S (Yw.1, Yw.2 - u))) := hCm.neg
  rw [hdec, r26t8a_nest_add p q z X hCp hCm']
  have h1 := r26t8a_near_conv Kp hKp0 hKpm hKpi p q S hS R0 hSv B X z hB ρ hρ
  have h2 := r26t8a_near_conv Km hKm0' hKmm hKmi p q S hS R0 hSv B X z hB ρ hρ
  have hsum : ∫ u in ball (0 : Euc d) ρ, |K u| = (∫ u in ball (0 : Euc d) ρ, Kp u) + ∫ u in ball (0 : Euc d) ρ, Km u := by
    rw [← integral_add (hKpi ρ) (hKmi ρ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hKp, hKm]
    rcases le_total 0 (K u) with h | h
    · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith)]; ring
  rw [hsum, mul_add]
  refine (norm_add_le _ _).trans (add_le_add h1 ?_)
  rw [r26t8a_N1_nest_neg]
  exact h2

end HRS.MS.R26T8A
