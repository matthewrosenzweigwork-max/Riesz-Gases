import HRS.MS.R26T8APot1
import HRS.MS.R26T8APot2
import HRS.Torus.Basic

/-!
# S8.2 nonlocal layer: mixed center/relative derivatives of a convolution with a locally integrable kernel
`r26t8a_near_conv`: for `V(Y,z) = int K(u) S(Y,z-u) du` with `S` of class `C^(p+q)` and compactly supported in `w`, the
mixed jet `nest p q V X z` is bounded by `B * int_{ball 0 rho} K` (all relative derivatives are moved to the source).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff

namespace HRS.MS.R26T8A
open HRS

section Pot3

variable {d : ℕ}

theorem r26t8a_nest_norm_zero (j : ℕ) (S : Euc d × Euc d → ℝ) (Y w : Euc d) :
    ‖iteratedFDeriv ℝ j (fun w' => S (Y, w')) w‖ = ‖r26t8a_nest 0 j S Y w‖ := by
  unfold r26t8a_nest
  rw [norm_iteratedFDeriv_zero]

theorem r26t8a_nest_vanish (p q : ℕ) (S : Euc d × Euc d → ℝ) (R0 : ℝ)
    (hSv : ∀ Y w, R0 < ‖w‖ → S (Y, w) = 0) (Y w : Euc d) (hw : R0 < ‖w‖) :
    r26t8a_nest p q S Y w = 0 := by
  refine r26t8a_nest_eq_zero p q S Y w ?_
  have : IsOpen {w' : Euc d | R0 < ‖w'‖} := isOpen_lt continuous_const continuous_norm
  filter_upwards [this.mem_nhds hw] with w' hw' Y' using hSv Y' w' hw'

theorem r26t8a_near_conv (K : Euc d → ℝ) (hK0 : ∀ u, 0 ≤ K u) (hKm : Measurable K)
    (hKi : ∀ r : ℝ, IntegrableOn K (ball (0 : Euc d) r))
    (p q : ℕ) (S : Euc d × Euc d → ℝ) (hS : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) S)
    (R0 : ℝ) (hSv : ∀ Y w, R0 < ‖w‖ → S (Y, w) = 0) (B : ℝ) (X z : Euc d)
    (hB : ∀ i ≤ p, ∀ j ≤ q, ∀ Y, ‖Y - X‖ < 1 → ∀ w, ‖r26t8a_nest i j S Y w‖ ≤ B)
    (ρ : ℝ) (hρ : ‖z‖ + R0 < ρ) :
    ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => ∫ u, K u * S (Yw.1, Yw.2 - u)) X z‖ ≤
      B * ∫ u in ball (0 : Euc d) ρ, K u := by
  have hSY : ∀ Y : Euc d, ContDiff ℝ (q : WithTop ℕ∞) (fun w => S (Y, w)) := fun Y =>
    (hS.of_le (by exact_mod_cast Nat.le_add_left q p)).comp
      (contDiff_const.prodMk contDiff_id : ContDiff ℝ (q : WithTop ℕ∞) fun w : Euc d => (Y, w))
  -- stage 1: derivatives in the relative variable
  have hstage1 : ∀ Y : Euc d, ‖Y - X‖ < 1 → ∀ z' : Euc d,
      iteratedFDeriv ℝ q (fun z'' => ∫ u, K u * S (Y, z'' - u)) z' =
        ∫ u, K u • iteratedFDeriv ℝ q (fun w => S (Y, w)) (z' - u) := by
    intro Y hY z'
    have hjet : ∀ (u : Euc d) (i : ℕ), i ≤ q → ∀ x : Euc d,
        iteratedFDeriv ℝ i (fun z'' : Euc d => K u • S (Y, z'' - u)) x =
          K u • iteratedFDeriv ℝ i (fun w => S (Y, w)) (x - u) := by
      intro u i hi x
      have hc : ContDiffAt ℝ (i : WithTop ℕ∞) (fun z'' : Euc d => S (Y, z'' - u)) x :=
        (((hSY Y).of_le (by exact_mod_cast hi)).comp (contDiff_id.sub contDiff_const)).contDiffAt
      rw [iteratedFDeriv_const_smul_apply' hc]
      rw [iteratedFDeriv_comp_sub (f := fun w => S (Y, w)) i u x]
    have hint : Integrable (Set.indicator (ball (0 : Euc d) (‖z'‖ + R0 + 1)) (fun u => B * K u)) volume :=
      (show IntegrableOn (fun u => B * K u) (ball (0 : Euc d) (‖z'‖ + R0 + 1)) volume from
        (hKi (‖z'‖ + R0 + 1)).const_mul B).integrable_indicator measurableSet_ball
    have hG : ∀ᵐ u ∂(volume : Measure (Euc d)), ∀ x ∈ ball z' 1,
        ContDiffAt ℝ (q : WithTop ℕ∞) (fun z'' : Euc d => K u • S (Y, z'' - u)) x :=
      Filter.Eventually.of_forall fun u x _ =>
        (((hSY Y).comp (contDiff_id.sub contDiff_const)).const_smul (K u)).contDiffAt
    have hbd : ∀ i ≤ q, ∀ᵐ u ∂(volume : Measure (Euc d)), ∀ x ∈ ball z' 1,
        ‖iteratedFDeriv ℝ i (fun z'' : Euc d => K u • S (Y, z'' - u)) x‖ ≤
          Set.indicator (ball (0 : Euc d) (‖z'‖ + R0 + 1)) (fun u => B * K u) u := by
      intro i hi
      refine Filter.Eventually.of_forall fun u x hx => ?_
      rw [hjet u i hi x, norm_smul, Real.norm_of_nonneg (hK0 u), r26t8a_nest_norm_zero]
      by_cases hu : u ∈ ball (0 : Euc d) (‖z'‖ + R0 + 1)
      · rw [Set.indicator_of_mem hu]
        have := hB 0 (Nat.zero_le _) i hi Y hY (x - u)
        calc K u * ‖r26t8a_nest 0 i S Y (x - u)‖ ≤ K u * B := mul_le_mul_of_nonneg_left this (hK0 u)
          _ = B * K u := mul_comm _ _
      · rw [Set.indicator_of_notMem hu]
        have h1 : ‖z'‖ + R0 + 1 ≤ ‖u‖ := by simpa using hu
        have h2 : ‖x‖ < ‖z'‖ + 1 := by
          have := norm_le_insert' x z'
          have h3 : ‖x - z'‖ < 1 := by simpa [dist_eq_norm] using hx
          have h4 := norm_sub_norm_le x z'
          linarith
        have h5 : ‖u‖ - ‖x‖ ≤ ‖x - u‖ := by
          have := norm_sub_norm_le u x
          rwa [norm_sub_rev] at this
        rw [r26t8a_nest_vanish 0 i S R0 hSv Y (x - u) (by linarith)]
        simp
    have hmeas : ∀ i ≤ q, ∀ x ∈ ball z' 1,
        AEStronglyMeasurable (fun u => iteratedFDeriv ℝ i (fun z'' : Euc d => K u • S (Y, z'' - u)) x) volume := by
      intro i hi x _
      have e : (fun u => iteratedFDeriv ℝ i (fun z'' : Euc d => K u • S (Y, z'' - u)) x) =
          fun u => K u • iteratedFDeriv ℝ i (fun w => S (Y, w)) (x - u) := funext fun u => hjet u i hi x
      rw [e]
      have hc : Continuous fun u : Euc d => iteratedFDeriv ℝ i (fun w => S (Y, w)) (x - u) :=
        ((hSY Y).continuous_iteratedFDeriv (by exact_mod_cast hi)).comp (continuous_const.sub continuous_id)
      exact hKm.aestronglyMeasurable.smul hc.aestronglyMeasurable
    have key := r26t8a_iter_integral (E := Euc d) (μ := (volume : Measure (Euc d))) (U := ball z' 1)
      isOpen_ball (fun u z'' => K u • S (Y, z'' - u)) q hG hint hbd hmeas q le_rfl z' (mem_ball_self one_pos)
    calc iteratedFDeriv ℝ q (fun z'' => ∫ u, K u * S (Y, z'' - u)) z'
        = iteratedFDeriv ℝ q (fun z'' => ∫ u, K u • S (Y, z'' - u)) z' := rfl
      _ = ∫ u, iteratedFDeriv ℝ q (fun z'' : Euc d => K u • S (Y, z'' - u)) z' ∂volume := key
      _ = _ := by
        congr 1
        funext u
        exact hjet u q le_rfl z'
  -- stage 2: derivatives in the center variable
  have hT : ∀ w : Euc d, ContDiff ℝ (p : WithTop ℕ∞)
      (fun Y : Euc d => iteratedFDeriv ℝ q (fun w' => S (Y, w')) w) :=
    fun w => r26t8a_nest_contDiff q p S w hS
  have hjet2 : ∀ (u : Euc d) (i : ℕ), i ≤ p → ∀ Y : Euc d,
      iteratedFDeriv ℝ i (fun Y' : Euc d => K u • iteratedFDeriv ℝ q (fun w' => S (Y', w')) (z - u)) Y =
        K u • r26t8a_nest i q S Y (z - u) := by
    intro u i hi Y
    have hc : ContDiffAt ℝ (i : WithTop ℕ∞) (fun Y' : Euc d => iteratedFDeriv ℝ q (fun w' => S (Y', w')) (z - u)) Y :=
      ((hT (z - u)).of_le (by exact_mod_cast hi)).contDiffAt
    rw [iteratedFDeriv_const_smul_apply' hc]
    rfl
  have hint2 : Integrable (Set.indicator (ball (0 : Euc d) ρ) (fun u => B * K u)) volume :=
    (show IntegrableOn (fun u => B * K u) (ball (0 : Euc d) ρ) volume from
      (hKi ρ).const_mul B).integrable_indicator measurableSet_ball
  have hG2 : ∀ᵐ u ∂(volume : Measure (Euc d)), ∀ Y ∈ ball X 1,
      ContDiffAt ℝ (p : WithTop ℕ∞)
        (fun Y' : Euc d => K u • iteratedFDeriv ℝ q (fun w' => S (Y', w')) (z - u)) Y :=
    Filter.Eventually.of_forall fun u Y _ => ((hT (z - u)).const_smul (K u)).contDiffAt
  have hbd2 : ∀ i ≤ p, ∀ᵐ u ∂(volume : Measure (Euc d)), ∀ Y ∈ ball X 1,
      ‖iteratedFDeriv ℝ i (fun Y' : Euc d => K u • iteratedFDeriv ℝ q (fun w' => S (Y', w')) (z - u)) Y‖ ≤
        Set.indicator (ball (0 : Euc d) ρ) (fun u => B * K u) u := by
    intro i hi
    refine Filter.Eventually.of_forall fun u Y hY => ?_
    rw [hjet2 u i hi Y, norm_smul, Real.norm_of_nonneg (hK0 u)]
    have hY' : ‖Y - X‖ < 1 := by simpa [dist_eq_norm] using hY
    by_cases hu : u ∈ ball (0 : Euc d) ρ
    · rw [Set.indicator_of_mem hu]
      calc K u * ‖r26t8a_nest i q S Y (z - u)‖ ≤ K u * B :=
            mul_le_mul_of_nonneg_left (hB i hi q le_rfl Y hY' _) (hK0 u)
        _ = B * K u := mul_comm _ _
    · rw [Set.indicator_of_notMem hu]
      have h1 : ρ ≤ ‖u‖ := by simpa using hu
      have h5 : ‖u‖ - ‖z‖ ≤ ‖z - u‖ := by
        have := norm_sub_norm_le u z
        rwa [norm_sub_rev] at this
      rw [r26t8a_nest_vanish i q S R0 hSv Y (z - u) (by linarith)]
      simp
  have hmeas2 : ∀ i ≤ p, ∀ Y ∈ ball X 1,
      AEStronglyMeasurable (fun u => iteratedFDeriv ℝ i
        (fun Y' : Euc d => K u • iteratedFDeriv ℝ q (fun w' => S (Y', w')) (z - u)) Y) volume := by
    intro i hi Y _
    have e : (fun u => iteratedFDeriv ℝ i
        (fun Y' : Euc d => K u • iteratedFDeriv ℝ q (fun w' => S (Y', w')) (z - u)) Y) =
        fun u => K u • r26t8a_nest i q S Y (z - u) := funext fun u => hjet2 u i hi Y
    rw [e]
    have hc : Continuous fun u : Euc d => r26t8a_nest i q S Y (z - u) :=
      (r26t8a_nest_continuous i q S
        (hS.of_le (by exact_mod_cast Nat.add_le_add_right hi q))).comp
        (continuous_const.prodMk (continuous_const.sub continuous_id))
    exact hKm.aestronglyMeasurable.smul hc.aestronglyMeasurable
  have key2 := r26t8a_iter_integral (E := Euc d) (μ := (volume : Measure (Euc d))) (U := ball X 1)
    isOpen_ball (fun u Y' => K u • iteratedFDeriv ℝ q (fun w' => S (Y', w')) (z - u)) p hG2 hint2 hbd2 hmeas2
    p le_rfl X (mem_ball_self one_pos)
  -- identify
  have hev : (fun Y : Euc d => iteratedFDeriv ℝ q (fun w => ∫ u, K u * S (Y, w - u)) z) =ᶠ[𝓝 X]
      fun Y => ∫ u, K u • iteratedFDeriv ℝ q (fun w' => S (Y, w')) (z - u) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (one_pos : (0 : ℝ) < 1))] with Y hY
    exact hstage1 Y (by simpa [dist_eq_norm] using hY) z
  have hform : r26t8a_nest p q (fun Yw : Euc d × Euc d => ∫ u, K u * S (Yw.1, Yw.2 - u)) X z =
      ∫ u, K u • r26t8a_nest p q S X (z - u) := by
    have h1 : r26t8a_nest p q (fun Yw : Euc d × Euc d => ∫ u, K u * S (Yw.1, Yw.2 - u)) X z =
        iteratedFDeriv ℝ p (fun Y : Euc d => ∫ u, K u • iteratedFDeriv ℝ q (fun w' => S (Y, w')) (z - u)) X := by
      unfold r26t8a_nest
      exact (hev.iteratedFDeriv ℝ p).self_of_nhds
    rw [h1]
    refine key2.trans ?_
    congr 1
    funext u
    exact hjet2 u p le_rfl X
  rw [hform]
  have hle : ∀ u, ‖K u • r26t8a_nest p q S X (z - u)‖ ≤
      Set.indicator (ball (0 : Euc d) ρ) (fun u => B * K u) u := by
    intro u
    rw [norm_smul, Real.norm_of_nonneg (hK0 u)]
    by_cases hu : u ∈ ball (0 : Euc d) ρ
    · rw [Set.indicator_of_mem hu]
      calc K u * ‖r26t8a_nest p q S X (z - u)‖ ≤ K u * B :=
            mul_le_mul_of_nonneg_left (hB p le_rfl q le_rfl X (by simp) _) (hK0 u)
        _ = B * K u := mul_comm _ _
    · rw [Set.indicator_of_notMem hu]
      have h1 : ρ ≤ ‖u‖ := by simpa using hu
      have h5 : ‖u‖ - ‖z‖ ≤ ‖z - u‖ := by
        have := norm_sub_norm_le u z
        rwa [norm_sub_rev] at this
      rw [r26t8a_nest_vanish p q S R0 hSv X (z - u) (by linarith)]
      simp
  calc _ ≤ ∫ u, Set.indicator (ball (0 : Euc d) ρ) (fun u => B * K u) u :=
        norm_integral_le_of_norm_le hint2 (Filter.Eventually.of_forall hle)
    _ = B * ∫ u in ball (0 : Euc d) ρ, K u := by
        rw [integral_indicator measurableSet_ball, integral_const_mul]

end Pot3

end HRS.MS.R26T8A
