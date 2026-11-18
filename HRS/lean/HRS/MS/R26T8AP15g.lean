import HRS.MS.R26T8AP15e
import HRS.MS.R26T8AP08b

/-!
# S8.2 T8A P15g: the separation factor and the three product corollaries
`r26t8a_nest_cM_zero`: `‖nest i 0 (cM alpha)‖ ≤ 2 B pairWeight 1 * min 1 ‖z‖` (mean value theorem for `D^i alpha`).
Corollaries `r26t8a_conormal_mul_xw`, `_mul_yw`, `_mul_sum`, `_mul_diff`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_nest_cM_zero {k : ℕ} {α : Euc d → ℝ} (hα : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) α) {B : ℝ}
    (hab : ∀ j ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ j α x‖ ≤ B * jbracket x) (hB : 0 ≤ B) {i : ℕ} (hi : i ≤ k)
    (X z : Euc d) :
    ‖r26t8a_nest i 0 (r26t8a_cM α) X z‖ ≤ 2 * B * HRS.MS.Phase2S82.pairWeight 1 (X + (1 / 2 : ℝ) • z)
      (X - (1 / 2 : ℝ) • z) * min 1 ‖z‖ := by
  have hαk : ContDiff ℝ (i : WithTop ℕ∞) α := hα.of_le (by exact_mod_cast (by omega : i ≤ k + 1))
  rw [r26t8a_nest_zero]
  have e : (fun Y : Euc d => r26t8a_cM α (Y, z)) =
      (fun Y => α (Y + (1 / 2 : ℝ) • z)) - (fun Y => α (Y - (1 / 2 : ℝ) • z)) := by
    funext Y
    simp only [r26t8a_cM, r26t8a_cX, r26t8a_cY, Pi.sub_apply]
    congr 2
    module
  have hc1 : ContDiff ℝ (i : WithTop ℕ∞) (fun Y : Euc d => α (Y + (1 / 2 : ℝ) • z)) :=
    hαk.comp (contDiff_id.add contDiff_const)
  have hc2 : ContDiff ℝ (i : WithTop ℕ∞) (fun Y : Euc d => α (Y - (1 / 2 : ℝ) • z)) :=
    hαk.comp (contDiff_id.sub contDiff_const)
  rw [e, iteratedFDeriv_sub_apply hc1.contDiffAt hc2.contDiffAt, iteratedFDeriv_comp_add_right,
    iteratedFDeriv_comp_sub]
  set f : Euc d → (Euc d [×i]→L[ℝ] ℝ) := iteratedFDeriv ℝ i α with hf
  set x : Euc d := X + (1 / 2 : ℝ) • z with hx
  set y : Euc d := X - (1 / 2 : ℝ) • z with hy
  have hxy : x - y = z := by rw [hx, hy]; module
  have hjx := r26t8a_one_le_jb x
  have hjy := r26t8a_one_le_jb y
  have hr0 : 0 ≤ min 1 ‖z‖ := le_min zero_le_one (norm_nonneg _)
  have hpw : HRS.MS.Phase2S82.pairWeight 1 x y = jbracket x * jbracket y := by
    simp only [HRS.MS.Phase2S82.pairWeight, Real.rpow_one]
  rw [hpw]
  by_cases hz1 : ‖z‖ < 1
  · have hmin : min 1 ‖z‖ = ‖z‖ := min_eq_right hz1.le
    rw [hmin]
    set s : Set (Euc d) := Metric.closedBall 0 (max ‖x‖ ‖y‖) with hs
    have hsc : Convex ℝ s := convex_closedBall _ _
    have hxs : x ∈ s := by rw [hs, mem_closedBall_zero_iff]; exact le_max_left _ _
    have hys : y ∈ s := by rw [hs, mem_closedBall_zero_iff]; exact le_max_right _ _
    have hdiff : ∀ u ∈ s, DifferentiableAt ℝ f u := fun u _ =>
      (hα.differentiable_iteratedFDeriv (m := i) (by exact_mod_cast (by omega : i < k + 1)) u)
    have hbd : ∀ u ∈ s, ‖fderiv ℝ f u‖ ≤ B * (jbracket x * jbracket y) := by
      intro u hu
      rw [hf, norm_fderiv_iteratedFDeriv]
      refine (hab (i + 1) (by omega) u).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hB
      have hu' : ‖u‖ ≤ max ‖x‖ ‖y‖ := by rwa [hs, mem_closedBall_zero_iff] at hu
      rcases le_max_iff.1 hu' with h | h
      · exact (r26t8a_jb_mono h).trans (r26t8a_jb_mul_ge x y)
      · exact (r26t8a_jb_mono h).trans (by
          have := r26t8a_jb_mul_ge y x
          rw [mul_comm] at this; exact this)
    have := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbd hsc hys hxs
    rw [hxy] at this
    calc ‖f x - f y‖ ≤ B * (jbracket x * jbracket y) * ‖z‖ := by
          exact this
      _ ≤ 2 * B * (jbracket x * jbracket y) * ‖z‖ := by
          have : 0 ≤ B * (jbracket x * jbracket y) * ‖z‖ := by positivity
          nlinarith
  · have hmin : min 1 ‖z‖ = 1 := min_eq_left (not_lt.1 hz1)
    rw [hmin, mul_one]
    refine (norm_sub_le _ _).trans ?_
    have h1 := hab i (by omega) x
    have h2 := hab i (by omega) y
    have h3 := r26t8a_jb_add_le x y
    rw [hf]
    nlinarith

theorem r26t8a_conormal_mul_xw {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {k b : ℕ} {M σ A B : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) {α : Euc d → ℝ} (hα : ContDiff ℝ (k : WithTop ℕ∞) α)
    (hab : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j α x‖ ≤ B * jbracket x) {G : Euc d → Euc d → ℝ}
    (hG : Conormal k b M σ A G) :
    Conormal k b (M + 1) σ (2 ^ k * ((k + 1 : ℝ) ^ 2 * B * A)) (fun x y => α x * G x y) := by
  have h := r26t8a_conormal_mul_gen hchi (m := 1) 0 (by norm_num) hA hB (r26t8a_cX_contDiff hα)
    (fun i j hij X z _ => by
      have := (r26t8a_nest_cX hα hab hij X z).trans (mul_le_mul_of_nonneg_left (r26t8a_jb_x_pair X z) hB)
      simp only [pow_zero, ite_self, mul_one]
      exact this) hG
  simp only [Nat.cast_zero, sub_zero, r26t8a_cpair_cX] at h
  exact h

theorem r26t8a_conormal_mul_sum {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {k b : ℕ} {M σ A B : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) {α : Euc d → ℝ} (hα : ContDiff ℝ (k : WithTop ℕ∞) α)
    (hab : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j α x‖ ≤ B * jbracket x) {G : Euc d → Euc d → ℝ}
    (hG : Conormal k b M σ A G) :
    Conormal k b (M + 1) σ (2 ^ k * ((k + 1 : ℝ) ^ 2 * (2 * B) * A)) (fun x y => (α x + α y) * G x y) := by
  have h := r26t8a_conormal_mul_gen hchi (m := 1) 0 (by norm_num) hA (by positivity : 0 ≤ 2 * B)
    (c := r26t8a_cP α) ((r26t8a_cX_contDiff hα).add (r26t8a_cY_contDiff hα))
    (fun i j hij X z _ => by
      have := r26t8a_nest_cP hα hab hB hij X z
      simp only [pow_zero, ite_self, mul_one]
      exact this) hG
  simp only [Nat.cast_zero, sub_zero, r26t8a_cpair_cP] at h
  exact h

theorem r26t8a_conormal_mul_diff {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {k b : ℕ} {M σ A B : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) {α : Euc d → ℝ} (hα : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) α)
    (hab : ∀ j ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ j α x‖ ≤ B * jbracket x) {G : Euc d → Euc d → ℝ}
    (hG : Conormal k b M σ A G) :
    Conormal k b (M + 1) (σ - 1) (2 ^ k * ((k + 1 : ℝ) ^ 2 * (2 * B) * A)) (fun x y => (α x - α y) * G x y) := by
  have hαk : ContDiff ℝ (k : WithTop ℕ∞) α := hα.of_le (by exact_mod_cast Nat.le_succ k)
  have h := r26t8a_conormal_mul_gen hchi (m := 1) 1 le_rfl hA (by positivity : 0 ≤ 2 * B)
    (c := r26t8a_cM α) ((r26t8a_cX_contDiff hαk).sub (r26t8a_cY_contDiff hαk))
    (fun i j hij X z _ => by
      by_cases hj : j = 0
      · subst hj
        simp only [ite_true, pow_one]
        exact r26t8a_nest_cM_zero hα hab hB (by omega) X z
      · simp only [hj, ite_false, mul_one]
        exact r26t8a_nest_cM_pos hαk (fun j hj x => hab j (by omega) x) hB hij X z) hG
  simp only [Nat.cast_one, r26t8a_cpair_cM] at h
  exact h

theorem r26t8a_conormal_mul_yw {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {k b : ℕ} {M σ A B : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) {α : Euc d → ℝ} (hα : ContDiff ℝ (k : WithTop ℕ∞) α)
    (hab : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j α x‖ ≤ B * jbracket x) {G : Euc d → Euc d → ℝ}
    (hG : Conormal k b M σ A G) :
    Conormal k b (M + 1) σ (2 ^ k * ((k + 1 : ℝ) ^ 2 * B * A)) (fun x y => α y * G x y) := by
  have h := r26t8a_conormal_mul_xw hchi hA hB hα hab (r26t8a_f24_conormal_swap hchi hG)
  exact r26t8a_f24_conormal_swap hchi h

end HRS.MS.R26T8A
