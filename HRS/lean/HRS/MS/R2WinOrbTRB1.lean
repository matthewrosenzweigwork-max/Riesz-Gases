import HRS.MS.R2WinOrbNLAux11
import HRS.MS.WadAux101
import HRS.MS.WadAux14

/-!
# S10.3 packet [B], part 1: decay-weighted Gaussian averages and iterated differences

Prefix `s103b_`, namespace `HRS.MS.R2WinOrbNL`.  The weight is `w(y) = (1+‖y‖)⁻¹` (a DECAY weight; the repository's Mehler estimates `s83_*`/`s8f_*` are for the growth
weights `⟨y⟩^M`, `M ≥ 0`).

* `s103b_peetre`: `1+‖u‖ ≤ (1+‖u+v‖)(1+‖v‖)`.
* `s103b_G_wt`: the Gaussian average `G_{c,σ} g(x) = ∫ g(cx+σz) dγ` of `g` with `|g| ≤ A w` satisfies `|G_{c,σ} g(x)| ≤ A m₁ (1+c‖x‖)⁻¹`, `m₁ = ∫(1+σ₀‖z‖)dγ`.
* `s103b_dp_bound`: iterated mean value inequality with the decay weight: for `g ∈ C^k` with `‖D^i g‖ ≤ N w` (`1 ≤ i ≤ k`) and `Σ‖η_l‖ ≤ 1/8`,
  `‖Δ_{η_1}⋯Δ_{η_k} g (y)‖ ≤ N (5/4)^k ∏‖η_l‖ w(y)`.  (No zeroth-order bound is used when `k ≥ 1`.)
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.Wad

variable {d : ℕ}

theorem s103b_peetre (u v : Euc d) : 1 + ‖u‖ ≤ (1 + ‖u + v‖) * (1 + ‖v‖) := by
  have h1 : ‖u‖ ≤ ‖u + v‖ + ‖v‖ := by
    calc ‖u‖ = ‖(u + v) - v‖ := by simp
      _ ≤ ‖u + v‖ + ‖v‖ := norm_sub_le _ _
  nlinarith [norm_nonneg (u + v), norm_nonneg v]

theorem s103b_mom_one (σ₀ : ℝ) : mom d 1 σ₀ = ∫ z : Euc d, (1 + σ₀ * ‖z‖) ∂(stdGaussian (Euc d)) := by
  unfold mom
  simp

theorem s103b_G_wt {g : Euc d → ℝ} {A : ℝ} (hA : ∀ y, |g y| ≤ A * (1 + ‖y‖)⁻¹)
    {c σ σ₀ : ℝ} (hc0 : 0 < c) (hσ : |σ| ≤ σ₀) (x : Euc d) :
    |s83_G c σ g x| ≤ A * mom d 1 σ₀ * (1 + c * ‖x‖)⁻¹ := by
  have hA0 : 0 ≤ A := by
    have := hA 0
    simpa using (abs_nonneg _).trans this
  have hσ0 : 0 ≤ σ₀ := (abs_nonneg _).trans hσ
  have hpos : 0 < 1 + c * ‖x‖ := by positivity
  set B : Euc d → ℝ := fun z => A * (1 + σ₀ * ‖z‖) / (1 + c * ‖x‖) with hB
  have hBi : Integrable B (stdGaussian (Euc d)) := by
    have := (s83_int_one_add_mul (d := d) hσ0 1).const_mul (A / (1 + c * ‖x‖))
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only [hB, pow_one]
    ring
  have hbd : ∀ z : Euc d, ‖g (c • x + σ • z)‖ ≤ B z := by
    intro z
    rw [Real.norm_eq_abs]
    refine (hA _).trans ?_
    have hp := s103b_peetre (c • x) (σ • z)
    have hn1 : ‖c • x‖ = c * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc0]
    have hn2 : ‖σ • z‖ ≤ σ₀ * ‖z‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hσ (norm_nonneg _)
    have hq : 0 < 1 + ‖c • x + σ • z‖ := by positivity
    rw [hn1] at hp
    have h3 : (1 + ‖c • x + σ • z‖)⁻¹ ≤ (1 + σ₀ * ‖z‖) / (1 + c * ‖x‖) := by
      rw [inv_eq_one_div, div_le_div_iff₀ hq hpos]
      have : (1 + c * ‖x‖) ≤ (1 + ‖c • x + σ • z‖) * (1 + σ₀ * ‖z‖) :=
        hp.trans (mul_le_mul_of_nonneg_left (by linarith) hq.le)
      linarith
    calc A * (1 + ‖c • x + σ • z‖)⁻¹ ≤ A * ((1 + σ₀ * ‖z‖) / (1 + c * ‖x‖)) :=
          mul_le_mul_of_nonneg_left h3 hA0
      _ = B z := by simp only [hB]; ring
  have hint : ∫ z, B z ∂(stdGaussian (Euc d)) = A * mom d 1 σ₀ * (1 + c * ‖x‖)⁻¹ := by
    simp only [hB]
    have : (fun z : Euc d => A * (1 + σ₀ * ‖z‖) / (1 + c * ‖x‖)) =
        fun z => (A / (1 + c * ‖x‖)) * (1 + σ₀ * ‖z‖) := by funext z; ring
    rw [this, integral_const_mul, s103b_mom_one]
    ring
  rw [← hint, ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le hBi (Eventually.of_forall hbd)

/-- The ball version of the decay weight: `w(y') ≤ (5/4) w(y)` for `‖y'-y‖ ≤ 1/4`. -/
theorem s103b_w_ball {y y' : Euc d} (h : ‖y' - y‖ ≤ 1 / 4) :
    (1 + ‖y'‖)⁻¹ ≤ (5 / 4) * (1 + ‖y‖)⁻¹ := by
  have h1 : ‖y‖ ≤ ‖y'‖ + 1 / 4 := by
    calc ‖y‖ = ‖y' - (y' - y)‖ := by simp
      _ ≤ ‖y'‖ + ‖y' - y‖ := norm_sub_le _ _
      _ ≤ ‖y'‖ + 1 / 4 := by linarith
  have hp : 0 < 1 + ‖y'‖ := by positivity
  have hq : 0 < 1 + ‖y‖ := by positivity
  rw [inv_eq_one_div, inv_eq_one_div, ← mul_div_assoc, div_le_div_iff₀ hp hq]
  nlinarith [norm_nonneg y, norm_nonneg y']

theorem s103b_dp_bound : ∀ (k : ℕ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : Euc d → F) {N : ℝ}, 0 ≤ N → ContDiff ℝ k g →
    (∀ i, i ≤ k → (1 ≤ i ∨ k = 0) → ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ N * (1 + ‖y‖)⁻¹) →
    ∀ η : List (Euc d), η.length = k → (η.map (fun e => ‖e‖)).sum ≤ 1 / 8 → ∀ y,
      ‖s8f_dp η g y‖ ≤ N * (5 / 4) ^ k * (η.map (fun e => ‖e‖)).prod * (1 + ‖y‖)⁻¹ := by
  intro k
  induction k with
  | zero =>
    intro F _ _ g N hN hg hb η hη hs y
    have : η = [] := List.length_eq_zero_iff.1 hη
    subst this
    simp only [s8f_dp, pow_zero, mul_one, List.map_nil, List.prod_nil]
    have := hb 0 le_rfl (Or.inr rfl) y
    rwa [norm_iteratedFDeriv_zero] at this
  | succ k ih =>
    intro F _ _ g N hN hg hb η hη hs y
    obtain ⟨e, rest, rfl⟩ : ∃ e rest, η = e :: rest := by
      cases η with
      | nil => simp at hη
      | cons e rest => exact ⟨e, rest, rfl⟩
    have hη' : rest.length = k := by simpa using hη
    simp only [List.map_cons, List.sum_cons, List.prod_cons] at hs ⊢
    have hrest : (rest.map (fun e => ‖e‖)).sum ≤ 1 / 8 := by linarith [norm_nonneg e]
    have hdg : Differentiable ℝ g := hg.differentiable (by simp)
    have hDg : ContDiff ℝ k (fderiv ℝ g) := hg.fderiv_right (by norm_cast)
    have hP : 0 ≤ (rest.map (fun e => ‖e‖)).prod := List.prod_nonneg (by
      intro x hx
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg a)
    have hS : 0 ≤ (rest.map (fun e => ‖e‖)).sum := List.sum_nonneg (by
      intro x hx
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg a)
    have hw0 : 0 ≤ (1 + ‖y‖)⁻¹ := inv_nonneg.2 (by positivity)
    set C : ℝ := N * (5 / 4) ^ k * (rest.map (fun e => ‖e‖)).prod * ((5 / 4) * (1 + ‖y‖)⁻¹) with hC
    have hmv := (convex_ball y (1 / 4 : ℝ)).norm_image_sub_le_of_norm_fderiv_le (f := s8f_dp rest g) (C := C)
      (fun y' _ => (s8f_dp_differentiable rest hdg) y') (fun y' hy' => ?_) (mem_ball_self (by norm_num))
      (show y + e ∈ ball y (1 / 4) by
        rw [mem_ball_iff_norm]; simp only [add_sub_cancel_left]; linarith [norm_nonneg e])
    · simp only [add_sub_cancel_left] at hmv
      show ‖s8f_dp rest g (y + e) - s8f_dp rest g y‖ ≤ _
      refine hmv.trans (le_of_eq ?_)
      rw [hC]; ring
    · rw [s8f_dp_fderiv rest hdg]
      have := ih (fderiv ℝ g) (N := N) hN hDg (fun i hi _ y' => by
        rw [norm_iteratedFDeriv_fderiv]; exact hb (i + 1) (by omega) (Or.inl (by omega)) y') rest hη' hrest y'
      refine this.trans ?_
      have hy'' : ‖y' - y‖ ≤ 1 / 4 := by rw [mem_ball_iff_norm] at hy'; exact hy'.le
      have hj := s103b_w_ball hy''
      rw [hC]
      calc N * (5 / 4) ^ k * (rest.map (fun e => ‖e‖)).prod * (1 + ‖y'‖)⁻¹
          ≤ N * (5 / 4) ^ k * (rest.map (fun e => ‖e‖)).prod * ((5 / 4) * (1 + ‖y‖)⁻¹) :=
            mul_le_mul_of_nonneg_left hj (by positivity)
        _ = _ := rfl

end HRS.MS.R2WinOrbNL

end
