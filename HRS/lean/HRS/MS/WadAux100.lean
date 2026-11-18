import HRS.MS.WadAux99

/-!
# S8.3, packet S8F-1, part 1: iterated plain differences and their weighted bound

`s8f_dp η g`: the iterated difference `Δ_{η_1} ⋯ Δ_{η_k} g` along a list of vectors (outermost `Δ` is the head).
`s8f_dp_fderiv`: `D` commutes with the differences.  `s8f_dp_bound`: for `g ∈ C^k` with weighted derivative bounds through order `k`
and `Σ‖η_i‖ ≤ 1/8`, `‖Δ_η g (y)‖ ≤ N (3^M)^k ∏‖η_i‖ ⟨y⟩^M` (iterated mean value inequality).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

def s8f_dp {F : Type} [AddCommGroup F] : List (Euc d) → (Euc d → F) → Euc d → F
  | [], g => g
  | e :: rest, g => fun y => s8f_dp rest g (y + e) - s8f_dp rest g y

theorem s8f_dp_differentiable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (η : List (Euc d))
    {g : Euc d → F} (hg : Differentiable ℝ g) : Differentiable ℝ (s8f_dp η g) := by
  induction η with
  | nil => exact hg
  | cons e rest ih =>
    intro y
    show DifferentiableAt ℝ (fun y => s8f_dp rest g (y + e) - s8f_dp rest g y) y
    exact ((ih (y + e)).comp y (differentiableAt_id.add_const e)).sub (ih y)

theorem s8f_dp_fderiv {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (η : List (Euc d))
    {g : Euc d → F} (hg : Differentiable ℝ g) :
    fderiv ℝ (s8f_dp η g) = s8f_dp η (fderiv ℝ g) := by
  induction η with
  | nil => rfl
  | cons e rest ih =>
    funext y
    show fderiv ℝ (fun y => s8f_dp rest g (y + e) - s8f_dp rest g y) y = _
    rw [s8e_fderiv_shift_sub (s8f_dp_differentiable rest hg) e y, ih]
    rfl

theorem s8f_dp_bound {M : ℝ} (hM : 0 ≤ M) : ∀ (k : ℕ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : Euc d → F) {N : ℝ}, ContDiff ℝ k g → (∀ i ≤ k, ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ N * jbracket y ^ M) →
    ∀ η : List (Euc d), η.length = k → (η.map (fun e => ‖e‖)).sum ≤ 1 / 8 → ∀ y,
      ‖s8f_dp η g y‖ ≤ N * (3 ^ M) ^ k * (η.map (fun e => ‖e‖)).prod * jbracket y ^ M := by
  intro k
  induction k with
  | zero =>
    intro F _ _ g N hg hb η hη hs y
    have : η = [] := List.length_eq_zero_iff.1 hη
    subst this
    simp only [s8f_dp, pow_zero, mul_one, List.map_nil, List.prod_nil]
    have := hb 0 le_rfl y
    rwa [norm_iteratedFDeriv_zero] at this
  | succ k ih =>
    intro F _ _ g N hg hb η hη hs y
    obtain ⟨e, rest, rfl⟩ : ∃ e rest, η = e :: rest := by
      cases η with
      | nil => simp at hη
      | cons e rest => exact ⟨e, rest, rfl⟩
    have hη' : rest.length = k := by simpa using hη
    simp only [List.map_cons, List.sum_cons, List.prod_cons] at hs ⊢
    have hrest : (rest.map (fun e => ‖e‖)).sum ≤ 1 / 8 := by linarith [norm_nonneg e]
    have hdg : Differentiable ℝ g := hg.differentiable (by simp)
    have hDg : ContDiff ℝ k (fderiv ℝ g) := hg.fderiv_right (by norm_cast)
    have hN : 0 ≤ N := by
      have h0 := hb 0 (Nat.zero_le _) y
      rw [norm_iteratedFDeriv_zero] at h0
      have hj : 0 < jbracket y ^ M := Real.rpow_pos_of_pos (s83_jb_pos y) _
      by_contra hneg
      push Not at hneg
      nlinarith [norm_nonneg (g y)]
    have hP : 0 ≤ (rest.map (fun e => ‖e‖)).prod := List.prod_nonneg (by
      intro x hx
      obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
      exact norm_nonneg a)
    have h3 : 0 ≤ (3 : ℝ) ^ M := Real.rpow_nonneg (by norm_num) _
    set C : ℝ := N * (3 ^ M) ^ k * (rest.map (fun e => ‖e‖)).prod * (3 ^ M * jbracket y ^ M) with hC
    have hmv := (convex_ball y (1 / 4 : ℝ)).norm_image_sub_le_of_norm_fderiv_le (f := s8f_dp rest g) (C := C)
      (fun y' _ => (s8f_dp_differentiable rest hdg) y') (fun y' hy' => ?_) (mem_ball_self (by norm_num))
      (show y + e ∈ ball y (1 / 4) by
        rw [mem_ball_iff_norm]; simp only [add_sub_cancel_left]; linarith [norm_nonneg e,
          List.sum_nonneg (l := rest.map (fun e => ‖e‖)) (by
            intro x hx
            obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
            exact norm_nonneg a)])
    · simp only [add_sub_cancel_left] at hmv
      show ‖s8f_dp rest g (y + e) - s8f_dp rest g y‖ ≤ _
      refine hmv.trans (le_of_eq ?_)
      rw [hC]; ring
    · rw [s8f_dp_fderiv rest hdg]
      have := ih (fderiv ℝ g) (N := N) hDg (fun i hi y' => by
        rw [norm_iteratedFDeriv_fderiv]; exact hb (i + 1) (by omega) y') rest hη' hrest y'
      refine this.trans ?_
      have hj := s84_jb_ball hM hy'
      rw [hC]
      calc N * (3 ^ M) ^ k * (rest.map (fun e => ‖e‖)).prod * jbracket y' ^ M
          ≤ N * (3 ^ M) ^ k * (rest.map (fun e => ‖e‖)).prod * (3 ^ M * jbracket y ^ M) :=
            mul_le_mul_of_nonneg_left hj (by positivity)
        _ = _ := rfl

end HRS.MS.Wad
