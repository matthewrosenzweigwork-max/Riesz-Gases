import HRS.MS.WadAux77

/-!
# S8.3, packet S8E-2, part 2: translation covariance of `𝓑`, linearity in the density, shifted densities

* `s8e_Bop_shift`: `𝓑_{σ(·+z)} (h(·+z)) (x) = 𝓑_σ h (x + z)`.
* `s8e_Bop_rho_sub`: `𝓑_{σ₁ - σ₂} h = 𝓑_{σ₁} h - 𝓑_{σ₂} h` for densities with Gaussian bounds and `h ∈ C²_b`.
* `s8e_shift_gauss`, `s8e_rho_diff_gauss`: the difference density `ρ(·+z) - ρ` of a smooth density with Gaussian
  bounds on its derivatives has Gaussian bounds with constant proportional to `‖z‖`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.MS.Wad

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

theorem s8e_conv_shift (G : Euc d → Euc d) (ρ : Euc d → ℝ) (x z : Euc d) :
    convGradConvW G (fun y => ρ (y + z)) x = convGradConvW G ρ (x + z) := by
  unfold convGradConvW
  conv_rhs => rw [← integral_add_right_eq_self _ z]
  congr 1
  funext y
  simp only [add_sub_add_right_eq_sub]

theorem s8e_gradient_shift (h : Euc d → ℝ) (z y : Euc d) :
    gradient (fun y => h (y + z)) y = gradient h (y + z) := by
  unfold gradient
  rw [fderiv_comp_add_right]

theorem s8e_Bop_shift (σ h : Euc d → ℝ) (z x : Euc d) :
    s84_Bop (fun y => σ (y + z)) (fun y => h (y + z)) x = s84_Bop σ h (x + z) := by
  unfold s84_Bop
  rw [s8e_conv_shift, s8e_gradient_shift]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have := s8e_conv_shift (rieszKernelGrad d ((d : ℝ) / 2))
    (fun y => σ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h y)) j) x z
  simp only [s8e_gradient_shift]
  rw [this]

theorem s8e_exp_shift {c : ℝ} (hc : 0 ≤ c) {z : Euc d} (hz : ‖z‖ ≤ 1) (x : Euc d) :
    Real.exp (-c * ‖x + z‖ ^ 2) ≤ Real.exp c * Real.exp (-(c / 2) * ‖x‖ ^ 2) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h1 : ‖x‖ ≤ ‖x + z‖ + ‖z‖ := by
    have := norm_sub_le (x + z) z
    simpa using this
  have h2 : ‖x‖ ^ 2 ≤ 2 * ‖x + z‖ ^ 2 + 2 * ‖z‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x + z‖ - ‖z‖), norm_nonneg (x + z), norm_nonneg z, norm_nonneg x]
  have h3 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
  nlinarith

theorem s8e_shift_gauss {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Euc d → E}
    (hf : Differentiable ℝ f) {C c : ℝ} (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hb : ∀ y, ‖fderiv ℝ f y‖ ≤ C * Real.exp (-c * ‖y‖ ^ 2)) {z : Euc d} (hz : ‖z‖ ≤ 1) (x : Euc d) :
    ‖f (x + z) - f x‖ ≤ ‖z‖ * (C * Real.exp c) * Real.exp (-(c / 2) * ‖x‖ ^ 2) := by
  have hmv := (convex_closedBall x 1).norm_image_sub_le_of_norm_fderiv_le
    (f := f) (C := C * Real.exp c * Real.exp (-(c / 2) * ‖x‖ ^ 2)) (fun y _ => hf y)
    (fun y hy => by
      rw [mem_closedBall_iff_norm] at hy
      refine (hb y).trans ?_
      have := s8e_exp_shift hc (z := y - x) (by simpa using hy) x
      rw [add_sub_cancel] at this
      calc C * Real.exp (-c * ‖y‖ ^ 2) ≤ C * (Real.exp c * Real.exp (-(c / 2) * ‖x‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left this hC
        _ = _ := by ring)
    (mem_closedBall_self (by norm_num)) (show x + z ∈ closedBall x 1 by
      rw [mem_closedBall_iff_norm]; simpa using hz)
  have e : x + z - x = z := by abel
  rw [e] at hmv
  calc ‖f (x + z) - f x‖ ≤ C * Real.exp c * Real.exp (-(c / 2) * ‖x‖ ^ 2) * ‖z‖ := hmv
    _ = _ := by ring

theorem s8e_rho_diff_gauss {ρ : Euc d → ℝ} (hρ : ContDiff ℝ 2 ρ)
    (hg : ∀ k : ℕ, k ≤ 2 → ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ x : Euc d,
      ‖iteratedFDeriv ℝ k ρ x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2)) :
    ∃ Cρ c : ℝ, 0 ≤ Cρ ∧ 0 < c ∧ ∀ z : Euc d, ‖z‖ ≤ 1 → ∀ x : Euc d,
      |ρ (x + z) - ρ x| ≤ (Cρ * ‖z‖) * Real.exp (-c * ‖x‖ ^ 2) ∧
      ‖fderiv ℝ ρ (x + z) - fderiv ℝ ρ x‖ ≤ (Cρ * ‖z‖) * Real.exp (-c * ‖x‖ ^ 2) := by
  obtain ⟨C1, c1, hC1, hc1, h1⟩ := hg 1 (by norm_num)
  obtain ⟨C2, c2, hC2, hc2, h2⟩ := hg 2 (by norm_num)
  have hd1 : Differentiable ℝ ρ := hρ.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ ρ) :=
    (hρ.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  refine ⟨max (C1 * Real.exp c1) (C2 * Real.exp c2), min (c1 / 2) (c2 / 2), by positivity,
    lt_min (by positivity) (by positivity), fun z hz x => ⟨?_, ?_⟩⟩
  · have := s8e_shift_gauss hd1 hc1.le hC1 (fun y => by
      have := h1 y; rwa [norm_iteratedFDeriv_one] at this) hz x
    rw [← Real.norm_eq_abs]
    refine this.trans ?_
    have : (C1 * Real.exp c1) * Real.exp (-(c1 / 2) * ‖x‖ ^ 2) ≤
        max (C1 * Real.exp c1) (C2 * Real.exp c2) * Real.exp (-min (c1 / 2) (c2 / 2) * ‖x‖ ^ 2) :=
      mul_le_mul (le_max_left _ _) (Real.exp_le_exp.2 (by nlinarith [min_le_left (c1 / 2) (c2 / 2), sq_nonneg ‖x‖]))
        (Real.exp_pos _).le (by positivity)
    nlinarith [norm_nonneg z]
  · have := s8e_shift_gauss hd2 hc2.le hC2 (fun y => by
      have := h2 y
      rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at this
      exact this) hz x
    refine this.trans ?_
    have : (C2 * Real.exp c2) * Real.exp (-(c2 / 2) * ‖x‖ ^ 2) ≤
        max (C1 * Real.exp c1) (C2 * Real.exp c2) * Real.exp (-min (c1 / 2) (c2 / 2) * ‖x‖ ^ 2) :=
      mul_le_mul (le_max_right _ _) (Real.exp_le_exp.2 (by nlinarith [min_le_right (c1 / 2) (c2 / 2), sq_nonneg ‖x‖]))
        (Real.exp_pos _).le (by positivity)
    nlinarith [norm_nonneg z]

end HRS.MS.Wad
