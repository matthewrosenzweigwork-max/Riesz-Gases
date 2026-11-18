import HRS.MS.S104gJc1

/-!
# S10.4 packet S104G, part 3: Lipschitz continuity in the terminal time from the difference-quotient convergence

Prefix `s104g_`, namespace `HRS.MS.R2WinOrbNL`.

`s104g_lipT`: if `h⁻¹ (u₁(t+h) r - u₁(t) r) → u₂(t) r` in the `C^1` sup norm (for `r ≤ t, t+h ≤ T0`) and `‖∇u₂(t) r‖ ≤ Gb`, then
`‖∇u₁(t) r (x) - ∇u₁(t') r (x)‖ ≤ Gb |t - t'|` for all `r ≤ t, t'` (mean value theorem for the gradient).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole

variable {d : ℕ}

theorem s104g_grad_quot {f1 f0 f2 : Euc d → ℝ} (h : ℝ) {x : Euc d} (h1 : DifferentiableAt ℝ f1 x)
    (h0 : DifferentiableAt ℝ f0 x) (h2 : DifferentiableAt ℝ f2 x) :
    gradient (fun y => h⁻¹ * (f1 y - f0 y) - f2 y) x = h⁻¹ • (gradient f1 x - gradient f0 x) - gradient f2 x := by
  have hq : HasFDerivAt (fun y => h⁻¹ * (f1 y - f0 y) - f2 y)
      (h⁻¹ • (fderiv ℝ f1 x - fderiv ℝ f0 x) - fderiv ℝ f2 x) x :=
    (((h1.hasFDerivAt.sub h0.hasFDerivAt).const_mul h⁻¹).sub h2.hasFDerivAt)
  simp only [gradient, hq.fderiv, map_sub, map_smul]

theorem s104g_lipT {u1 u2 : ℝ → ℝ → Euc d → ℝ} {T0 Gb : ℝ}
    (hsm1 : ∀ t ∈ Set.Icc (0 : ℝ) T0, ∀ r ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ 2 (u1 t r))
    (hsm2 : ∀ t ∈ Set.Icc (0 : ℝ) T0, ∀ r ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ 1 (u2 t r))
    (dq : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T0 → ∀ e : ℝ, 0 < e → ∃ δ : ℝ, 0 < δ ∧
      ∀ h : ℝ, h ≠ 0 → |h| < δ → r ≤ t + h → t + h ≤ T0 → ∀ x : Euc d,
        ‖iteratedFDeriv ℝ 1 (fun y => h⁻¹ * (u1 (t + h) r y - u1 t r y) - u2 t r y) x‖ ≤ e)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) T0, ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, ‖gradient (u2 t r) x‖ ≤ Gb) :
    ∀ t ∈ Set.Icc (0 : ℝ) T0, ∀ t' ∈ Set.Icc (0 : ℝ) T0, ∀ r : ℝ, 0 ≤ r → r ≤ t → r ≤ t' → ∀ x : Euc d,
      ‖gradient (u1 t r) x - gradient (u1 t' r) x‖ ≤ Gb * |t - t'| := by
  intro t ht t' ht' r hr hrt hrt' x
  have hder : ∀ τ ∈ Set.Icc r T0, HasDerivWithinAt (fun σ => gradient (u1 σ r) x) (gradient (u2 τ r) x)
      (Set.Icc r T0) τ := by
    intro τ hτ
    have hτ0 : 0 ≤ τ := hr.trans hτ.1
    rw [hasDerivWithinAt_iff_tendsto_slope, Metric.tendsto_nhdsWithin_nhds]
    intro e he
    obtain ⟨δ, hδ, hh⟩ := dq r τ hr hτ.1 hτ.2 (e / 2) (half_pos he)
    refine ⟨δ, hδ, fun y hy hyd => ?_⟩
    obtain ⟨hyI, hyne⟩ := hy
    have hyne' : y - τ ≠ 0 := sub_ne_zero.2 hyne
    have hyτ : τ + (y - τ) = y := by ring
    have hd1 : DifferentiableAt ℝ (u1 y r) x :=
      ((hsm1 y ⟨hr.trans hyI.1, hyI.2⟩ r ⟨hr, hyI.1⟩).differentiable (by norm_num)).differentiableAt
    have hd0 : DifferentiableAt ℝ (u1 τ r) x :=
      ((hsm1 τ ⟨hτ0, hτ.2⟩ r ⟨hr, hτ.1⟩).differentiable (by norm_num)).differentiableAt
    have hd2 : DifferentiableAt ℝ (u2 τ r) x :=
      ((hsm2 τ ⟨hτ0, hτ.2⟩ r ⟨hr, hτ.1⟩).differentiable (by norm_num)).differentiableAt
    have hbd := hh (y - τ) hyne' (by rwa [Real.dist_eq] at hyd) (by rw [hyτ]; exact hyI.1)
      (by rw [hyτ]; exact hyI.2) x
    rw [hyτ] at hbd
    have hd1' : DifferentiableAt ℝ (u1 y r) x := hd1
    rw [norm_iteratedFDeriv_one, ← s104g_norm_gradient, s104g_grad_quot _ hd1' hd0 hd2] at hbd
    rw [dist_eq_norm, slope_def_module]
    exact lt_of_le_of_lt hbd (by linarith)
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun σ => gradient (u1 σ r) x)
    (f' := fun τ => gradient (u2 τ r) x) (C := Gb) (s := Set.Icc r T0) hder
    (fun τ hτ => hb τ ⟨hr.trans hτ.1, hτ.2⟩ r ⟨hr, hτ.1⟩ x) (convex_Icc r T0) ⟨hrt', ht'.2⟩ ⟨hrt, ht.2⟩
  rw [Real.norm_eq_abs] at hmv
  exact hmv

end HRS.MS.R2WinOrbNL

end
