import HRS.MC.CepE1

/-!
# Packet CEPE2, auxiliary 1: one-dimensional facts on `f(u) = -log(2 sin πu)`, `u ∈ (0,1)`
-/

open Set
open scoped NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE2

/-- The profile `f(u) = -log (2 sin (π u))`. -/
def cepe2_f (u : ℝ) : ℝ := -Real.log (2 * Real.sin (Real.pi * u))

/-- Its derivative `f'(u) = -π cot (π u)`. -/
def cepe2_f' (u : ℝ) : ℝ := -(Real.pi * (Real.cos (Real.pi * u) / Real.sin (Real.pi * u)))

theorem cepe2_sin_pos {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : 0 < Real.sin (Real.pi * u) :=
  Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hu.1) (by nlinarith [Real.pi_pos, hu.2])

theorem cepe2_hasDerivAt {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : HasDerivAt cepe2_f (cepe2_f' u) u :=
  HRS.MC.CepE1.cepe1_hasDerivAt_neglog hu

theorem cepe2_f_ge {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : -Real.log 2 ≤ cepe2_f u := by
  unfold cepe2_f
  have hs := cepe2_sin_pos hu
  have : Real.log (2 * Real.sin (Real.pi * u)) ≤ Real.log 2 :=
    Real.log_le_log (by linarith) (by nlinarith [Real.sin_le_one (Real.pi * u)])
  linarith

/-- The quantitative barrier: `f u ≤ M` forces `u` away from `0` and `1`. -/
def cepe2_delta (M : ℝ) : ℝ := Real.exp (-M) / (2 * Real.pi)

theorem cepe2_delta_pos (M : ℝ) : 0 < cepe2_delta M := by
  unfold cepe2_delta; positivity

theorem cepe2_barrier {u M : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (h : cepe2_f u ≤ M) :
    cepe2_delta M ≤ u ∧ cepe2_delta M ≤ 1 - u := by
  have hs := cepe2_sin_pos hu
  have h1 : Real.exp (-M) ≤ 2 * Real.sin (Real.pi * u) := by
    unfold cepe2_f at h
    have : -M ≤ Real.log (2 * Real.sin (Real.pi * u)) := by linarith
    calc Real.exp (-M) ≤ Real.exp (Real.log (2 * Real.sin (Real.pi * u))) := Real.exp_le_exp.2 this
      _ = 2 * Real.sin (Real.pi * u) := Real.exp_log (by linarith)
  have hpi := Real.pi_pos
  unfold cepe2_delta
  constructor
  · have h2 : Real.sin (Real.pi * u) ≤ Real.pi * u := Real.sin_le (mul_pos hpi hu.1).le
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  · have h2 : Real.sin (Real.pi * (1 - u)) ≤ Real.pi * (1 - u) := Real.sin_le (by nlinarith [hu.2])
    have h3 : Real.sin (Real.pi * (1 - u)) = Real.sin (Real.pi * u) := by
      rw [mul_sub, mul_one, Real.sin_pi_sub]
    rw [h3] at h2
    rw [div_le_iff₀ (by positivity)]
    nlinarith

theorem cepe2_f'_strictMono {u v : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) (huv : u < v) :
    cepe2_f' u < cepe2_f' v := by
  have hsu := cepe2_sin_pos hu
  have hsv := cepe2_sin_pos hv
  have hpi := Real.pi_pos
  have hd : 0 < Real.sin (Real.pi * v - Real.pi * u) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith) (by nlinarith [hu.1, hv.2])
  have key : Real.cos (Real.pi * u) / Real.sin (Real.pi * u) -
      Real.cos (Real.pi * v) / Real.sin (Real.pi * v) =
      Real.sin (Real.pi * v - Real.pi * u) / (Real.sin (Real.pi * u) * Real.sin (Real.pi * v)) := by
    rw [Real.sin_sub]
    field_simp
  have : 0 < Real.cos (Real.pi * u) / Real.sin (Real.pi * u) -
      Real.cos (Real.pi * v) / Real.sin (Real.pi * v) := by
    rw [key]; positivity
  unfold cepe2_f'
  nlinarith

theorem cepe2_f'_mono {u v : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) (huv : u ≤ v) :
    cepe2_f' u ≤ cepe2_f' v := by
  rcases huv.lt_or_eq with h | h
  · exact (cepe2_f'_strictMono hu hv h).le
  · rw [h]

/-- Tangent-line inequality (convexity of `f` on `(0,1)`). -/
theorem cepe2_tangent {u v : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) :
    cepe2_f v + cepe2_f' v * (u - v) ≤ cepe2_f u := by
  set g : ℝ → ℝ := fun w => cepe2_f w - cepe2_f v - cepe2_f' v * (w - v) with hg
  have hgd : ∀ w ∈ Ioo (0 : ℝ) 1, HasDerivAt g (cepe2_f' w - cepe2_f' v) w := by
    intro w hw
    have := ((cepe2_hasDerivAt hw).sub_const (cepe2_f v)).sub (((hasDerivAt_id w).sub_const v).const_mul (cepe2_f' v))
    refine HasDerivAt.congr_deriv this ?_
    ring
  have hgv : g v = 0 := by simp [hg]
  rcases lt_trichotomy u v with h | h | h
  · -- u < v : g antitone on [u, v]
    have hsub : Icc u v ⊆ Ioo (0 : ℝ) 1 := fun w hw => ⟨by linarith [hu.1, hw.1], by linarith [hv.2, hw.2]⟩
    have hanti : AntitoneOn g (Icc u v) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc u v)
        (fun w hw => (hgd w (hsub hw)).continuousAt.continuousWithinAt)
        (fun w hw => (hgd w (hsub (interior_subset hw))).differentiableAt.differentiableWithinAt)
        (fun w hw => ?_)
      rw [(hgd w (hsub (interior_subset hw))).deriv]
      rw [interior_Icc] at hw
      have := cepe2_f'_mono (hsub (interior_subset (s := Icc u v) (by rw [interior_Icc]; exact hw))) hv hw.2.le
      linarith
    have := hanti ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h.le
    simp only [hg] at this hgv
    linarith
  · subst h; simp
  · have hsub : Icc v u ⊆ Ioo (0 : ℝ) 1 := fun w hw => ⟨by linarith [hv.1, hw.1], by linarith [hu.2, hw.2]⟩
    have hmono : MonotoneOn g (Icc v u) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc v u)
        (fun w hw => (hgd w (hsub hw)).continuousAt.continuousWithinAt)
        (fun w hw => (hgd w (hsub (interior_subset hw))).differentiableAt.differentiableWithinAt)
        (fun w hw => ?_)
      rw [(hgd w (hsub (interior_subset hw))).deriv]
      rw [interior_Icc] at hw
      have := cepe2_f'_mono hv (hsub (interior_subset (s := Icc v u) (by rw [interior_Icc]; exact hw))) hw.1.le
      linarith
    have := hmono ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h.le
    simp only [hg] at this hgv
    linarith

end HRS.MC.CepE2
