import HRS.MC.CepaDefs

/-!
# Packet CEPH3, part A1: the one-dimensional kernel `h(u) = -log(2 sin(π u))` on `(0,1)`

Convexity, derivative and tangent inequality.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH3

/-- The pair kernel `h(u) = -log(2 sin(π u))`. -/
def h3a_h (u : ℝ) : ℝ := -Real.log (2 * Real.sin (Real.pi * u))

/-- Its derivative `h'(u) = -π cos(π u) / sin(π u)`. -/
def h3a_dh (u : ℝ) : ℝ := -(Real.pi * Real.cos (Real.pi * u) / Real.sin (Real.pi * u))

lemma h3a_sin_pos {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : 0 < Real.sin (Real.pi * u) :=
  Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hu.1) (by nlinarith [Real.pi_pos, hu.2])

lemma h3a_hasDerivAt {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : HasDerivAt h3a_h (h3a_dh u) u := by
  have hs := h3a_sin_pos hu
  have h1 : HasDerivAt (fun u : ℝ => 2 * Real.sin (Real.pi * u)) (2 * (Real.cos (Real.pi * u) * Real.pi)) u := by
    have := ((Real.hasDerivAt_sin (Real.pi * u)).comp u ((hasDerivAt_id u).const_mul Real.pi))
    simpa using this.const_mul 2
  have h2 : HasDerivAt (fun u : ℝ => -Real.log (2 * Real.sin (Real.pi * u)))
      (-((2 * (Real.cos (Real.pi * u) * Real.pi)) / (2 * Real.sin (Real.pi * u)))) u :=
    (h1.log (by positivity)).neg
  have h3 : h3a_dh u = -((2 * (Real.cos (Real.pi * u) * Real.pi)) / (2 * Real.sin (Real.pi * u))) := by
    unfold h3a_dh
    field_simp
  rw [h3]
  exact h2

lemma h3a_convexOn : ConvexOn ℝ (Ioo (0 : ℝ) 1) h3a_h := by
  refine ⟨convex_Ioo 0 1, fun u hu v hv a b ha hb hab => ?_⟩
  have hsu := h3a_sin_pos hu
  have hsv := h3a_sin_pos hv
  have hcon : a * Real.sin (Real.pi * u) + b * Real.sin (Real.pi * v) ≤
      Real.sin (Real.pi * (a * u + b * v)) := by
    have := (strictConcaveOn_sin_Icc.concaveOn).2 (x := Real.pi * u) (y := Real.pi * v)
      ⟨by nlinarith [Real.pi_pos, hu.1], by nlinarith [Real.pi_pos, hu.2]⟩
      ⟨by nlinarith [Real.pi_pos, hv.1], by nlinarith [Real.pi_pos, hv.2]⟩ ha hb hab
    simp only [smul_eq_mul] at this
    have e : Real.pi * (a * u + b * v) = a * (Real.pi * u) + b * (Real.pi * v) := by ring
    rw [e]; exact this
  have hpos : 0 < a * (2 * Real.sin (Real.pi * u)) + b * (2 * Real.sin (Real.pi * v)) := by
    rcases ha.eq_or_lt with h | h
    · subst h
      have : b = 1 := by linarith
      subst this; simp; positivity
    · have : 0 ≤ b * (2 * Real.sin (Real.pi * v)) := by positivity
      have : 0 < a * (2 * Real.sin (Real.pi * u)) := by positivity
      linarith
  have hlog := strictConcaveOn_log_Ioi.concaveOn.2 (x := 2 * Real.sin (Real.pi * u))
    (y := 2 * Real.sin (Real.pi * v)) (by simp only [mem_Ioi]; positivity)
    (by simp only [mem_Ioi]; positivity) ha hb hab
  simp only [smul_eq_mul] at hlog
  have hmono : Real.log (a * (2 * Real.sin (Real.pi * u)) + b * (2 * Real.sin (Real.pi * v))) ≤
      Real.log (2 * Real.sin (Real.pi * (a * u + b * v))) :=
    Real.log_le_log hpos (by linarith)
  simp only [h3a_h, smul_eq_mul]
  linarith

/-- Tangent inequality for the convex kernel on `(0,1)`. -/
lemma h3a_tangent {u v : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Ioo (0 : ℝ) 1) :
    h3a_h u + h3a_dh u * (v - u) ≤ h3a_h v := by
  rcases lt_trichotomy u v with h | h | h
  · have := h3a_convexOn.le_slope_of_hasDerivAt hu hv h (h3a_hasDerivAt hu)
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    linarith
  · subst h; simp
  · have := h3a_convexOn.slope_le_of_hasDerivAt hv hu h (h3a_hasDerivAt hu)
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith

/-- Monotonicity of the derivative of the kernel. -/
lemma h3a_dh_mono : MonotoneOn h3a_dh (Ioo (0 : ℝ) 1) := by
  have := h3a_convexOn.monotoneOn_deriv (fun x hx => (h3a_hasDerivAt hx).differentiableAt)
  intro x hx y hy hxy
  have h := this hx hy hxy
  rwa [(h3a_hasDerivAt hx).deriv, (h3a_hasDerivAt hy).deriv] at h

lemma h3a_dh_continuousAt {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) : ContinuousAt h3a_dh u := by
  have hs := h3a_sin_pos hu
  unfold h3a_dh
  refine ContinuousAt.neg (ContinuousAt.div ?_ ?_ hs.ne')
  · fun_prop
  · fun_prop

end HRS.MC.CepH3
