import HRS.PDE.TorusFPLpGlue5

/-!
# D3PHIP, helper 1: torus calculus for powers, and the fixed-time Green identity of packet A

Relocated helpers (prefix `d3pp_`) for `d3phi_identity_classical`.  Fixed time: `w, ψ ∈ C²`, `w > 0`, `Zc > 0`,
`u = w Zc e^{-ψ}`, `a = ∇ log w - ∇ψ`; then for every real `s`
`s ∫ u^{s-1} L w dP = -s(s-1) κ ∫ u^{s-1} w ‖a‖² dP + (s-1) ∫ u^{s-1} w (Lψ + κ‖∇ψ‖²) dP`
(two applications of the weighted Green identity `d3a_green_P`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

theorem d3pp_lift_ck {k : WithTop ℕ∞} {f : Torus n → ℝ} (hf : Torus.IsCk k f) :
    ContDiff ℝ k (Torus.lift f) := hf

theorem d3pp_pd_lincomb {f g : Torus n → ℝ} (hf : Torus.IsCk 1 f) (hg : Torus.IsCk 1 g) (a b c : ℝ)
    (j : Fin n) (x : Torus n) :
    Torus.partialDeriv j (fun y => a * f y + b * g y + c) x =
      a * Torus.partialDeriv j f x + b * Torus.partialDeriv j g x := by
  have e1 : Torus.lift (fun y => a * f y + b * g y + c) =
      fun y => a * Torus.lift f y + b * Torus.lift g y + c := rfl
  have h1 := (hf.differentiable one_ne_zero) (Torus.rep x)
  have h2 := (hg.differentiable one_ne_zero) (Torus.rep x)
  have h0 : HasFDerivAt (fun y => a * Torus.lift f y + b * Torus.lift g y + c)
      (a • fderiv ℝ (Torus.lift f) (Torus.rep x) + b • fderiv ℝ (Torus.lift g) (Torus.rep x))
      (Torus.rep x) :=
    ((h1.hasFDerivAt.const_mul a).add (h2.hasFDerivAt.const_mul b)).add_const c
  simp only [Torus.partialDeriv]
  rw [e1, h0.fderiv]
  simp

theorem d3pp_pd_rpow {f : Torus n → ℝ} (hf : Torus.IsCk 1 f) (hpos : ∀ x, 0 < f x) (a : ℝ)
    (j : Fin n) (x : Torus n) :
    Torus.partialDeriv j (fun y => f y ^ a) x =
      a * f x ^ (a - 1) * Torus.partialDeriv j f x := by
  have e1 : Torus.lift (fun y => f y ^ a) = fun y => Torus.lift f y ^ a := rfl
  have h1 := (hf.differentiable one_ne_zero) (Torus.rep x)
  have hne : Torus.lift f (Torus.rep x) ≠ 0 := by
    simp only [Torus.lift, Function.comp_apply, Torus.mk_rep]
    exact (hpos x).ne'
  have h0 := h1.hasFDerivAt.rpow_const (p := a) (Or.inl hne)
  simp only [Torus.partialDeriv]
  rw [e1, h0.fderiv]
  simp [Torus.lift, Torus.mk_rep]

theorem d3pp_isCk_rpow {k : WithTop ℕ∞} {f : Torus n → ℝ} (hf : Torus.IsCk k f) (hpos : ∀ x, 0 < f x)
    (a : ℝ) : Torus.IsCk k (fun y => f y ^ a) := by
  unfold Torus.IsCk
  have e1 : Torus.lift (fun y => f y ^ a) = fun y => Torus.lift f y ^ a := rfl
  rw [e1]
  exact ContDiff.rpow_const_of_ne hf (fun y => (hpos _).ne')

theorem d3pp_isCk_mul {k : WithTop ℕ∞} {f g : Torus n → ℝ} (hf : Torus.IsCk k f) (hg : Torus.IsCk k g) :
    Torus.IsCk k (fun y => f y * g y) := by
  unfold Torus.IsCk
  have e1 : Torus.lift (fun y => f y * g y) = fun y => Torus.lift f y * Torus.lift g y := rfl
  rw [e1]
  exact hf.mul hg

theorem d3pp_isCk_u {k : WithTop ℕ∞} {w ψ : Torus n → ℝ} (hw : Torus.IsCk k w) (hψ : Torus.IsCk k ψ)
    (Zc : ℝ) : Torus.IsCk k (fun y => w y * Zc * Real.exp (-ψ y)) := by
  unfold Torus.IsCk
  have e1 : Torus.lift (fun y => w y * Zc * Real.exp (-ψ y)) =
      fun y => Torus.lift w y * Zc * Real.exp (-Torus.lift ψ y) := rfl
  rw [e1]
  exact (hw.mul contDiff_const).mul (Real.contDiff_exp.comp hψ.neg)

/-- `∇ log u = ∇ log w - ∇ ψ` for `u = w Zc e^{-ψ}`. -/
theorem d3pp_grad_log_u {w ψ : Torus n → ℝ} (hw : Torus.IsCk 1 w) (hwpos : ∀ x, 0 < w x)
    (hψ : Torus.IsCk 1 ψ) {Zc : ℝ} (hZ : 0 < Zc) (x : Torus n) :
    Torus.grad (fun y => Real.log (w y * Zc * Real.exp (-ψ y))) x =
      Torus.grad (fun y => Real.log (w y)) x - Torus.grad ψ x := by
  have e : (fun y => Real.log (w y * Zc * Real.exp (-ψ y))) =
      fun y => 1 * Real.log (w y) + (-1) * ψ y + Real.log Zc := by
    funext y
    rw [Real.log_mul (mul_pos (hwpos y) hZ).ne' (Real.exp_pos _).ne', Real.log_mul (hwpos y).ne' hZ.ne',
      Real.log_exp]
    ring
  have hlog : Torus.IsCk 1 (fun y => Real.log (w y)) := d3a_isCk_log hw hwpos
  ext j
  rw [d1c_grad_component, e, d3pp_pd_lincomb hlog hψ, PiLp.sub_apply, d1c_grad_component,
    d1c_grad_component]
  ring

/-- `∇ (f^a) = (a f^a) ∇ log f`. -/
theorem d3pp_grad_rpow {f : Torus n → ℝ} (hf : Torus.IsCk 1 f) (hpos : ∀ x, 0 < f x) (a : ℝ)
    (x : Torus n) :
    Torus.grad (fun y => f y ^ a) x = (a * f x ^ a) • Torus.grad (fun y => Real.log (f y)) x := by
  ext j
  rw [d1c_grad_component, d3pp_pd_rpow hf hpos, d3a_grad_log hf hpos]
  simp only [PiLp.smul_apply, d1c_grad_component]
  have h1 : f x ^ (a - 1) = f x ^ a / f x := by
    rw [Real.rpow_sub (hpos x), Real.rpow_one]
  rw [h1]
  have := (hpos x).ne'
  simp only [smul_eq_mul, div_eq_inv_mul]
  field_simp

/-- Product rule for the gradient. -/
theorem d3pp_grad_mul {f g : Torus n → ℝ} (hf : Torus.IsCk 1 f) (hg : Torus.IsCk 1 g) (x : Torus n) :
    Torus.grad (fun y => f y * g y) x = f x • Torus.grad g x + g x • Torus.grad f x := by
  ext j
  rw [d1c_grad_component, d3a_pd_mul hf hg, PiLp.add_apply, PiLp.smul_apply, PiLp.smul_apply,
    d1c_grad_component, d1c_grad_component]
  simp only [smul_eq_mul]
  ring

end HRS
