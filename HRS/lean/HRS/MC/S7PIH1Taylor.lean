import HRS.MC.S7PIS3Heat

/-!
# Packet piH, part 1: second order Taylor estimate with modulus of `D²` (pure calculus)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIH

section Taylor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Second order Taylor estimate for a `C²` function, in terms of the oscillation of `D²H` on the
segment `[c, c + k]`. -/
theorem S7PIH_taylor2 {H : E → ℝ} (hH : ContDiff ℝ 2 H) (c k : E) {m : ℝ}
    (hm : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ 2 H (c + θ • k) - iteratedFDeriv ℝ 2 H c‖ ≤ m) :
    |H (c + k) - H c - fderiv ℝ H c k - (1 / 2) * iteratedFDeriv ℝ 2 H c ![k, k]|
      ≤ m * ‖k‖ ^ 2 := by
  have hline : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => c + θ • k) k θ := fun θ => by
    simpa using ((hasDerivAt_id θ).smul_const k).const_add c
  have hd1 : Differentiable ℝ H := hH.differentiable (by norm_num)
  have hfd : ContDiff ℝ 1 (fderiv ℝ H) := hH.fderiv_right (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ H) := hfd.differentiable (by norm_num)
  have hg1 : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => H (c + θ • k)) (fderiv ℝ H (c + θ • k) k) θ :=
    fun θ => (hd1 (c + θ • k)).hasFDerivAt.comp_hasDerivAt θ (hline θ)
  have hg2 : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => fderiv ℝ H (c + θ • k) k)
      (iteratedFDeriv ℝ 2 H (c + θ • k) ![k, k]) θ := fun θ => by
    have h1 : HasDerivAt (fun θ : ℝ => fderiv ℝ H (c + θ • k))
        (fderiv ℝ (fderiv ℝ H) (c + θ • k) k) θ :=
      (hd2 (c + θ • k)).hasFDerivAt.comp_hasDerivAt θ (hline θ)
    have h2 := h1.clm_apply (hasDerivAt_const θ k)
    simpa [iteratedFDeriv_two_apply] using h2
  set D2c : ℝ := iteratedFDeriv ℝ 2 H c ![k, k] with hD2c
  set p : ℝ → ℝ := fun θ => fderiv ℝ H (c + θ • k) k - fderiv ℝ H c k - θ * D2c with hp
  have hp' : ∀ θ, HasDerivAt p (iteratedFDeriv ℝ 2 H (c + θ • k) ![k, k] - D2c) θ := fun θ => by
    have := ((hg2 θ).sub_const (fderiv ℝ H c k)).sub ((hasDerivAt_id θ).mul_const D2c)
    convert this using 1
    · funext x; simp [hp]
    · simp
  have hbound : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ 2 H (c + θ • k) ![k, k] - D2c‖ ≤ m * ‖k‖ ^ 2 := by
    intro θ hθ
    have h := hm θ hθ
    have e : iteratedFDeriv ℝ 2 H (c + θ • k) ![k, k] - D2c =
        (iteratedFDeriv ℝ 2 H (c + θ • k) - iteratedFDeriv ℝ 2 H c) ![k, k] := by
      simp [hD2c]
    rw [Real.norm_eq_abs] at *
    rw [e]
    refine ((iteratedFDeriv ℝ 2 H (c + θ • k) - iteratedFDeriv ℝ 2 H c).le_opNorm _).trans ?_
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith [norm_nonneg k, mul_nonneg (norm_nonneg k) (norm_nonneg k), norm_nonneg
      (iteratedFDeriv ℝ 2 H (c + θ • k) - iteratedFDeriv ℝ 2 H c)]
  have hpb : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖p θ‖ ≤ m * ‖k‖ ^ 2 := by
    intro θ hθ
    have h0 : p 0 = 0 := by simp [hp]
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := p) (s := Set.Icc (0 : ℝ) 1)
      (x := 0) (y := θ) (C := m * ‖k‖ ^ 2)
      (fun x _ => (hp' x).differentiableAt)
      (fun x hx => by rw [(hp' x).deriv]; exact hbound x hx)
      (convex_Icc 0 1) (by simp) hθ
    rw [h0, sub_zero] at this
    refine this.trans ?_
    have : ‖θ - 0‖ ≤ 1 := by
      rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hθ.1]; exact hθ.2
    have hmk : 0 ≤ m * ‖k‖ ^ 2 := by
      have := hbound 0 (by simp)
      exact (norm_nonneg _).trans this
    nlinarith
  set h : ℝ → ℝ := fun θ => H (c + θ • k) - H c - θ * fderiv ℝ H c k - θ ^ 2 / 2 * D2c with hh
  have hh' : ∀ θ, HasDerivAt h (p θ) θ := fun θ => by
    have := (((hg1 θ).sub_const (H c)).sub ((hasDerivAt_id θ).mul_const (fderiv ℝ H c k))).sub
      (((hasDerivAt_pow 2 θ).div_const 2).mul_const D2c)
    convert this using 1
    · funext x; simp [hh]
    · simp only [hp]; ring
  have key := Convex.norm_image_sub_le_of_norm_deriv_le (f := h) (s := Set.Icc (0 : ℝ) 1)
    (x := 0) (y := 1) (C := m * ‖k‖ ^ 2)
    (fun x _ => (hh' x).differentiableAt)
    (fun x hx => by rw [(hh' x).deriv]; exact hpb x hx)
    (convex_Icc 0 1) (by simp) (by simp)
  have h0 : h 0 = 0 := by simp [hh]
  have h1 : h 1 = H (c + k) - H c - fderiv ℝ H c k - (1 / 2) * D2c := by
    simp only [hh, one_smul, one_mul, one_pow]
  rw [h0, h1, sub_zero] at key
  simpa [Real.norm_eq_abs] using key

end Taylor

end HRS.MC.Sec7.S7PIH

end
