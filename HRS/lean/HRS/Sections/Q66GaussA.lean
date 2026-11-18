import Mathlib

/-!
# Packet Q66: Gaussian integration by parts (one dimension and product measures)
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Q66

theorem q66_gpdf_deriv (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h1 : HasDerivAt (fun x : ℝ => -(x - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) (-x) x := by
    have := ((hasDerivAt_id x).sub_const 0).pow 2
    simp only [Nat.cast_ofNat, id_eq] at this
    have h2 := (this.neg).div_const (2 * ((1 : ℝ≥0) : ℝ))
    convert h2 using 1
    simp; ring
  have h3 := h1.exp.const_mul ((√(2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹)
  simp only [gaussianPDFReal_def]
  convert h3 using 1
  simp [gaussianPDFReal]; ring

theorem q66_integral_gauss_eq (f : ℝ → ℝ) :
    ∫ x, f x ∂(gaussianReal 0 1) = ∫ x, gaussianPDFReal 0 1 x * f x := by
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero]; rfl

theorem q66_integrable_gauss_iff (f : ℝ → ℝ) :
    Integrable f (gaussianReal 0 1) ↔ Integrable (fun x => gaussianPDFReal 0 1 x * f x) := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (Eventually.of_forall fun x => gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF, smul_eq_mul]

/-- One-dimensional Gaussian integration by parts `E[ξ h(ξ)] = E[h'(ξ)]`. -/
theorem q66_gauss1d_ibp {h h' : ℝ → ℝ} (hd : ∀ x, HasDerivAt h (h' x) x)
    (i1 : Integrable (fun x => x * h x) (gaussianReal 0 1))
    (i2 : Integrable h' (gaussianReal 0 1)) (i3 : Integrable h (gaussianReal 0 1)) :
    ∫ x, x * h x ∂(gaussianReal 0 1) = ∫ x, h' x ∂(gaussianReal 0 1) := by
  set p : ℝ → ℝ := gaussianPDFReal 0 1 with hp
  rw [q66_integral_gauss_eq, q66_integral_gauss_eq]
  have j1 := (q66_integrable_gauss_iff _).1 i1
  have j2 := (q66_integrable_gauss_iff _).1 i2
  have j3 := (q66_integrable_gauss_iff _).1 i3
  have := integral_mul_deriv_eq_deriv_mul_of_integrable (A := ℝ) (u := h) (u' := h') (v := p)
    (v' := fun x => -x * p x) (fun x _ => hd x) (fun x _ => q66_gpdf_deriv x)
    (by refine j1.neg.congr (Eventually.of_forall fun x => ?_); simp only [Pi.mul_apply, Pi.neg_apply]; ring)
    (by refine j2.congr (Eventually.of_forall fun x => ?_); simp only [Pi.mul_apply]; ring)
    (by refine j3.congr (Eventually.of_forall fun x => ?_); simp only [Pi.mul_apply]; ring)
  have e1 : ∫ x, p x * (x * h x) = -∫ x, h x * (-x * p x) := by
    rw [← integral_neg]; refine integral_congr_ae (Eventually.of_forall fun x => ?_); ring
  have e2 : ∫ x, p x * h' x = -∫ x, h x * (-x * p x) := by
    rw [this, neg_neg]; refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply]; ring
  exact e1.trans e2.symm

/-- Coordinate-wise Gaussian integration by parts on the product space `ℝ^{m+1}`. -/
theorem q66_gaussN_ibp {m : ℕ} (j : Fin (m + 1)) {H dH : (Fin (m + 1) → ℝ) → ℝ}
    (hd : ∀ (η' : Fin m → ℝ) (t : ℝ), HasDerivAt (fun t : ℝ => H (Fin.insertNth j t η'))
      (dH (Fin.insertNth j t η')) t)
    (hHm : Measurable H) (hdHm : Measurable dH)
    (i1 : Integrable (fun η : Fin (m + 1) → ℝ => η j * H η) (Measure.pi fun _ => gaussianReal 0 1))
    (i2 : Integrable dH (Measure.pi fun _ => gaussianReal 0 1))
    (i3 : Integrable H (Measure.pi fun _ => gaussianReal 0 1)) :
    ∫ η, η j * H η ∂(Measure.pi fun _ : Fin (m + 1) => gaussianReal 0 1) =
      ∫ η, dH η ∂(Measure.pi fun _ : Fin (m + 1) => gaussianReal 0 1) := by
  set γ : Measure ℝ := gaussianReal 0 1 with hγ
  set π : Measure (Fin (m + 1) → ℝ) := Measure.pi fun _ => γ with hπ
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => γ) j).symm
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) j with he
  have hsymm : ∀ p : ℝ × (Fin m → ℝ), e.symm p = Fin.insertNth j p.1 p.2 := fun p => rfl
  have hcomp : ∀ F : (Fin (m + 1) → ℝ) → ℝ, ∫ η, F η ∂π =
      ∫ p, F (Fin.insertNth j p.1 p.2) ∂(γ.prod (Measure.pi fun i : Fin m => γ)) := by
    intro F
    have := hmp.integral_comp' F
    simp only [hsymm] at this
    rw [← this]
  have hint : ∀ F : (Fin (m + 1) → ℝ) → ℝ, Integrable F π →
      Integrable (fun p : ℝ × (Fin m → ℝ) => F (Fin.insertNth j p.1 p.2))
        (γ.prod (Measure.pi fun i : Fin m => γ)) := by
    intro F hF
    have := (hmp.integrable_comp_of_integrable hF)
    have e2 : (fun p : ℝ × (Fin m → ℝ) => F (Fin.insertNth j p.1 p.2)) = F ∘ e.symm := by
      funext p; exact (congrArg F (hsymm p)).symm
    rw [e2]; exact this
  rw [hcomp (fun η => η j * H η), hcomp dH]
  have I1 := hint _ i1
  have I2 := hint _ i2
  have I3 := hint _ i3
  simp only [Fin.insertNth_apply_same] at I1 ⊢
  rw [integral_prod_symm _ I1, integral_prod_symm _ I2]
  refine integral_congr_ae ?_
  filter_upwards [I1.prod_left_ae, I2.prod_left_ae, I3.prod_left_ae] with η' h1 h2 h3
  exact q66_gauss1d_ibp (h := fun t => H (Fin.insertNth j t η'))
    (h' := fun t => dH (Fin.insertNth j t η')) (fun t => hd η' t) h1 h2 h3

end HRS.Q66

end
