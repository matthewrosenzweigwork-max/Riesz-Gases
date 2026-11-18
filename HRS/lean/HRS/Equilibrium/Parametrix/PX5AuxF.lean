import HRS.Equilibrium.Parametrix.PX5AuxE
import HRS.Equilibrium.Parametrix.PXSAuxGlue

/-!
# Prop 4.13 parametrix, packet PX5: `Bop` is `β⁻¹ M` and a second thermal hypothesis

`Bop d s V β ρ f x = β⁻¹ (Δf + ∇log ρ · ∇f)` (Gibbs relation) so that the hypothesis
`ParxHyp d s V' (β/2) ρ` with `V' = V - β⁻¹ log (Z ρ)` has `Bop' = 2 Bop`.  This lets
`gen_integral_comm` (applied twice) separate the nonlocal part `Jop`.
-/

open MeasureTheory Filter Topology
noncomputable section

namespace HRS.Parx

open HRS.PDE HRS.PDE.MFAux

variable {d : ℕ} {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ}

theorem px5_conv_eq (H : ParxHyp d s V β ρ) :
    convMeasure (periodicRiesz d s) (withDensityReal ρ) = convFun (periodicRiesz d s) ρ := by
  have hρ := H.rho_smooth
  have hρ1 : Torus.IsCk 1 ρ := PDE.MFPair.isCk_of_smooth_ps hρ.smooth 1
  have hρc : Continuous ρ := MFAux.continuous_of_isCk hρ1
  funext z
  unfold convMeasure convFun
  rw [integral_withDensityReal_eq ρ hρc.measurable (fun y => (hρ.pos y).le)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  ring

theorem px5_gibbs (H : ParxHyp d s V β ρ) (j : Fin d) (x : Torus d) :
    Torus.partialDeriv j V x + (forceField d s ρ x) j = -β⁻¹ * (Torus.partialDeriv j ρ x / ρ x) := by
  have hρ := H.rho_smooth
  have hρ1 : Torus.IsCk 1 ρ := PDE.MFPair.isCk_of_smooth_ps hρ.smooth 1
  have hV1 : Torus.IsCk 1 V := PDE.MFPair.isCk_of_smooth_ps H.V_smooth 1
  obtain ⟨-, hdiff⟩ := MFAux.gibbs_partialDeriv V ρ (convFun (periodicRiesz d s) ρ) β H.beta_pos.ne'
    (∫ y, Real.exp (-β * (V y + convFun (periodicRiesz d s) ρ y))) hρ1 hV1 hρ.pos H.thermal.2
  unfold forceField
  rw [px5_conv_eq H, MFAux.grad_apply, hdiff j x]
  ring

theorem px5_Bop_form (H : ParxHyp d s V β ρ) (f : Torus d → ℝ) (x : Torus d) :
    Bop d s V β ρ f x = β⁻¹ * (Torus.laplacian f x +
      ∑ j, (Torus.partialDeriv j ρ x / ρ x) * Torus.partialDeriv j f x) := by
  unfold Bop
  rw [PiLp.inner_apply]
  have e : ∀ i, inner ℝ ((Torus.grad V x + forceField d s ρ x).ofLp i) ((Torus.grad f x).ofLp i) =
      -β⁻¹ * (Torus.partialDeriv i ρ x / ρ x) * Torus.partialDeriv i f x := by
    intro i
    rw [real_inner_eq_re_inner, ← px5_gibbs H i x] 
    simp [MFAux.grad_apply]
    ring
  simp_rw [e]
  rw [mul_add, Finset.mul_sum]
  have : ∑ i, -β⁻¹ * (Torus.partialDeriv i ρ x / ρ x) * Torus.partialDeriv i f x =
      -∑ i, β⁻¹ * ((Torus.partialDeriv i ρ x / ρ x) * Torus.partialDeriv i f x) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]; ring


theorem px5_scaled_hyp (H : ParxHyp d s V β ρ) :
    ∃ V' : Torus d → ℝ, ∃ H' : ParxHyp d s V' (β / 2) ρ,
      ∀ (f : Torus d → ℝ) (x : Torus d), Bop d s V' (β / 2) ρ f x = 2 * Bop d s V β ρ f x := by
  have hρ := H.rho_smooth
  have hβ : β ≠ 0 := H.beta_pos.ne'
  set G : Torus d → ℝ := convFun (periodicRiesz d s) ρ with hG
  set Z : ℝ := ∫ y, Real.exp (-β * (V y + G y)) with hZdef
  have ht : ∀ x, ρ x = Real.exp (-β * (V x + G x)) / Z := H.thermal.2
  have hZ : 0 < Z := by
    have h1 := ht 0
    have h2 := hρ.pos 0
    have h3 := Real.exp_pos (-β * (V 0 + G 0))
    rcases lt_trichotomy Z 0 with h | h | h
    · exfalso
      have : Real.exp (-β * (V 0 + G 0)) / Z < 0 := div_neg_of_pos_of_neg h3 h
      linarith
    · rw [h, div_zero] at h1; linarith
    · exact h
  have hlog : ∀ x, Real.log (Z * ρ x) = -β * (V x + G x) := by
    intro x
    have h1 : Z * ρ x = Real.exp (-β * (V x + G x)) := by
      rw [ht x]; field_simp
    rw [h1, Real.log_exp]
  set V' : Torus d → ℝ := fun x => V x - β⁻¹ * Real.log (Z * ρ x) with hV'
  have hVs : Torus.IsSmooth V' := by
    unfold Torus.IsSmooth Torus.IsCk
    have hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift V) := H.V_smooth
    have hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift ρ) := hρ.smooth
    have e : Torus.lift V' = fun w => Torus.lift V w - β⁻¹ * Real.log (Z * Torus.lift ρ w) := rfl
    rw [e]
    refine hV.sub (contDiff_const.mul (ContDiff.log (contDiff_const.mul hr) fun w => ?_))
    exact (mul_pos hZ (hρ.pos _)).ne'
  have key : ∀ y, -(β / 2) * (V' y + G y) = Real.log (Z * ρ y) := by
    intro y
    have := hlog y
    simp only [hV']
    field_simp
    linarith
  have hexp : ∀ y, Real.exp (-(β / 2) * (V' y + G y)) = Z * ρ y := by
    intro y
    rw [key y, Real.exp_log (mul_pos hZ (hρ.pos y))]
  have hZ' : ∫ y, Real.exp (-(β / 2) * (V' y + G y)) = Z := by
    simp_rw [hexp]
    rw [integral_const_mul, hρ.density.integral_one, mul_one]
  have hH' : ParxHyp d s V' (β / 2) ρ :=
    { two_le := H.two_le
      crit := H.crit
      beta_pos := half_pos H.beta_pos
      V_smooth := hVs
      thermal := ⟨H.thermal.1, fun x => by
        show ρ x = Real.exp (-(β / 2) * (V' x + G x)) / ∫ y, Real.exp (-(β / 2) * (V' y + G y))
        rw [hZ', hexp]
        field_simp⟩
      rho_smooth := hρ }
  refine ⟨V', hH', fun f x => ?_⟩
  rw [px5_Bop_form hH', px5_Bop_form H]
  have : (β / 2)⁻¹ = 2 * β⁻¹ := by field_simp
  rw [this]; ring

end HRS.Parx

end
