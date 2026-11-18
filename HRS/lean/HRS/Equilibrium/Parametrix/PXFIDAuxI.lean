import HRS.Equilibrium.Parametrix.PXFIDAuxH

/-!
# Packet PX-FID, file I: the Gibbs force relation and the product integrability of the envelope
-/

open MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace HRS.Parx.PXFID

variable {d : ℕ} {s : ℝ}

/-- The force relation `ρ (∇V + F_μ) = -β⁻¹ ∇ρ` of a thermal density. -/
theorem force_relation (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {V ρ : Torus d → ℝ} (hV : Torus.IsSmooth V) (hρ : IsThermalDensity (periodicRiesz d s) V β ρ)
    (hρs : SmoothPosDensity ρ) (x : Torus d) :
    ρ x • (Torus.grad V x + forceField d s ρ x) = -β⁻¹ • Torus.grad ρ x := by
  have hρ1 : Torus.IsCk 1 ρ :=
    (show ContDiff ℝ ∞ (Torus.lift ρ) from hρs.smooth).of_le (by exact_mod_cast le_top)
  have hV1 : Torus.IsCk 1 V :=
    (show ContDiff ℝ ∞ (Torus.lift V) from hV).of_le (by exact_mod_cast le_top)
  have hρc : Continuous ρ := PDE.MFAux.continuous_of_isCk hρ1
  obtain ⟨-, hdiff⟩ := PDE.MFAux.gibbs_partialDeriv V ρ (convFun (periodicRiesz d s) ρ) β hβ.ne'
    (∫ y, Real.exp (-β * (V y + convFun (periodicRiesz d s) ρ y))) hρ1 hV1 hρs.pos hρ.2
  have hconv : convMeasure (periodicRiesz d s) (withDensityReal ρ) = convFun (periodicRiesz d s) ρ := by
    funext z
    unfold convMeasure convFun
    rw [integral_withDensityReal_eq ρ hρc.measurable (fun y => (hρs.pos y).le)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    ring
  have hpos := hρs.pos x
  ext j
  simp only [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
  have e1 : (forceField d s ρ x) j = Torus.partialDeriv j (convFun (periodicRiesz d s) ρ) x := by
    unfold forceField
    rw [hconv, PDE.MFAux.grad_apply]
  rw [e1, PDE.MFAux.grad_apply, PDE.MFAux.grad_apply, hdiff j x]
  field_simp
  ring

theorem exists_force_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {V ρ : Torus d → ℝ} (hV : Torus.IsSmooth V) (hρ : IsThermalDensity (periodicRiesz d s) V β ρ)
    (hρs : SmoothPosDensity ρ) :
    ∃ M : ℝ, ∀ x, ‖Torus.grad V x + forceField d s ρ x‖ ≤ M := by
  obtain ⟨G, hG⟩ := exists_norm_grad_le_of_smooth hρs.smooth
  have hρc : Continuous ρ := Torus.continuous_of_continuous_lift
    (show ContDiff ℝ ∞ (Torus.lift ρ) from hρs.smooth).continuous
  have hic : Continuous fun x => (ρ x)⁻¹ := hρc.inv₀ fun x => (hρs.pos x).ne'
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hic.continuousOn
  refine ⟨β⁻¹ * G * C, fun x => ?_⟩
  have h := force_relation hd hs0 hsd hβ hV hρ hρs x
  have hpos := hρs.pos x
  have h2 : Torus.grad V x + forceField d s ρ x = (-β⁻¹ * (ρ x)⁻¹) • Torus.grad ρ x := by
    have : Torus.grad V x + forceField d s ρ x = (ρ x)⁻¹ • (ρ x • (Torus.grad V x + forceField d s ρ x)) := by
      rw [smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
    rw [this, h, smul_smul]
    congr 1
    ring
  rw [h2, norm_smul, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (inv_pos.2 hβ),
    abs_of_pos (inv_pos.2 hpos)]
  have hC' : (ρ x)⁻¹ ≤ C := by
    have := hC x (Set.mem_univ x)
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos)] at this
    exact this
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG x)
  calc β⁻¹ * (ρ x)⁻¹ * ‖Torus.grad ρ x‖ ≤ β⁻¹ * C * G :=
        mul_le_mul (mul_le_mul_of_nonneg_left hC' (inv_pos.2 hβ).le) (hG x) (norm_nonneg _)
          (mul_nonneg (inv_pos.2 hβ).le ((inv_pos.2 hpos).le.trans hC'))
    _ = β⁻¹ * G * C := by ring

end HRS.Parx.PXFID

end
