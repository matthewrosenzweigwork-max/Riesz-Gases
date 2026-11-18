import HRS.Equilibrium.Parametrix.PXFIDAuxC

/-!
# Packet PX-FID, file D: integrability against `μ` and the vanishing-flux integration by parts
-/

open MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace HRS.Parx.PXFID

variable {d : ℕ} {s : ℝ}

theorem withDensityReal_le_smul' {ρ : Torus d → ℝ} {Λ : ℝ} (hρΛ : ∀ x, ρ x ≤ Λ) :
    withDensityReal ρ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d)) := by
  unfold withDensityReal
  rw [← withDensity_const]
  exact withDensity_mono (Filter.Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (hρΛ x))

theorem integrable_wEnv (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (a : Torus d) :
    Integrable (fun z => wEnv s a z) := by
  refine ⟨(PairCorrAux.measurable_wEnv s a).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z =>
    (zero_le_one.trans (PairCorrAux.one_le_wEnv s a z) : (0 : ℝ) ≤ wEnv s a z))]
  exact lt_of_le_of_lt (PairCorrAux.radial_B0 hd hcrit a) ENNReal.ofReal_lt_top

theorem integrable_wEnv_mu (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {ρ : Torus d → ℝ} {Λ : ℝ}
    (hρΛ : ∀ x, ρ x ≤ Λ) (a : Torus d) : Integrable (fun z => wEnv s z a) (withDensityReal ρ) := by
  have h : (fun z => wEnv s z a) = fun z => wEnv s a z := funext fun z => PairCorrAux.wEnv_symm s z a
  rw [h]
  exact ((integrable_wEnv hd hcrit a).smul_measure ENNReal.ofReal_ne_top).mono_measure
    (withDensityReal_le_smul' hρΛ)

theorem ae_ne_withDensity (hd : 1 ≤ d) (ρ : Torus d → ℝ) (a : Torus d) :
    ∀ᵐ x ∂(withDensityReal ρ), x ≠ a := by
  have h0 : ∀ᵐ x ∂(volume : Measure (Torus d)), x ≠ a := by
    rw [ae_iff]
    have := volume_singleton_torus hd a
    simpa using this
  exact withDensity_absolutelyContinuous _ _ h0

theorem integrable_of_le_wEnv (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {ρ : Torus d → ℝ} {Λ : ℝ}
    (hρΛ : ∀ x, ρ x ≤ Λ) (a : Torus d) {f : Torus d → ℝ}
    (hf : AEStronglyMeasurable f (withDensityReal ρ)) (C : ℝ)
    (hb : ∀ x, x ≠ a → ‖f x‖ ≤ C * wEnv s x a) : Integrable f (withDensityReal ρ) := by
  refine Integrable.mono' ((integrable_wEnv_mu hd hcrit hρΛ a).const_mul C) hf ?_
  filter_upwards [ae_ne_withDensity (by omega) ρ a] with x hx using hb x hx

theorem exists_abs_le_of_smooth {ϕ : Torus d → ℝ} (hϕ : Torus.IsSmooth ϕ) :
    ∃ M : ℝ, ∀ x, |ϕ x| ≤ M := by
  have hc : Continuous ϕ := Torus.continuous_of_continuous_lift
    (show ContDiff ℝ ∞ (Torus.lift ϕ) from hϕ).continuous
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact ⟨C, fun x => by simpa using hC x (Set.mem_univ x)⟩

theorem exists_norm_grad_le_of_smooth {ϕ : Torus d → ℝ} (hϕ : Torus.IsSmooth ϕ) :
    ∃ G : ℝ, ∀ x, ‖Torus.grad ϕ x‖ ≤ G := by
  have h1 : ContDiff ℝ 1 (Torus.lift ϕ) :=
    (show ContDiff ℝ ∞ (Torus.lift ϕ) from hϕ).of_le (by exact_mod_cast le_top)
  obtain ⟨G, hG⟩ := Torus.bddAbove_norm_iteratedFDeriv_lift 1 ϕ h1
  refine ⟨G, fun x => ?_⟩
  have h2 : ‖Torus.grad ϕ x‖ = ‖iteratedFDeriv ℝ 1 (Torus.lift ϕ) (Torus.rep x)‖ := by
    rw [norm_iteratedFDeriv_one]
    unfold Torus.grad gradient
    exact LinearIsometryEquiv.norm_map _ _
  rw [h2]
  exact hG ⟨Torus.rep x, rfl⟩

end HRS.Parx.PXFID

end
