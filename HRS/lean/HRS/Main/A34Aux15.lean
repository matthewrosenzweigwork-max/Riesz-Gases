import HRS.Main.A34Aux14

/-!
# Packet A34, helper 15: the isometry `L²(ρ dμ₀; ℝ^d) → L²(μ₀; ℝ^d)`, `f ↦ √ρ f`, and transfer of
isonormal processes
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A34

open HRS HRS.PDE HRS.PDE.ET HRS.A33 HRS.Main

variable {d : ℕ}

section Phi

variable {T : ℝ} {ρ : ℝ → Torus d → ℝ}

theorem a34_nu_ae (hρ : A33Rho T ρ) {P : ℝ × Torus d → Prop} :
    (∀ᵐ p ∂(a33_nu d T ρ), P p) ↔ ∀ᵐ p ∂(a33_mu0 d T), 0 < ρ p.1 p.2 → P p := by
  unfold a33_nu
  rw [ae_withDensity_iff' hρ.aemeasurable.ennreal_ofReal]
  refine Filter.eventually_congr (Eventually.of_forall fun p => ?_)
  simp [ENNReal.ofReal_eq_zero, not_le]

theorem a34_sq_sqrt_eq (x : ℝ) : Real.sqrt x ^ 2 = ((x.toNNReal : ℝ≥0) : ℝ) := by
  by_cases hx : 0 ≤ x
  · rw [Real.sq_sqrt hx, Real.coe_toNNReal _ hx]
  · have : Real.sqrt x = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
    rw [this, Real.toNNReal_of_nonpos (by linarith)]
    simp

theorem a34_Phi_memLp (hρ : A33Rho T ρ) (f : Lp (Euc d) 2 (a33_nu d T ρ)) :
    MemLp (fun p : ℝ × Torus d => Real.sqrt (ρ p.1 p.2) • (f : ℝ × Torus d → Euc d) p) 2
      (a33_mu0 d T) := by
  set f' := (Lp.aestronglyMeasurable f).mk f with hf'
  have hfae : (f : ℝ × Torus d → Euc d) =ᵐ[a33_nu d T ρ] f' := (Lp.aestronglyMeasurable f).ae_eq_mk
  have hfae' : ∀ᵐ p ∂(a33_mu0 d T), 0 < ρ p.1 p.2 → (f : ℝ × Torus d → Euc d) p = f' p :=
    (a34_nu_ae hρ).1 hfae
  have hae : (fun p : ℝ × Torus d => Real.sqrt (ρ p.1 p.2) • (f : ℝ × Torus d → Euc d) p) =ᵐ[a33_mu0 d T]
      fun p => Real.sqrt (ρ p.1 p.2) • f' p := by
    filter_upwards [hfae'] with p hp
    by_cases h : 0 < ρ p.1 p.2
    · simp only [hp h]
    · have : Real.sqrt (ρ p.1 p.2) = 0 := Real.sqrt_eq_zero_of_nonpos (not_lt.1 h)
      simp [this]
  have hm : AEStronglyMeasurable (fun p : ℝ × Torus d => Real.sqrt (ρ p.1 p.2) • (f : ℝ × Torus d → Euc d) p)
      (a33_mu0 d T) := by
    refine AEStronglyMeasurable.congr ?_ hae.symm
    exact (hρ.aemeasurable.sqrt.aestronglyMeasurable).smul (Lp.aestronglyMeasurable f).stronglyMeasurable_mk.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hm]
  have hI : Integrable (fun p => ‖(f : ℝ × Torus d → Euc d) p‖ ^ 2) (a33_nu d T ρ) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).1 (Lp.memLp f)
  have hI' : Integrable (fun p => (ρ p.1 p.2).toNNReal • ‖(f : ℝ × Torus d → Euc d) p‖ ^ 2)
      (a33_mu0 d T) := by
    have := (integrable_withDensity_iff_integrable_smul₀ (μ := a33_mu0 d T)
      (f := fun p : ℝ × Torus d => (ρ p.1 p.2).toNNReal) hρ.aemeasurable.real_toNNReal
      (g := fun p => ‖(f : ℝ × Torus d → Euc d) p‖ ^ 2)).1
    exact this hI
  refine hI'.congr (Eventually.of_forall fun p => ?_)
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, NNReal.smul_def, smul_eq_mul]
  rw [a34_sq_sqrt_eq]

theorem a34_smul_ae (hρ : A33Rho T ρ) {f g : ℝ × Torus d → Euc d}
    (h : f =ᵐ[a33_nu d T ρ] g) :
    (fun p : ℝ × Torus d => Real.sqrt (ρ p.1 p.2) • f p) =ᵐ[a33_mu0 d T]
      fun p => Real.sqrt (ρ p.1 p.2) • g p := by
  have h' := (a34_nu_ae hρ).1 h
  filter_upwards [h'] with p hp
  by_cases hq : 0 < ρ p.1 p.2
  · simp only [hp hq]
  · have : Real.sqrt (ρ p.1 p.2) = 0 := Real.sqrt_eq_zero_of_nonpos (not_lt.1 hq)
    simp [this]

theorem a34_lp_norm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Lp (Euc d) 2 μ) : ‖f‖ ^ 2 = ∫ a, ‖(f : α → Euc d) a‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  exact real_inner_self_eq_norm_sq _

theorem a34_Phi_integral (hρ : A33Rho T ρ) (f : ℝ × Torus d → Euc d) :
    ∫ p, ‖Real.sqrt (ρ p.1 p.2) • f p‖ ^ 2 ∂(a33_mu0 d T) = ∫ p, ‖f p‖ ^ 2 ∂(a33_nu d T ρ) := by
  unfold a33_nu
  rw [integral_withDensity_eq_integral_toReal_smul₀ hρ.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun p => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, a34_sq_sqrt_eq, smul_eq_mul]
  rw [ENNReal.toReal_ofReal', Real.coe_toNNReal']

/-- the map `f ↦ √ρ f` on `L²` -/
def a34_Phi0 (hρ : A33Rho T ρ) (f : Lp (Euc d) 2 (a33_nu d T ρ)) : Lp (Euc d) 2 (a33_mu0 d T) :=
  (a34_Phi_memLp hρ f).toLp _

theorem a34_Phi0_coe (hρ : A33Rho T ρ) (f : Lp (Euc d) 2 (a33_nu d T ρ)) :
    (a34_Phi0 hρ f : ℝ × Torus d → Euc d) =ᵐ[a33_mu0 d T]
      fun p => Real.sqrt (ρ p.1 p.2) • (f : ℝ × Torus d → Euc d) p :=
  (a34_Phi_memLp hρ f).coeFn_toLp

theorem a34_Phi0_add (hρ : A33Rho T ρ) (f g : Lp (Euc d) 2 (a33_nu d T ρ)) :
    a34_Phi0 hρ (f + g) = a34_Phi0 hρ f + a34_Phi0 hρ g := by
  apply Lp.ext
  have h1 := a34_Phi0_coe hρ (f + g)
  have h2 := a34_Phi0_coe hρ f
  have h3 := a34_Phi0_coe hρ g
  have h4 := a34_smul_ae hρ (Lp.coeFn_add f g)
  filter_upwards [h1, h2, h3, h4, Lp.coeFn_add (a34_Phi0 hρ f) (a34_Phi0 hρ g)] with p e1 e2 e3 e4 e5
  rw [e5]
  simp only [Pi.add_apply] at e4 ⊢
  rw [e1, e4, e2, e3, smul_add]

theorem a34_Phi0_smul (hρ : A33Rho T ρ) (c : ℝ) (f : Lp (Euc d) 2 (a33_nu d T ρ)) :
    a34_Phi0 hρ (c • f) = c • a34_Phi0 hρ f := by
  apply Lp.ext
  have h1 := a34_Phi0_coe hρ (c • f)
  have h2 := a34_Phi0_coe hρ f
  have h4 := a34_smul_ae hρ (Lp.coeFn_smul c f)
  filter_upwards [h1, h2, h4, Lp.coeFn_smul c (a34_Phi0 hρ f)] with p e1 e2 e4 e5
  rw [e5]
  simp only [Pi.smul_apply] at e4 ⊢
  rw [e1, e4, e2, smul_comm]

theorem a34_Phi0_norm (hρ : A33Rho T ρ) (f : Lp (Euc d) 2 (a33_nu d T ρ)) :
    ‖a34_Phi0 hρ f‖ = ‖f‖ := by
  have h1 : ‖a34_Phi0 hρ f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [a34_lp_norm_sq, a34_lp_norm_sq, ← a34_Phi_integral hρ]
    refine integral_congr_ae ?_
    filter_upwards [a34_Phi0_coe hρ f] with p hp
    rw [hp]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1

/-- the linear isometry `f ↦ √ρ f` -/
def a34_Phi (hρ : A33Rho T ρ) :
    Lp (Euc d) 2 (a33_nu d T ρ) →ₗᵢ[ℝ] Lp (Euc d) 2 (a33_mu0 d T) where
  toFun := a34_Phi0 hρ
  map_add' := a34_Phi0_add hρ
  map_smul' := fun c f => a34_Phi0_smul hρ c f
  norm_map' := a34_Phi0_norm hρ

theorem a34_Phi_coe (hρ : A33Rho T ρ) (f : Lp (Euc d) 2 (a33_nu d T ρ)) :
    (a34_Phi hρ f : ℝ × Torus d → Euc d) =ᵐ[a33_mu0 d T]
      fun p => Real.sqrt (ρ p.1 p.2) • (f : ℝ × Torus d → Euc d) p :=
  a34_Phi0_coe hρ f

end Phi

theorem a34_iso_comp {H₁ H₂ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {W : H₂ → Ω → ℝ} (hI : A33Iso P W) (Φ : H₁ →ₗᵢ[ℝ] H₂) :
    A33Iso P (fun h => W (Φ h)) where
  meas := fun h => hI.meas _
  memLp := fun h => hI.memLp _
  lin := fun a b h h' => by
    have := hI.lin a b (Φ h) (Φ h')
    rwa [← map_smul, ← map_smul, ← map_add] at this
  fin := fun {κ} h t J => by
    have := hI.fin (fun a => Φ (h a)) t J
    simpa [map_sum, map_smul] using this
  inner := fun h h' => by
    rw [hI.inner, LinearIsometry.inner_map_map]
  single := fun g => by
    rw [hI.single, Φ.norm_map]
  gauss := fun κ _ _ h => by
    have := hI.gauss κ (fun a => Φ (h a))
    simpa [LinearIsometry.inner_map_map] using this

end HRS.A34
