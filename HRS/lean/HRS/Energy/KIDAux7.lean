import HRS.Energy.KIDAux6

/-!
# KID helper file 7: the pathwise identity for the modulated energy
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.PDE HRS.Uniform.Q54c

namespace HRS.KID

variable {d N : ℕ}

section Pathwise

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {D : DynData d}
  {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
  {T Λ : ℝ} {ρ : ℝ → Torus d → ℝ}

/-- The full drift (pair term, empirical term and quadratic background term). -/
def Jfull (D : DynData d) (h : Torus d → ℝ) (ρ : ℝ → Torus d → ℝ) (X : ℝ≥0 → Ω → Config d N)
    (r : ℝ) (ω : Ω) : ℝ :=
  ppDrift D h (X (Real.toNNReal r) ω) - fDrift D h ρ r (X (Real.toNNReal r) ω) +
    wkG D ρ (fK h ρ r) r

theorem kid_pathwise (c : MFctx D T Λ ρ) (hN : 2 ≤ N) {t : ℝ} (ht0 : 0 < t) (htT : t ≤ T)
    (hsol : IsStrongSolution P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    {h : Torus d → ℝ} (hsm : Torus.IsSmooth h) (hev : ∀ x, h (-x) = h x) :
    IsProgressiveL2 P ℱ (fun s ω k => fkeRef D t (Φpp h) X s ω k) ∧
    IsProgressiveL2 P ℱ (empiricalNoiseIntegrand D t (fK h ρ) X) ∧
    ∀ᵐ ω ∂P,
      modulatedEnergyKernel h (X (Real.toNNReal t) ω) (withDensityReal (ρ t)) -
        modulatedEnergyKernel h (X 0 ω) (withDensityReal (ρ 0)) =
      (∫ r in Set.Icc (0 : ℝ) t, Jfull D h ρ X r ω) +
        itoIntegral P ℱ W' (fun s ω k => fkeRef D t (Φpp h) X s ω k) t ω -
        itoIntegral P ℱ W' (empiricalNoiseIntegrand D t (fK h ρ) X) t ω := by
  have hN0 : 0 < N := by omega
  obtain ⟨hΨpp, hpp⟩ := kid_pp_ito c.hV ht0.le htT hsol.toContact hF hsm hev
  obtain ⟨hΨf, hf⟩ := kid_f_ito c hN ht0 htT hsol hF hsm hev
  refine ⟨hΨpp, hΨf, ?_⟩
  filter_upwards [hpp, hf] with ω hωpp hωf
  have hτ : ((Real.toNNReal t : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht0.le
  have h1 := hωpp.2 (Real.toNNReal t) (le_of_eq hτ)
  rw [hτ] at h1
  obtain ⟨hint_f, h2⟩ := hωf t ⟨ht0.le, le_rfl⟩
  have hWc : IntegrableOn (fun r : ℝ => wkG D ρ (fK h ρ r) r) (Set.Icc 0 t) :=
    ((c.continuousOn_Wdiag hsm hev).mono (Set.Icc_subset_Icc le_rfl htT)).integrableOn_Icc
  have hDg := c.Dg_eq hsm hev (t := t) ⟨ht0.le, htT⟩
  have hDg' : Dg h ρ t - Dg h ρ 0 = 2 * ∫ τ in Set.Icc (0 : ℝ) t, wkG D ρ (fK h ρ τ) τ := by
    rw [hDg, intervalIntegral.integral_of_le ht0.le, ← integral_Icc_eq_integral_Ioc,
      ← integral_const_mul]
  have h2' : (∫ r in (0 : ℝ)..t, fDrift D h ρ r (X (Real.toNNReal r) ω)) =
      ∫ r in Set.Icc (0 : ℝ) t, fDrift D h ρ r (X (Real.toNNReal r) ω) := by
    rw [intervalIntegral.integral_of_le ht0.le, ← integral_Icc_eq_integral_Ioc]
  rw [h2'] at h2
  unfold Jfull
  have hi : IntegrableOn (fun r : ℝ => ppDrift D h (X (Real.toNNReal r) ω) -
      fDrift D h ρ r (X (Real.toNNReal r) ω)) (Set.Icc 0 t) := hωpp.1.sub hint_f
  rw [integral_add hi hWc, integral_sub hωpp.1 hint_f]
  rw [energy_eq hev hN0, energy_eq hev hN0]
  simp only [empiricalMartingale] at h2
  rw [hτ] at h2
  linarith

/-- `Jfull` with the time argument of the mean-field data clamped to `[0,T]`. -/
def Jc (D : DynData d) (h : Torus d → ℝ) (ρ : ℝ → Torus d → ℝ) (T : ℝ) (X : ℝ≥0 → Ω → Config d N)
    (r : ℝ) (ω : Ω) : ℝ :=
  ppDrift D h (X (Real.toNNReal r) ω) -
    fDrift D h ρ (clampT T r) (X (Real.toNNReal r) ω) +
    wkG D ρ (fK h ρ (clampT T r)) (clampT T r)

theorem Jc_eq {h : Torus d → ℝ} {r : ℝ} (hr : r ∈ Set.Icc 0 T) (ω : Ω) :
    Jc D h ρ T X r ω = Jfull D h ρ X r ω := by
  unfold Jc Jfull
  rw [clampT_of_mem hr]

theorem MFctx.continuous_Wdiag_clamp (c : MFctx D T Λ ρ) {h : Torus d → ℝ}
    (hsm : Torus.IsSmooth h) (hev : ∀ x, h (-x) = h x) :
    Continuous fun r : ℝ => wkG D ρ (fK h ρ (clampT T r)) (clampT T r) := by
  have := (c.continuous_W hsm hev).comp (continuous_id.prodMk continuous_id)
  simpa only [Function.comp_def, id_eq] using this

instance kid_borelConfig : BorelSpace (Fin N → Torus d) := Pi.borelSpace

theorem measurable_X_joint (hF : IsFilteredSolution P ℱ W' W X) :
    Measurable fun p : ℝ × Ω => X (Real.toNNReal p.1) p.2 :=
  measurable_of_progressive (u := ofNNRealTime X) hF.progressive

theorem MFctx.measurable_Jc (c : MFctx D T Λ ρ) (hF : IsFilteredSolution P ℱ W' W X)
    {h : Torus d → ℝ} (hsm : Torus.IsSmooth h) (hev : ∀ x, h (-x) = h x) :
    Measurable fun p : ℝ × Ω => Jc D h ρ T X p.1 p.2 := by
  have hXm := measurable_X_joint hF
  have h1 : Measurable fun p : ℝ × Ω => ppDrift D h (X (Real.toNNReal p.1) p.2) :=
    (measurable_ppDrift c.hV hsm).comp hXm
  have h2 : Measurable fun p : ℝ × Ω =>
      fDrift D h ρ (clampT T p.1) (X (Real.toNNReal p.1) p.2) := by
    have := (c.measurable_fDrift hsm hev).comp (measurable_fst.prodMk hXm)
    simpa only [Function.comp_def] using this
  have h3 : Measurable fun p : ℝ × Ω => wkG D ρ (fK h ρ (clampT T p.1)) (clampT T p.1) :=
    (c.continuous_Wdiag_clamp hsm hev).measurable.comp measurable_fst
  unfold Jc
  exact (h1.sub h2).add h3

end Pathwise

end HRS.KID
