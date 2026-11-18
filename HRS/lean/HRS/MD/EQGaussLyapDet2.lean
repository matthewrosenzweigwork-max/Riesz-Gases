import HRS.MD.EQGaussLyapDet

/-!
# EQ-GAUSS (a), deterministic part 2: the exact Lyapunov identity and the stationary lag covariance
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.PDE

namespace HRS.MD.EQGaussLyapDet2

open HRS.MD.EQGaussLyapDet

variable {d : ℕ}

theorem eqgld_projMean_idem {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (ψ : Torus d → ℝ) :
    projMean μ (projMean μ ψ) = projMean μ ψ := by
  funext x
  unfold projMean
  have := PDE.MFSemigroup.pair_projMean μ ψ
  unfold projMean at this
  rw [this, sub_zero]

theorem eqgld_responseInverse_projMean {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (g : Torus d → ℝ) (β : ℝ) (ψ : Torus d → ℝ) :
    responseInverse g μ β (projMean μ ψ) = responseInverse g μ β ψ := by
  have hI : IsResponse g μ β (projMean μ ψ) = IsResponse g μ β ψ := by
    funext h
    unfold IsResponse
    rw [eqgld_projMean_idem]
  unfold responseInverse
  rw [hI]

theorem eqgld_cs_projMean {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (g : Torus d → ℝ)
    (β : ℝ) (f h : Torus d → ℝ) :
    susceptibilityCov g μ β (projMean μ f) (projMean μ h) = susceptibilityCov g μ β f h := by
  unfold susceptibilityCov
  rw [eqgld_projMean_idem, eqgld_responseInverse_projMean]

/-- The noise integrand `E(σ) = ∫ ∇U^{σ,a}φ · ∇U^{σ,b}ψ ρ_β dx`. -/
def eqgld_E (D : DynData d) (ρβ : Torus d → ℝ) (A B : Torus d → ℝ) (a b σ : ℝ) : ℝ :=
  ∫ x, inner ℝ (Torus.grad (propagator D (fun _ => ρβ) σ a A) x)
    (Torus.grad (propagator D (fun _ => ρβ) σ b B) x) * ρβ x

theorem eqgld_main (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (φ ψ : Torus d → ℝ)
    (hφ : Torus.IsSmooth φ) (hψ : Torus.IsSmooth ψ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β
        (propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) 0 a φ)
        (propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) 0 b ψ) +
      2 * β⁻¹ * ∫ σ in Set.Icc 0 a, eqgld_E (mfData d s hs0 hsd V β hβ) ρβ φ ψ a b σ =
    susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β φ
        (equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ (b - a) ψ) := by
  obtain ⟨hpos, hρC, c₀, Λ₀, ⟨Hz⟩⟩ := eqgld_frozen hd hs0 hsd V hV hβ ρβ hρβ
  have hd1 : 1 ≤ d := by omega
  have hprob := hρβ.1
  haveI : IsProbabilityMeasure (withDensityReal ρβ) := isProb_withDensityReal hprob
  set D := mfData d s hs0 hsd V β hβ with hD
  have hsm : ∀ f, Torus.IsSmooth f → ∀ r t : ℝ, 0 ≤ r → r ≤ t →
      Torus.IsSmooth (propagator D (fun _ => ρβ) r t f) := fun f hf r t hr hrt =>
    eqgld_prop_smooth hd1 hs0 hsd V hV hβ ρβ hprob hρC hpos f hf r t hr hrt
  have hSsm : ∀ f, Torus.IsSmooth f → ∀ v : ℝ, 0 ≤ v →
      Torus.IsSmooth (equilibriumSemigroup D ρβ v f) := by
    intro f hf v hv
    have h := hsm f hf 0 v le_rfl hv
    unfold equilibriumSemigroup projMean
    unfold Torus.IsSmooth at h ⊢
    exact h.sub contDiff_const
  have hgradS : ∀ f v x, Torus.grad (equilibriumSemigroup D ρβ v f) x =
      Torus.grad (propagator D (fun _ => ρβ) 0 v f) x := fun f v x => by
    unfold equilibriumSemigroup projMean
    exact MFLinear.grad_sub_const _ _ x
  have hc : ∀ f : Torus d → ℝ, Torus.IsSmooth f → Continuous f := fun f hf =>
    MFLinear.continuous_of_isSmooth hf
  have hM : ∀ f : Torus d → ℝ, Torus.IsSmooth f → MemSobolev ((mStar d : ℝ) + 4) f := fun f hf =>
    MFSemigroup.memSobolev_of_isSmooth hf _
  set δ : ℝ := b - a with hδ
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith
  have hb0 : 0 ≤ b := ha.trans hab
  have hadd : ∀ f : Torus d → ℝ, Torus.IsSmooth f → ∀ v τ : ℝ, 0 ≤ v → 0 ≤ τ →
      equilibriumSemigroup D ρβ v (equilibriumSemigroup D ρβ τ f) =
        equilibriumSemigroup D ρβ (v + τ) f := fun f hf v τ hv hτ =>
    MFAdjoint.equilibriumSemigroup_add hd1 s β⁻¹ β⁻¹ c₀ Λ₀ β V ρβ Hz f (hc f hf) (hM f hf) v τ hv hτ
  set w : ℝ → ℝ := fun v => ∫ x, inner ℝ (Torus.grad (equilibriumSemigroup D ρβ v φ) x)
    (Torus.grad (equilibriumSemigroup D ρβ (v + δ) ψ) x) * ρβ x with hw
  -- the integral formula for `(φ, S_δ ψ)`
  have hSδ := hSsm ψ hψ δ hδ0
  obtain ⟨hint1, hcov1⟩ := MFLinear.susceptibilityCov_eq_integral hd1 s β⁻¹ β⁻¹ c₀ Λ₀ β V ρβ Hz φ
    (equilibriumSemigroup D ρβ δ ψ) (hc φ hφ) (hM φ hφ) (hc _ hSδ) (hM _ hSδ)
  have hwint : MeasureTheory.IntegrableOn w (Set.Ici 0) := by
    refine hint1.congr_fun (fun v hv => ?_) measurableSet_Ici
    simp only [hw]
    rw [hadd ψ hψ v δ hv hδ0]
  have hcov1' : susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β φ
      (equilibriumSemigroup D ρβ δ ψ) = 2 * β⁻¹ * ∫ v in Set.Ici (0 : ℝ), w v := by
    rw [hcov1]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ici (fun v hv => ?_)
    simp only [hw]
    rw [hadd ψ hψ v δ hv hδ0]
  -- the integral formula for `(S_a φ, S_b ψ)`
  have hSa := hSsm φ hφ a ha
  have hSb := hSsm ψ hψ b hb0
  obtain ⟨hint2, hcov2⟩ := MFLinear.susceptibilityCov_eq_integral hd1 s β⁻¹ β⁻¹ c₀ Λ₀ β V ρβ Hz
    (equilibriumSemigroup D ρβ a φ) (equilibriumSemigroup D ρβ b ψ) (hc _ hSa) (hM _ hSa)
    (hc _ hSb) (hM _ hSb)
  have hw2 : ∀ v : ℝ, 0 ≤ v → (∫ x, inner ℝ (Torus.grad (equilibriumSemigroup D ρβ v
      (equilibriumSemigroup D ρβ a φ)) x) (Torus.grad (equilibriumSemigroup D ρβ v
      (equilibriumSemigroup D ρβ b ψ)) x) * ρβ x) = w (v + a) := by
    intro v hv
    simp only [hw]
    rw [hadd φ hφ v a hv ha, hadd ψ hψ v b hv hb0]
    have e : v + b = v + a + δ := by rw [hδ]; ring
    rw [e]
  have hcov2' : susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β
      (equilibriumSemigroup D ρβ a φ) (equilibriumSemigroup D ρβ b ψ) =
      2 * β⁻¹ * ∫ v in Set.Ici (0 : ℝ), w (v + a) := by
    rw [hcov2]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ici (fun v hv => hw2 v hv)
  -- projMean invariance
  have hcs : susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β
        (propagator D (fun _ => ρβ) 0 a φ) (propagator D (fun _ => ρβ) 0 b ψ) =
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β
        (equilibriumSemigroup D ρβ a φ) (equilibriumSemigroup D ρβ b ψ) := by
    unfold equilibriumSemigroup
    rw [eqgld_cs_projMean]
  -- the noise integral
  have hE : ∀ σ ∈ Set.Ico (0 : ℝ) a, eqgld_E D ρβ φ ψ a b σ = w (a - σ) := by
    intro σ hσ
    have hσa : σ < a := hσ.2
    have h1 := eqgld_homog hd1 hs0 hsd V hV hβ ρβ hprob hρC hpos φ hφ hσ.1 hσa
    have h2 := eqgld_homog hd1 hs0 hsd V hV hβ ρβ hprob hρC hpos ψ hψ hσ.1 (hσa.trans_le hab)
    unfold eqgld_E
    simp only [hw]
    rw [h1, h2]
    have e : b - σ = a - σ + δ := by rw [hδ]; ring
    rw [e]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hgradS]
    rfl
  have hnoise : ∫ σ in Set.Icc 0 a, eqgld_E D ρβ φ ψ a b σ = ∫ v in Set.Ico (0 : ℝ) a, w v := by
    rw [integral_Icc_eq_integral_Ico]
    rw [setIntegral_congr_fun measurableSet_Ico hE]
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha,
      intervalIntegral.integral_comp_sub_left (fun v => w v) a]
    simp only [sub_self, sub_zero]
    rw [intervalIntegral.integral_of_le ha, ← integral_Ico_eq_integral_Ioc]
  -- the shift
  have hshift : ∫ v in Set.Ici (0 : ℝ), w (v + a) = ∫ v in Set.Ici a, w v := by
    have e1 : ∫ v in Set.Ici (0 : ℝ), w (v + a) = ∫ v, (Set.Ici a).indicator w (v + a) := by
      rw [← integral_indicator measurableSet_Ici]
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      by_cases hv : (0 : ℝ) ≤ v
      · have : a ≤ v + a := by linarith
        simp [Set.indicator, hv, this]
      · have : ¬ a ≤ v + a := by intro h; apply hv; linarith
        simp [Set.indicator, hv, this]
    rw [e1, MeasureTheory.integral_add_right_eq_self (fun v => (Set.Ici a).indicator w v) a,
      integral_indicator measurableSet_Ici]
  have hsplit : ∫ v in Set.Ici (0 : ℝ), w v =
      (∫ v in Set.Ico (0 : ℝ) a, w v) + ∫ v in Set.Ici a, w v := by
    have hU : Set.Ico (0 : ℝ) a ∪ Set.Ici a = Set.Ici 0 := Set.Ico_union_Ici_eq_Ici ha
    have hdisj : Disjoint (Set.Ico (0 : ℝ) a) (Set.Ici a) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact absurd hx.2 (not_lt.2 hx')
    rw [← hU]
    exact setIntegral_union hdisj measurableSet_Ici (hwint.mono_set (by
      intro x hx; rw [← hU]; exact Or.inl hx)) (hwint.mono_set (by
      intro x hx; rw [← hU]; exact Or.inr hx))
  rw [hcs, hcov1', hcov2', hnoise, hshift, hsplit]
  ring

/-- The covariance matrix of the stationary Gaussian field: transported initial covariance plus noise. -/
theorem eqgld_cov_total (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) {p : ℕ} (τ : Fin p → ℝ)
    (hτ : ∀ a, 0 ≤ τ a) (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    (Matrix.of fun a b => susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β
        (propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) 0 (τ a) (φ a))
        (propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) 0 (τ b) (φ b)) +
      2 * β⁻¹ * ∫ σ in Set.Icc 0 (min (τ a) (τ b)),
        eqgld_E (mfData d s hs0 hsd V β hβ) ρβ (φ a) (φ b) (τ a) (τ b) σ) =
    PDE.stationaryLagCov d s β (mfData d s hs0 hsd V β hβ) ρβ τ φ := by
  obtain ⟨hpos, hρC, c₀, Λ₀, ⟨Hz⟩⟩ := eqgld_frozen hd hs0 hsd V hV hβ ρβ hρβ
  have hd1 : 1 ≤ d := by omega
  have hprob := hρβ.1
  haveI : IsProbabilityMeasure (withDensityReal ρβ) := isProb_withDensityReal hprob
  set D := mfData d s hs0 hsd V β hβ with hD
  have hsm : ∀ f, Torus.IsSmooth f → ∀ r t : ℝ, 0 ≤ r → r ≤ t →
      Torus.IsSmooth (propagator D (fun _ => ρβ) r t f) := fun f hf r t hr hrt =>
    eqgld_prop_smooth hd1 hs0 hsd V hV hβ ρβ hprob hρC hpos f hf r t hr hrt
  have hSsm : ∀ f, Torus.IsSmooth f → ∀ v : ℝ, 0 ≤ v →
      Torus.IsSmooth (equilibriumSemigroup D ρβ v f) := by
    intro f hf v hv
    have h := hsm f hf 0 v le_rfl hv
    unfold equilibriumSemigroup projMean
    unfold Torus.IsSmooth at h ⊢
    exact h.sub contDiff_const
  have hc : ∀ f : Torus d → ℝ, Torus.IsSmooth f → Continuous f := fun f hf =>
    MFLinear.continuous_of_isSmooth hf
  have hM : ∀ f : Torus d → ℝ, Torus.IsSmooth f → MemSobolev ((mStar d : ℝ) + 4) f := fun f hf =>
    MFSemigroup.memSobolev_of_isSmooth hf _
  have hsymm : ∀ f g : Torus d → ℝ, Torus.IsSmooth f → Torus.IsSmooth g →
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β f g =
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β g f := fun f g hf hg =>
    MFLinear.cov_symm hd1 Hz (hc f hf) (hM f hf) (hc g hg) (hM g hg)
  ext a b
  simp only [Matrix.of_apply, PDE.stationaryLagCov]
  rcases le_total (τ a) (τ b) with hab | hba
  · rw [if_pos hab, min_eq_left hab]
    exact eqgld_main hd hs0 hsd V hV hβ ρβ hρβ (φ a) (φ b) (hφ a) (hφ b) (hτ a) hab
  · by_cases hEq : τ a ≤ τ b
    · have hab : τ a = τ b := le_antisymm hEq hba
      rw [if_pos hEq, min_eq_left hEq]
      exact eqgld_main hd hs0 hsd V hV hβ ρβ hρβ (φ a) (φ b) (hφ a) (hφ b) (hτ a) hEq
    · rw [if_neg hEq, min_eq_right hba]
      have hm := eqgld_main hd hs0 hsd V hV hβ ρβ hρβ (φ b) (φ a) (hφ b) (hφ a) (hτ b) hba
      have e1 := hsymm (propagator D (fun _ => ρβ) 0 (τ a) (φ a))
        (propagator D (fun _ => ρβ) 0 (τ b) (φ b)) (hsm _ (hφ a) 0 _ le_rfl (hτ a))
        (hsm _ (hφ b) 0 _ le_rfl (hτ b))
      have e2 := hsymm (equilibriumSemigroup D ρβ (τ a - τ b) (φ a)) (φ b)
        (hSsm _ (hφ a) _ (by linarith [not_le.1 hEq])) (hφ b)
      have e3 : ∀ σ, eqgld_E (mfData d s hs0 hsd V β hβ) ρβ (φ b) (φ a) (τ b) (τ a) σ =
          eqgld_E (mfData d s hs0 hsd V β hβ) ρβ (φ a) (φ b) (τ a) (τ b) σ := by
        intro σ
        unfold eqgld_E
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [real_inner_comm]
      simp only [e3] at hm
      rw [e1, e2]
      exact hm

end HRS.MD.EQGaussLyapDet2

end
