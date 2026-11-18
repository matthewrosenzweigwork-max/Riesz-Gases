import HRS.MD.EQGaussLyapDet2
import HRS.Sections.Q41Aux20
import HRS.Sections.Q41Aux13
import HRS.MD.EQGaussWindow
import HRS.Sections.Sec3

/-!
# EQ-BURN P2 (`eq_gauss_lin`), part 1: the covariance kernel of the stationary field

The two-point covariance `Cov(Z^x(φ), Z^y(ψ))` of a stationary Gaussian field is the kernel `eglK` (entry of
`PDE.stationaryLagCov`); here we compute the kernel against the tests `(0, g)` in terms of the propagator, using that the
susceptibility form does not see constants (`projMean`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.PDE HRS.MD.EQGaussLyapDet HRS.MD.EQGaussLyapDet2

namespace HRS.MD.EQBurnGaussLin

variable {d : ℕ}

/-- The susceptibility form does not see constants in its first argument. -/
theorem egl_cs_pm_left {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (g : Torus d → ℝ)
    (β : ℝ) (f h : Torus d → ℝ) :
    susceptibilityCov g μ β (projMean μ f) h = susceptibilityCov g μ β f h := by
  have h1 := eqgld_cs_projMean (μ := μ) g β (projMean μ f) h
  rw [eqgld_projMean_idem] at h1
  rw [← h1, eqgld_cs_projMean]

/-- The susceptibility form does not see constants in its second argument. -/
theorem egl_cs_pm_right {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (g : Torus d → ℝ)
    (β : ℝ) (f h : Torus d → ℝ) :
    susceptibilityCov g μ β f (projMean μ h) = susceptibilityCov g μ β f h := by
  have h1 := eqgld_cs_projMean (μ := μ) g β f (projMean μ h)
  rw [eqgld_projMean_idem] at h1
  rw [← h1, eqgld_cs_projMean]

/-- The two-point covariance kernel (entry of `PDE.stationaryLagCov`). -/
def eglK (d : ℕ) (s β : ℝ) (D : DynData d) (ρβ : Torus d → ℝ) (x y : ℝ × (Torus d → ℝ)) : ℝ :=
  if x.1 ≤ y.1 then
    susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β x.2
      (equilibriumSemigroup D ρβ (y.1 - x.1) y.2)
  else
    susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β
      (equilibriumSemigroup D ρβ (x.1 - y.1) x.2) y.2

theorem eglK_entry (d : ℕ) (s β : ℝ) (D : DynData d) (ρβ : Torus d → ℝ) {p : ℕ}
    (τ : Fin p → ℝ) (φ : Fin p → Torus d → ℝ) (a b : Fin p) :
    PDE.stationaryLagCov d s β D ρβ τ φ a b = eglK d s β D ρβ (τ a, φ a) (τ b, φ b) := by
  simp only [PDE.stationaryLagCov, Matrix.of_apply, eglK]

section Det

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
  (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ)
  (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ)

include hd hV hρβ in
/-- `U^{0,0} g = g` for smooth `g`. -/
theorem egl_prop_zero (g : Torus d → ℝ) (hg : Torus.IsSmooth g) :
    propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) 0 0 g = g := by
  obtain ⟨-, hsm, -⟩ := eqgld_frozen hd hs0 hsd V hV hβ ρβ hρβ
  have hKf := PDE.ClassicalAux.convKernelFacts (by omega : 1 ≤ d) (mfData d s hs0 hsd V β hβ)
  exact PDE.MFSemigroup.propagator_zero _ hKf (PDE.MFSemigroup.isCk_nat_of_isSmooth hV 1) (fun _ => ρβ)
    (PDE.MFSemigroup.isCk_nat_of_isSmooth hsm 1) (PDE.MFSemigroup.isCk_nat_of_isSmooth hg 2)

include hd hV hρβ in
/-- `S_0 g = projMean g` for smooth `g`; the form `C(f, S_0 g)` equals `C(f, g)`. -/
theorem egl_cs_S0 (f g : Torus d → ℝ) (hg : Torus.IsSmooth g) :
    susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β f
        (equilibriumSemigroup (mfData d s hs0 hsd V β hβ) ρβ 0 g) =
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β f g := by
  have : IsProbabilityMeasure (withDensityReal ρβ) := isProb_withDensityReal hρβ.1
  unfold equilibriumSemigroup
  rw [egl_prop_zero hd hs0 hsd V hV hβ ρβ hρβ g hg, egl_cs_pm_right]

include hd hV hρβ in
/-- `K((τ,φ),(0,g)) = C(U^{0,τ}φ, g)`. -/
theorem eglK_zero_right {τ : ℝ} (hτ : 0 ≤ τ) {φ g : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    (hg : Torus.IsSmooth g) :
    eglK d s β (mfData d s hs0 hsd V β hβ) ρβ (τ, φ) (0, g) =
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β
        (propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) 0 τ φ) g := by
  have : IsProbabilityMeasure (withDensityReal ρβ) := isProb_withDensityReal hρβ.1
  unfold eglK
  by_cases h : τ ≤ 0
  · have h0 : τ = 0 := le_antisymm h hτ
    subst h0
    simp only [le_refl, if_true, sub_self]
    rw [egl_cs_S0 hd hs0 hsd V hV hβ ρβ hρβ φ g hg,
      egl_prop_zero hd hs0 hsd V hV hβ ρβ hρβ φ hφ]
  · simp only [h, if_false, sub_zero]
    unfold equilibriumSemigroup
    rw [egl_cs_pm_left]

include hρβ in
/-- `K((0,g),(τ,φ)) = C(g, U^{0,τ}φ)`. -/
theorem eglK_zero_left {τ : ℝ} (hτ : 0 ≤ τ) {φ g : Torus d → ℝ} :
    eglK d s β (mfData d s hs0 hsd V β hβ) ρβ (0, g) (τ, φ) =
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β g
        (propagator (mfData d s hs0 hsd V β hβ) (fun _ => ρβ) 0 τ φ) := by
  have : IsProbabilityMeasure (withDensityReal ρβ) := isProb_withDensityReal hρβ.1
  unfold eglK
  simp only [hτ, if_true, sub_zero]
  unfold equilibriumSemigroup
  rw [egl_cs_pm_right]

include hd hV hρβ in
/-- The cross term of the noise: for smooth `φ_a, φ_b` and `τ ≥ 0`,
`K((0,U_a),(0,U_b)) = C(U_a, U_b)`. -/
theorem eglK_zero_zero {g h : Torus d → ℝ} (hg : Torus.IsSmooth g) (hh : Torus.IsSmooth h) :
    eglK d s β (mfData d s hs0 hsd V β hβ) ρβ (0, g) (0, h) =
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β g h := by
  have := eglK_zero_right hd hs0 hsd V hV hβ ρβ hρβ (le_refl (0 : ℝ)) hg hh
  rw [this, egl_prop_zero hd hs0 hsd V hV hβ ρβ hρβ g hg]

end Det

end HRS.MD.EQBurnGaussLin

end
