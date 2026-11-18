import HRS.MD.EQBurnGaussLinCov

/-!
# EQ-BURN P2 (`eq_gauss_lin`), part 2: the stationary field as a Gaussian process

The family `(Z^τ(φ))` indexed by times `τ ≥ 0` and smooth tests `φ` is a Gaussian process (`egl_gp`), with covariance
the kernel `eglK` (`egl_cov2`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.PDE HRS.MD.EQGaussLyapDet HRS.MD.EQGaussLyapDet2

namespace HRS.MD.EQBurnGaussLin

variable {d : ℕ}

/-- Index set of the evaluation process: times `τ ≥ 0` and smooth tests. -/
def EglIdx (d : ℕ) : Type := {x : ℝ × (Torus d → ℝ) // 0 ≤ x.1 ∧ Torus.IsSmooth x.2}

/-- The evaluation process `x = (τ, φ) ↦ Z^τ(φ)`. -/
def eglB {Ω : Type*} {m : ℝ} (Z : ℝ → Ω → NegSobolev d m) (x : EglIdx d) (ω : Ω) : ℝ :=
  NegSobolev.eval (Z x.1.1 ω) x.1.2

section GP

variable {s β : ℝ} {hs0 : 0 ≤ s} {hsd : s < d} {hβ : 0 < β} {V ρβ : Torus d → ℝ} {m : ℝ}
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : ℝ → Ω → NegSobolev d m}

theorem egl_B_measurable (hZ : IsStationaryGaussianField P s β hs0 hsd hβ V ρβ m Z) (x : EglIdx d) :
    Measurable (eglB Z x) :=
  (HRS.MD.EQGaussWindow.eqgw_eval_continuous (m := m) x.2.2).measurable.comp (hZ.meas _)

theorem egl_gp (hZ : IsStationaryGaussianField P s β hs0 hsd hβ V ρβ m Z) :
    IsGaussianProcess (eglB Z) P := by
  refine ⟨fun I => ?_⟩
  classical
  let e : Fin I.card ≃ I := I.equivFin.symm
  let τ : Fin I.card → ℝ := fun a => (e a).1.1.1
  let φ : Fin I.card → Torus d → ℝ := fun a => (e a).1.1.2
  have hlaw := hZ.gaussian I.card τ φ (fun a => (e a).1.2.1) (fun a => (e a).1.2.2)
  let W : Ω → EuclideanSpace ℝ (Fin I.card) := fun ω =>
    WithLp.toLp 2 fun a => NegSobolev.eval (Z (τ a) ω) (φ a)
  have hWm : Measurable W :=
    (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 fun a =>
      (HRS.MD.EQGaussWindow.eqgw_eval_continuous (m := m) (e a).1.2.2).measurable.comp (hZ.meas _))
  have hW : HasGaussianLaw W P := by
    refine ⟨hWm.aemeasurable, ?_⟩
    have h : P.map W = ProbabilityTheory.multivariateGaussian 0
        (PDE.stationaryLagCov d s β (PDE.mfData d s hs0 hsd V β hβ) ρβ τ φ) := hlaw
    rw [h]
    infer_instance
  let Lin : EuclideanSpace ℝ (Fin I.card) →ₗ[ℝ] (I → ℝ) :=
    { toFun := fun w i => w (e.symm i)
      map_add' := fun w w' => by funext i; rfl
      map_smul' := fun c w => by funext i; rfl }
  let L : EuclideanSpace ℝ (Fin I.card) →L[ℝ] (I → ℝ) := LinearMap.toContinuousLinearMap Lin
  have heq : (fun ω => I.restrict (fun x => eglB Z x ω)) = L ∘ W := by
    funext ω i
    simp [L, Lin, W, τ, φ, eglB, e]
  rw [heq]
  exact hW.map L

end GP

section Cov

variable (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
  (hV : Torus.IsSmooth V) (hβ : 0 < β) (ρβ : Torus d → ℝ)
  (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) {m : ℝ}
  {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  {Z : ℝ → Ω → NegSobolev d m}

include hd hV hρβ in
/-- The two-point covariance of the evaluation process is the kernel `eglK`. -/
theorem egl_cov2 (hZ : IsStationaryGaussianField P s β hs0 hsd hβ V ρβ m Z) (x y : EglIdx d) :
    cov[eglB Z x, eglB Z y; P] = eglK d s β (mfData d s hs0 hsd V β hβ) ρβ x.1 y.1 := by
  obtain ⟨hpos, hsm, -⟩ := eqgld_frozen hd hs0 hsd V hV hβ ρβ hρβ
  have hρC : Continuous ρβ := MFLinear.continuous_of_isSmooth hsm
  let τ : Fin 2 → ℝ := ![x.1.1, y.1.1]
  let φ : Fin 2 → Torus d → ℝ := ![x.1.2, y.1.2]
  have hτ : ∀ a, 0 ≤ τ a := by
    intro a; fin_cases a
    · exact x.2.1
    · exact y.2.1
  have hφ : ∀ a, Torus.IsSmooth (φ a) := by
    intro a; fin_cases a
    · exact x.2.2
    · exact y.2.2
  have hpsd := HRS.Q41.q41_lagcov_psd hd hs0 hsd hβ hV hρβ hρC hpos τ hτ φ hφ
  have hlaw := hZ.gaussian 2 τ φ hτ hφ
  let W : Ω → EuclideanSpace ℝ (Fin 2) := fun ω =>
    WithLp.toLp 2 fun a => NegSobolev.eval (Z (τ a) ω) (φ a)
  have hWm : Measurable W :=
    (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 fun a =>
      (HRS.MD.EQGaussWindow.eqgw_eval_continuous (m := m) (hφ a)).measurable.comp (hZ.meas _))
  have hmap : P.map W = ProbabilityTheory.multivariateGaussian 0
      (PDE.stationaryLagCov d s β (PDE.mfData d s hs0 hsd V β hβ) ρβ τ φ) := hlaw
  have h1 := covariance_map (μ := P) (X := fun v : EuclideanSpace ℝ (Fin 2) => v 0)
    (Y := fun v : EuclideanSpace ℝ (Fin 2) => v 1) (Z := W)
    (EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous.aestronglyMeasurable
    (EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous.aestronglyMeasurable
    hWm.aemeasurable
  rw [hmap, covariance_eval_multivariateGaussian hpsd 0 1] at h1
  have h2 := eglK_entry d s β (mfData d s hs0 hsd V β hβ) ρβ τ φ 0 1
  have h3 : cov[eglB Z x, eglB Z y; P] =
      cov[(fun v : EuclideanSpace ℝ (Fin 2) => v 0) ∘ W, (fun v : EuclideanSpace ℝ (Fin 2) => v 1) ∘ W; P] := rfl
  rw [h3, ← h1, h2]
  rfl

end Cov

end HRS.MD.EQBurnGaussLin

end
