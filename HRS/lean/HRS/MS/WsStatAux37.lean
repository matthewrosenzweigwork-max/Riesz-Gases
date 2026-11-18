import HRS.MS.WsStatAux35

/-!
# S21 packet K-6: finite-dimensional laws of the scaled Gaussian objects

* `s21_Zh_fdd`: if `Z` is a linear Gaussian evolution with noise level `q = beta^{-1}`, then `sqrt beta Z` has the finite-dimensional
  coordinate laws `multivariateGaussian 0 (beta C_0 + noiseCovW C 1)`.
* `s21_gammahat_fdd`: scaling of the initial Gaussian path measure by `sqrt beta`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath
open HRS (Euc)

variable {d : ℕ}

theorem s21_Zh_fdd {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P'] {m T : ℝ}
    {C : WholeCoeff d} {C₀ : (Euc d → ℝ) → (Euc d → ℝ) → ℝ} {Z : ℝ → Ω' → OscDual d m} {β : ℝ} (hβ : 0 < β)
    (hZ : IsLinearGaussianEvolutionW P' C m β⁻¹ T C₀ Z) {p : ℕ} (ts : Fin p → ℝ)
    (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T) (αs : Fin p → MultiIndex d) :
    P'.map (fun ζ => (WithLp.toLp 2 fun a => OscDual.coord (Real.sqrt β • Z (ts a) ζ) (αs a) :
        EuclideanSpace ℝ (Fin p))) =
      multivariateGaussian 0 (Matrix.of fun a c =>
        β * C₀ (propagatorW C 0 (ts a) (oscTestFun m (αs a))) (propagatorW C 0 (ts c) (oscTestFun m (αs c))) +
          noiseCovW C 1 (ts a) (ts c) (oscTestFun m (αs a)) (oscTestFun m (αs c))) := by
  have hc : Real.sqrt β ≠ 0 := (Real.sqrt_pos.2 hβ).ne'
  have h := hZ.gaussian p ts (fun a => oscTestFun m (αs a)) hts (fun a => s56_isOscTest m (αs a))
  simp only [OscDual.eval_oscTestFun] at h
  unfold law at h
  have hvm : Measurable (fun ζ => (WithLp.toLp 2 fun a => OscDual.coord (Z (ts a) ζ) (αs a) :
      EuclideanSpace ℝ (Fin p))) := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp (measurable_pi_iff.2 fun a => ?_)
    exact (s56_continuous_coord m (αs a)).measurable.comp (hZ.meas _)
  have hfun : (fun ζ => (WithLp.toLp 2 fun a => OscDual.coord (Real.sqrt β • Z (ts a) ζ) (αs a) :
      EuclideanSpace ℝ (Fin p))) = (fun z : EuclideanSpace ℝ (Fin p) => Real.sqrt β • z) ∘
      (fun ζ => (WithLp.toLp 2 fun a => OscDual.coord (Z (ts a) ζ) (αs a) : EuclideanSpace ℝ (Fin p))) := by
    funext ζ
    ext a
    simp [OscDual.coord_smul]
  have hsm : Measurable (fun z : EuclideanSpace ℝ (Fin p) => Real.sqrt β • z) :=
    by fun_prop
  rw [hfun, ← Measure.map_map hsm hvm, h, s21_gauss_smul_ne _ hc]
  congr 1
  ext a c
  simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Real.sq_sqrt hβ.le]
  rw [s21_noiseCovW_q C β⁻¹ (ts a) (ts c)]
  field_simp

theorem s21_gammahat_fdd {m T : ℝ} {β : ℝ} (hβ : 0 < β) (γ0 : Measure (OscPath d m T))
    (Cs : ℝ → ℝ → MultiIndex d → MultiIndex d → ℝ)
    (hγ : ∀ (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T) (αs : Fin p → MultiIndex d),
      (Matrix.of fun a c => Cs (ts a) (ts c) (αs a) (αs c)).PosSemidef ∧
      γ0.map (fun w : OscPath d m T => (WithLp.toLp 2 fun a => OscDual.coord (OscPath.at' w ⟨ts a, hts a⟩)
          (αs a) : EuclideanSpace ℝ (Fin p))) =
        multivariateGaussian 0 (Matrix.of fun a c => Cs (ts a) (ts c) (αs a) (αs c)))
    (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T) (αs : Fin p → MultiIndex d) :
    (Matrix.of fun a c => β * Cs (ts a) (ts c) (αs a) (αs c)).PosSemidef ∧
      (γ0.map (Real.sqrt β • ContinuousLinearMap.id ℝ (OscPath d m T))).map
        (fun w : OscPath d m T => (WithLp.toLp 2 fun a => OscDual.coord (OscPath.at' w ⟨ts a, hts a⟩)
          (αs a) : EuclideanSpace ℝ (Fin p))) =
        multivariateGaussian 0 (Matrix.of fun a c => β * Cs (ts a) (ts c) (αs a) (αs c)) := by
  have hc : Real.sqrt β ≠ 0 := (Real.sqrt_pos.2 hβ).ne'
  obtain ⟨hpsd, hlaw⟩ := hγ p ts hts αs
  have hmat : (Matrix.of fun a c => β * Cs (ts a) (ts c) (αs a) (αs c)) =
      (Real.sqrt β ^ 2) • (Matrix.of fun a c => Cs (ts a) (ts c) (αs a) (αs c)) := by
    ext a c
    simp [Real.sq_sqrt hβ.le]
  refine ⟨by rw [hmat]; exact hpsd.smul (sq_nonneg _), ?_⟩
  set vec : OscPath d m T → EuclideanSpace ℝ (Fin p) := fun w => (WithLp.toLp 2 fun a =>
    OscDual.coord (OscPath.at' w ⟨ts a, hts a⟩) (αs a) : EuclideanSpace ℝ (Fin p)) with hvec
  have hvm : Measurable vec := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp (measurable_pi_iff.2 fun a => ?_)
    have h1 : Continuous fun w : OscPath d m T => OscPath.at' w ⟨ts a, hts a⟩ := by
      have : Continuous fun w : C(Set.Icc (0 : ℝ) T, OscDual d m) => w ⟨ts a, hts a⟩ := continuous_eval_const _
      exact this
    exact ((s56_continuous_coord m (αs a)).comp h1).measurable
  have hL : Measurable (Real.sqrt β • ContinuousLinearMap.id ℝ (OscPath d m T) : OscPath d m T →L[ℝ] OscPath d m T) :=
    (Real.sqrt β • ContinuousLinearMap.id ℝ (OscPath d m T)).continuous.measurable
  have hfun : vec ∘ (Real.sqrt β • ContinuousLinearMap.id ℝ (OscPath d m T) : OscPath d m T →L[ℝ] OscPath d m T) =
      (fun z : EuclideanSpace ℝ (Fin p) => Real.sqrt β • z) ∘ vec := by
    funext w
    ext a
    simp [hvec, OscPath.at', OscDual.coord_smul]
    rfl
  have hsm : Measurable (fun z : EuclideanSpace ℝ (Fin p) => Real.sqrt β • z) :=
    by fun_prop
  rw [Measure.map_map hvm hL, hfun, ← Measure.map_map hsm hvm]
  show (γ0.map vec).map (fun z : EuclideanSpace ℝ (Fin p) => Real.sqrt β • z) = _
  rw [hlaw, s21_gauss_smul_ne _ hc, hmat]

end HRS.MS.S21
