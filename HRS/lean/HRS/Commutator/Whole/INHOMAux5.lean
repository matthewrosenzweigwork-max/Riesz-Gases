import HRS.Commutator.Whole.INHOMAux4

/-!
# CMX-INHOM auxiliary 5: convolution of `∇g_{>1}` with a Schwartz function is Schwartz

`inhom_ghi_conv`: `(∇g_{>1})_i * φ` is the inverse Fourier transform of the Schwartz function
`c (1-χ) ξ_i |ξ|^{-(d-s)} φ̂`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

/-- The symbol of `(∇g_{>1})_i`. -/
def inhom_M (d : ℕ) (s : ℝ) (c : ℂ) (i : Fin d) (ξ : Euc d) : ℂ :=
  c * ((1 - chi ξ : ℝ) : ℂ) * cmxMY_hi d s i ξ

lemma inhom_M_temperate (c : ℂ) (i : Fin d) :
    Function.HasTemperateGrowth (inhom_M d s c i) := by
  set γ : ℝ := (d : ℝ) - s with hγ
  have h1 : Function.HasTemperateGrowth (fun ξ : Euc d => (1 - chiBump d ξ) *
      (2 * Real.pi * ‖ξ‖) ^ (-γ)) := SAMP1.hasTemperateGrowth_riesz_cut (chiBump d) rfl γ
  have h2 : Function.HasTemperateGrowth (fun ξ : Euc d => ξ i) :=
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasTemperateGrowth
  have h3 : Function.HasTemperateGrowth (fun ξ : Euc d =>
      (2 * Real.pi) ^ γ * (ξ i * ((1 - chiBump d ξ) * (2 * Real.pi * ‖ξ‖) ^ (-γ)))) :=
    (Function.HasTemperateGrowth.const _).mul (h2.mul h1)
  have h4 := (Complex.hasTemperateGrowth_ofReal.comp h3)
  have h5 := (Function.HasTemperateGrowth.const c).mul h4
  have heq : inhom_M d s c i = (fun _ => c) * (Complex.ofReal ∘ fun ξ : Euc d =>
      (2 * Real.pi) ^ γ * (ξ i * ((1 - chiBump d ξ) * (2 * Real.pi * ‖ξ‖) ^ (-γ)))) := by
    funext ξ
    simp only [inhom_M, cmxMY_hi, chi, Pi.mul_apply, Function.comp]
    rw [mul_assoc, ← Complex.ofReal_mul]
    congr 2
    have hx : (2 * Real.pi * ‖ξ‖) ^ (-γ) = (2 * Real.pi) ^ (-γ) * ‖ξ‖ ^ (-γ) :=
      Real.mul_rpow (by positivity) (norm_nonneg _)
    have hcancel : (2 * Real.pi) ^ γ * (2 * Real.pi) ^ (-γ) = 1 := by
      rw [← Real.rpow_add (by positivity)]; simp
    rw [hx]
    calc (1 - chiBump d ξ) * (ξ i * ‖ξ‖ ^ (-(↑d - s))) = ((2 * Real.pi) ^ γ * (2 * Real.pi) ^ (-γ)) *
        ((1 - chiBump d ξ) * (ξ i * ‖ξ‖ ^ (-γ))) := by rw [hcancel, one_mul]
      _ = _ := by ring
  rw [heq]
  exact h5

theorem inhom_ghi_conv (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ c : ℂ, ∀ i : Fin d,
      Integrable (fun x : Euc d => ((ghiForce s x i : ℝ) : ℂ)) ∧
      (∀ ξ : Euc d, 𝓕 (fun x : Euc d => ((ghiForce s x i : ℝ) : ℂ)) ξ = inhom_M d s c i ξ) ∧
      ∀ φ : SchwartzMap (Euc d) ℂ, ∃ Θ : SchwartzMap (Euc d) ℂ,
        (∀ x, Θ x = ∫ y, ((ghiForce s y i : ℝ) : ℂ) * φ (x - y)) ∧
        ∀ ξ, 𝓕 (⇑Θ) ξ = inhom_M d s c i ξ * 𝓕 (⇑φ) ξ := by
  obtain ⟨c, hc⟩ := inhom_ghi_ae hd hs0 hsd
  refine ⟨c, fun i => ?_⟩
  obtain ⟨K, hK, hKF, hae⟩ := hc i
  set Kc : Euc d → ℂ := fun x => ((ghiForce s x i : ℝ) : ℂ) with hKc
  have hKci : Integrable Kc := by
    refine (hK.const_mul c).congr ?_
    filter_upwards [hae] with x hx
    simp only [hKc]; rw [hx]
  have hFT : ∀ ξ, 𝓕 Kc ξ = inhom_M d s c i ξ := by
    intro ξ
    have : 𝓕 Kc ξ = 𝓕 (fun x => c * K x) ξ := by
      rw [Real.fourier_eq, Real.fourier_eq]
      refine integral_congr_ae ?_
      filter_upwards [hae] with x hx
      simp only [hKc]; rw [hx]
    rw [this, Real.fourier_eq']
    have e : ∀ v : Euc d, Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • (c * K v) =
        c * (Complex.exp (↑(-2 * Real.pi * inner ℝ v ξ) * Complex.I) • K v) := by
      intro v; simp only [smul_eq_mul]; ring
    simp_rw [e]
    rw [integral_const_mul, ← Real.fourier_eq', hKF ξ]
    simp only [inhom_M]
    ring
  refine ⟨hKci, hFT, fun φ => ?_⟩
  have hT := inhom_M_temperate (d := d) (s := s) c i
  set S₁ : SchwartzMap (Euc d) ℂ := SchwartzMap.smulLeftCLM ℂ (inhom_M d s c i) (𝓕 φ) with hS₁
  have hS₁' : ∀ ξ, S₁ ξ = inhom_M d s c i ξ * 𝓕 ⇑φ ξ := by
    intro ξ
    rw [hS₁, SchwartzMap.smulLeftCLM_apply_apply hT, smul_eq_mul]
    rfl
  set Θ : SchwartzMap (Euc d) ℂ := 𝓕⁻ S₁ with hΘ
  have hFΘ : 𝓕 ⇑Θ = ⇑S₁ := by
    rw [← SchwartzMap.fourier_coe]
    exact congrArg (⇑) (FourierInvPair.fourier_fourierInv_eq (E := SchwartzMap (Euc d) ℂ)
      (F := SchwartzMap (Euc d) ℂ) S₁)
  have hΘx : ∀ x, Θ x = 𝓕⁻ ⇑S₁ x := fun x => by rw [hΘ, SchwartzMap.fourierInv_coe]
  refine ⟨Θ, fun x => ?_, fun ξ => by rw [hFΘ, hS₁' ξ]⟩
  have hconvi : Integrable (Kc ⋆[ContinuousLinearMap.mul ℂ ℂ] ⇑φ) :=
    hKci.integrable_convolution _ φ.integrable
  have hbdd : BddAbove (Set.range fun x => ‖φ x‖) := by
    refine ⟨‖φ.toBoundedContinuousFunction‖, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact φ.toBoundedContinuousFunction.norm_coe_le_norm y
  have hcont : Continuous (Kc ⋆[ContinuousLinearMap.mul ℂ ℂ] ⇑φ) :=
    hbdd.continuous_convolution_right_of_integrable _ hKci φ.continuous
  have hF : 𝓕 (Kc ⋆[ContinuousLinearMap.mul ℂ ℂ] ⇑φ) = ⇑S₁ := by
    funext ξ
    rw [Real.fourier_mul_convolution_eq hKci φ.integrable, hS₁' ξ, hFT ξ]
  have hSi : Integrable (𝓕 (Kc ⋆[ContinuousLinearMap.mul ℂ ℂ] ⇑φ)) := by
    rw [hF]; exact S₁.integrable
  have := hconvi.fourierInv_fourier_eq hSi (v := x) hcont.continuousAt
  rw [hF] at this
  rw [hΘx x, this, convolution_def]
  rfl

end HRS.Commutator.Whole
