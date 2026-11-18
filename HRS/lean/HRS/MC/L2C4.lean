import HRS.MC.L2C4Aux2

/-!
# Packet L2C-4: the noise covariance is uniformly bounded on `L²`

Relocated proof of `HRS.MC.L2Cov.l2cs_noise_cov_bound` (the frozen statement stays `sorry` in
`HRS/MC/L2CovSpec.lean`; the tie is `HRS/MC/L2C4Tie.lean`).

Route: `ρ^v ≤ M₀` (`Regime.bounds`, resp. `ρ_β ≤ Λ₀`) reduces the covariance to `2q M` times the unweighted
integrated gradient energy `∫_0^t∫|∇U^{v,t}φ|²`; this is bounded by `C ‖Q_βφ‖²` by L2C-3 (3) with `r = 0`, resp.
(frozen, time homogeneous `Ū^{v,t} = Ū^{0,t-v}`, `∇` kills `Q_β`) by L2C-1 (2); finally `‖Q_βφ‖² ≤ (2+2Λ₀)‖φ‖²`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Sec7 HRS.PDE HRS.PDE.MFAdjoint HRS.PDE.MFLinear

namespace HRS.MC.L2C4

variable {d : ℕ}

theorem l2c4_grad_projMean (μ : Measure (Torus d)) (f : Torus d → ℝ) :
    Torus.grad (projMean μ f) = Torus.grad f := by
  funext x
  unfold Torus.grad projMean
  have : Torus.lift (fun y => f y - pair μ f) = fun z => Torus.lift f z - pair μ f := rfl
  rw [this]
  simp [gradient, fderiv_sub_const]

theorem l2c4_prepared (R : Regime d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → ∀ t : ℝ, 0 ≤ t →
      noiseCovariance R.D R.ρ R.D.invβ t φ φ ≤ C * PDE.l2NormSq φ := by
  obtain ⟨C3, c, κ, hC3, -, -, H⟩ := HRS.MC.L2C3.l2c3_proof R
  obtain ⟨m₀, M₀, hm₀, hb⟩ := R.bounds
  obtain ⟨hth, hsm, -⟩ := R.thermal
  have hρc : Continuous R.ρβ := continuous_of_isSmooth hsm
  obtain ⟨Λ₀, hΛ⟩ := (isCompact_range hρc).bddAbove
  have hup : ∀ x, R.ρβ x ≤ Λ₀ := fun x => hΛ ⟨x, rfl⟩
  have hΛ0 : 0 ≤ Λ₀ := (hth.1.nonneg 0).trans (hup 0)
  have hν : 0 < R.D.invβ := by rw [R.hDβ]; exact inv_pos.2 R.hβ
  have hM0 : 0 ≤ M₀ := (hm₀.le.trans (hb 0 le_rfl 0).1).trans (hb 0 le_rfl 0).2
  refine ⟨2 * R.D.invβ * M₀ * C3 * (2 + 2 * Λ₀), by positivity, fun φ hφ t ht => ?_⟩
  have hQ := l2c4_Q_bound hth.1 hρc hup (continuous_of_isSmooth hφ)
  have hφ0 : 0 ≤ PDE.l2NormSq φ := integral_nonneg fun x => sq_nonneg _
  rcases ht.eq_or_lt with h0 | htp
  · subst h0
    have : noiseCovariance R.D R.ρ R.D.invβ 0 φ φ = 0 := by simp [noiseCovariance]
    rw [this]; positivity
  · obtain ⟨F, hF, hprop⟩ := HRS.MC.L2C3.l2c3_classical R htp hφ
    have hc : ∀ r ∈ Set.Icc (0 : ℝ) t,
        Continuous fun x => ‖Torus.grad (propagator R.D R.ρ r t φ) x‖ ^ 2 := by
      intro r hr
      have hs := (HRS.MC.L2C0.l2c0_proof R φ hφ r t hr.1 hr.2).1
      exact (continuous_grad (HRS.MC.L2C3.l2c3_isCk_of_smooth hs 1)).norm.pow 2
    have hI : ContinuousOn (fun r => ∫ x, ‖Torus.grad (propagator R.D R.ρ r t φ) x‖ ^ 2) (Set.Icc 0 t) := by
      refine (HRS.MC.L2C3.l2c3_energy_cont hF (w := fun _ => (1 : ℝ)) continuous_const).congr
        fun r hr => ?_
      rw [hprop r hr]; simp
    have hcov := l2c4_cov_le R.D R.ρ φ hν.le (M := M₀)
      (fun r hr x => ⟨hm₀.le.trans (hb r hr.1 x).1, (hb r hr.1 x).2⟩) hc hI
    obtain ⟨-, -, h3⟩ := H φ hφ 0 t le_rfl ht
    have h2qM : 0 ≤ 2 * R.D.invβ * M₀ := by positivity
    calc _ ≤ _ := hcov
      _ ≤ 2 * R.D.invβ * M₀ * (C3 * PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ)) :=
          mul_le_mul_of_nonneg_left h3 h2qM
      _ ≤ 2 * R.D.invβ * M₀ * (C3 * ((2 + 2 * Λ₀) * PDE.l2NormSq φ)) := by gcongr
      _ = _ := by ring

theorem l2c4_frozen (R : Regime d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → ∀ t : ℝ, 0 ≤ t →
      noiseCovariance R.D (fun _ => R.ρβ) R.D.invβ t φ φ ≤ C * PDE.l2NormSq φ := by
  obtain ⟨C1, c, hC1, -, H1⟩ := HRS.MC.L2C1.l2c1_proof R
  obtain ⟨hth, hsm, -⟩ := R.thermal
  have hρc : Continuous R.ρβ := continuous_of_isSmooth hsm
  obtain ⟨Λ₀, hΛ⟩ := (isCompact_range hρc).bddAbove
  have hup : ∀ x, R.ρβ x ≤ Λ₀ := fun x => hΛ ⟨x, rfl⟩
  have hΛ0 : 0 ≤ Λ₀ := (hth.1.nonneg 0).trans (hup 0)
  have hν : 0 < R.D.invβ := by rw [R.hDβ]; exact inv_pos.2 R.hβ
  refine ⟨2 * R.D.invβ * Λ₀ * C1 * (2 + 2 * Λ₀), by positivity, fun φ hφ t ht => ?_⟩
  have hQ := l2c4_Q_bound hth.1 hρc hup (continuous_of_isSmooth hφ)
  have hφ0 : 0 ≤ PDE.l2NormSq φ := integral_nonneg fun x => sq_nonneg _
  rcases ht.eq_or_lt with h0 | htp
  · subst h0
    have : noiseCovariance R.D (fun _ => R.ρβ) R.D.invβ 0 φ φ = 0 := by simp [noiseCovariance]
    rw [this]; positivity
  · obtain ⟨F, hF, hprop, hshift⟩ := l2c4_frozen_classical R htp hφ
    have hc : ∀ r ∈ Set.Icc (0 : ℝ) t,
        Continuous fun x => ‖Torus.grad (propagator R.D (fun _ => R.ρβ) r t φ) x‖ ^ 2 := by
      intro r hr
      have hs := (HRS.MC.L2C0.l2c0_proof R φ hφ r t hr.1 hr.2).2
      exact (continuous_grad (HRS.MC.L2C3.l2c3_isCk_of_smooth hs 1)).norm.pow 2
    have hI : ContinuousOn
        (fun r => ∫ x, ‖Torus.grad (propagator R.D (fun _ => R.ρβ) r t φ) x‖ ^ 2) (Set.Icc 0 t) := by
      refine (HRS.MC.L2C3.l2c3_energy_cont hF (w := fun _ => (1 : ℝ)) continuous_const).congr
        fun r hr => ?_
      rw [hprop r hr]; simp
    have hcov := l2c4_cov_le R.D (fun _ => R.ρβ) φ hν.le (M := Λ₀) (t := t)
      (fun r hr x => ⟨hth.1.nonneg x, hup x⟩) hc hI
    -- time homogeneity and reflection
    set G : ℝ → ℝ := fun w => ∫ x, ‖Torus.grad (PDE.equilibriumSemigroup R.D R.ρβ w φ) x‖ ^ 2 with hG
    have hrefl : ∫ r in Set.Icc (0 : ℝ) t, ∫ x, ‖Torus.grad (propagator R.D (fun _ => R.ρβ) r t φ) x‖ ^ 2 =
        ∫ v in Set.Icc (0 : ℝ) t, G v := by
      have h1 : ∫ r in Set.Icc (0 : ℝ) t, ∫ x, ‖Torus.grad (propagator R.D (fun _ => R.ρβ) r t φ) x‖ ^ 2 =
          ∫ r in Set.Icc (0 : ℝ) t, G (t - r) := by
        rw [integral_Icc_eq_integral_Ico, integral_Icc_eq_integral_Ico]
        refine setIntegral_congr_fun measurableSet_Ico fun v hv => ?_
        have hv' : v ∈ Set.Icc (0 : ℝ) t := ⟨hv.1, hv.2.le⟩
        simp only [hG, PDE.equilibriumSemigroup, l2c4_grad_projMean, hprop v hv', hshift v hv]
      rw [h1, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht,
        intervalIntegral.integral_comp_sub_left G t, sub_self, sub_zero,
        intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc]
    obtain ⟨-, h3⟩ := H1 φ hφ t ht
    have h3' : ∫ v in Set.Icc (0 : ℝ) t, G v ≤ C1 * PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) := h3
    have h2qM : 0 ≤ 2 * R.D.invβ * Λ₀ := by positivity
    rw [hrefl] at hcov
    calc _ ≤ _ := hcov
      _ ≤ 2 * R.D.invβ * Λ₀ * (C1 * PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ)) :=
          mul_le_mul_of_nonneg_left h3' h2qM
      _ ≤ 2 * R.D.invβ * Λ₀ * (C1 * ((2 + 2 * Λ₀) * PDE.l2NormSq φ)) := by gcongr
      _ = _ := by ring

/-- (Packet L2C-4.)  Verbatim copy of `HRS.MC.L2Cov.l2cs_noise_cov_bound`. -/
theorem l2c4_proof (R : Regime d) :
    ∃ C : ℝ, ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → ∀ t : ℝ, 0 ≤ t →
      noiseCovariance R.D R.ρ R.D.invβ t φ φ ≤ C * PDE.l2NormSq φ ∧
      noiseCovariance R.D (fun _ => R.ρβ) R.D.invβ t φ φ ≤ C * PDE.l2NormSq φ := by
  obtain ⟨C₁, h₁0, h₁⟩ := l2c4_prepared R
  obtain ⟨C₂, h₂0, h₂⟩ := l2c4_frozen R
  have hφ0 : ∀ φ : Torus d → ℝ, 0 ≤ PDE.l2NormSq φ := fun φ => integral_nonneg fun x => sq_nonneg _
  refine ⟨max C₁ C₂, fun φ hφ t ht => ⟨?_, ?_⟩⟩
  · exact (h₁ φ hφ t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hφ0 φ))
  · exact (h₂ φ hφ t ht).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (hφ0 φ))

end HRS.MC.L2C4
