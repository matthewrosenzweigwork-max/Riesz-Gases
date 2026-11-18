import HRS.Equilibrium.Preparation

/-!
# HRS.Equilibrium.PreparationFamily — Proposition 4.25, uniformity over families

Proposition 4.25 `O:prop:log-prep` (main paper, source lines 5585-5606), the sentence "The constants are
uniform for families satisfying the same density and partition bounds", read together with the proof
(the proof of Proposition 4.25: "This last algebraic argument applies to any reference measure satisfying the
same partition estimates"): the exponent `p` and the constant of `O:eq:prep-uniform` depend only on the
density bound `Λ`, the small negative parameter `a`, and the partition bound `CK` (and on `B`, `B₀`), not
on the reference density itself.  The partition bound is assumed on the parameter range
`[-a, (1 + a)|B₀| + |B|]`, which contains every parameter used by the ratio identity `O:eq:ratio`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d : ℕ}

/-- The interaction integral is bounded uniformly over bounded probability densities:
`|∬ g(x - y) dμ dμ| ≤ max Λ 0 · ∫ |g|` for `μ = ρ dx` with `0 ≤ ρ ≤ Λ`, `∫ρ = 1`. -/
theorem abs_interaction_le {g : Torus d → ℝ} (hg : Measurable g) (hgi : Integrable g)
    (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ) (Λ : ℝ) (hΛ : ∀ x, ρ x ≤ Λ) :
    |∫ z : Torus d × Torus d, g (z.1 - z.2) ∂((withDensityReal ρ).prod (withDensityReal ρ))| ≤
      max Λ 0 * ∫ y, ‖g y‖ := by
  have := isProb_withDensityReal hρ
  have hm : Measurable (fun z : Torus d × Torus d => ‖g (z.1 - z.2)‖ₑ) :=
    (hg.comp (measurable_fst.sub measurable_snd)).enorm
  have hL : ∫⁻ y, ‖g y‖ₑ < ∞ := hgi.2
  have h1 := norm_integral_le_lintegral_norm
    (μ := (withDensityReal ρ).prod (withDensityReal ρ)) (fun z : Torus d × Torus d => g (z.1 - z.2))
  simp only [ofReal_norm] at h1
  have h2 : ∫⁻ z : Torus d × Torus d, ‖g (z.1 - z.2)‖ₑ ∂((withDensityReal ρ).prod (withDensityReal ρ))
      ≤ ENNReal.ofReal (max Λ 0) * ∫⁻ y, ‖g y‖ₑ := by
    rw [lintegral_prod _ hm.aemeasurable]
    calc ∫⁻ x, ∫⁻ y, ‖g (x - y)‖ₑ ∂withDensityReal ρ ∂withDensityReal ρ
        ≤ ∫⁻ _x, (ENNReal.ofReal (max Λ 0) * ∫⁻ y, ‖g y‖ₑ) ∂withDensityReal ρ :=
          lintegral_mono fun x => (KernelAux2.lintegral_conv_le ρ Λ hΛ (fun z => ‖g z‖ₑ) x).trans
            (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left Λ 0)) zero_le)
      _ = ENNReal.ofReal (max Λ 0) * ∫⁻ y, ‖g y‖ₑ := by rw [lintegral_const, measure_univ, mul_one]
  rw [← Real.norm_eq_abs]
  refine h1.trans ?_
  rw [integral_norm_eq_lintegral_enorm hgi.aestronglyMeasurable]
  calc _ ≤ (ENNReal.ofReal (max Λ 0) * ∫⁻ y, ‖g y‖ₑ).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL.ne) h2
    _ = max Λ 0 * (∫⁻ y, ‖g y‖ₑ).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_max_right _ _)]

section Helpers

open PreparationAux

/-- Family version of `PreparationAux.uniform_of_small_negative`. The exponent `p` (from `a` and `B`)
and the constant `C` (from `CK`, `L`, `a`, `B`, `B₀`) are chosen before the reference measure `μ`.
The partition bound `CK` is assumed on `[-a, (1 + a)|B₀| + |B|] ⊇ [-a, p|B₀| + |B|]`, and the
interaction integral is assumed bounded by `L`. -/
theorem uniform_of_partition_bound {g : Torus d → ℝ} (hg : Measurable g) (a : ℝ) (ha : 0 < a)
    (CK L B B₀ : ℝ) :
    ∃ p : ℝ, 1 < p ∧ ∃ C : ℝ, ∀ (μ : Measure (Torus d)) [IsProbabilityMeasure μ],
      Integrable (fun z : Torus d × Torus d => g (z.1 - z.2)) (μ.prod μ) →
      (∀ N : ℕ, 2 ≤ N → ∀ γ ∈ Set.Icc (-a) ((1 + a) * |B₀| + |B|), KE g N γ μ ≤ ENNReal.ofReal CK) →
      |∫ z : Torus d × Torus d, g (z.1 - z.2) ∂(μ.prod μ)| ≤ L →
      ∀ N : ℕ, 2 ≤ N → ∀ β ∈ Set.Icc (0 : ℝ) B, ∀ β₀ ∈ Set.Icc (0 : ℝ) B₀,
        modulatedGibbs g N β₀ μ ≪ modulatedGibbs g N β μ ∧
          ∫⁻ X, ((modulatedGibbs g N β₀ μ).rnDeriv (modulatedGibbs g N β μ) X) ^ p
              ∂(modulatedGibbs g N β μ) ≤ ENNReal.ofReal C := by
  set q : ℝ := a / (2 * (|B| + 1)) with hq
  have hq0 : 0 < q := by positivity
  have hqa : q ≤ a / 2 := by
    rw [hq, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg B]
  set p : ℝ := 1 + q with hp
  have hp1 : 1 < p := by linarith
  have hp0 : 0 ≤ p := by linarith
  have hB0abs : 0 ≤ |B₀| := abs_nonneg _
  have hBabs : 0 ≤ |B| := abs_nonneg _
  have hpB : 0 ≤ p * |B₀| := mul_nonneg hp0 hB0abs
  set B₁ : ℝ := p * |B₀| + |B| with hB₁
  have hB12 : B₁ ≤ (1 + a) * |B₀| + |B| := by
    have : p * |B₀| ≤ (1 + a) * |B₀| := mul_le_mul_of_nonneg_right (by linarith) hB0abs
    linarith
  set Cp : ℝ := max CK 1 with hCp
  have hCp1 : 1 ≤ Cp := le_max_right _ _
  set m₀ : ℝ := Real.exp (-(|B₀| * L / 2)) with hm₀
  have hm0 : 0 < m₀ := Real.exp_pos _
  refine ⟨p, hp1, Cp ^ (p - 1) * Cp / m₀ ^ p, fun μ _ hI hT hGL N hN β hβ β₀ hβ₀ => ?_⟩
  set G := ∫ z : Torus d × Torus d, g (z.1 - z.2) ∂(μ.prod μ) with hG
  have hC₁ : ∀ N : ℕ, 2 ≤ N → ∀ γ ∈ Set.Icc (-a) B₁, KE g N γ μ ≤ ENNReal.ofReal CK :=
    fun N hN γ hγ => hT N hN γ ⟨hγ.1, hγ.2.trans hB12⟩
  obtain ⟨hβ1, hβ2⟩ := hβ
  obtain ⟨hβ₀1, hβ₀2⟩ := hβ₀
  -- range facts
  have hβB1 : β ∈ Set.Icc (-a) B₁ := ⟨by linarith, by have := le_abs_self B; linarith⟩
  have hβ₀B1 : β₀ ∈ Set.Icc (-a) B₁ := ⟨by linarith, by
    have h1 := le_abs_self B₀
    have h2 : |B₀| ≤ p * |B₀| := by nlinarith
    linarith⟩
  have hγ : β - p * (β - β₀) ∈ Set.Icc (-a) B₁ := by
    have e : β - p * (β - β₀) = p * β₀ - q * β := by rw [hp]; ring
    rw [e]
    constructor
    · have h1 : q * β ≤ q * |B| := mul_le_mul_of_nonneg_left (hβ2.trans (le_abs_self B)) hq0.le
      have h2 : q * |B| ≤ a := by
        rw [hq]
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      have h3 : 0 ≤ p * β₀ := by positivity
      linarith
    · have h1 : p * β₀ ≤ p * |B₀| := mul_le_mul_of_nonneg_left (hβ₀2.trans (le_abs_self B₀)) hp0
      have h2 : 0 ≤ q * β := by positivity
      linarith
  have hfin : ∀ γ ∈ Set.Icc (-a) B₁, KE g N γ μ ≠ ∞ := fun γ hγ =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hC₁ N hN γ hγ)
  have hZle : ∀ γ ∈ Set.Icc (-a) B₁, Zf (Measure.pi fun _ : Fin N => μ) (Wen g N μ) γ ≤ Cp := by
    intro γ hγ
    rw [← toReal_KE hg]
    calc (KE g N γ μ).toReal ≤ (ENNReal.ofReal CK).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (hC₁ N hN γ hγ)
      _ = max CK 0 := ENNReal.toReal_ofReal'
      _ ≤ Cp := max_le_max le_rfl zero_le_one
  have hf0 := log_Zf_ge hg hI (by omega : 1 ≤ N) (hfin β₀ hβ₀B1)
  have hZ0ge : m₀ ≤ Zf (Measure.pi fun _ : Fin N => μ) (Wen g N μ) β₀ := by
    have hZpos := Zf_pos hg (hfin β₀ hβ₀B1)
    have h1 : -(|B₀| * L / 2) ≤ Real.log (Zf (Measure.pi fun _ : Fin N => μ) (Wen g N μ) β₀) := by
      have hb : β₀ ≤ |B₀| := hβ₀2.trans (le_abs_self B₀)
      have e1 : β₀ * (-|G|) ≤ β₀ * G := mul_le_mul_of_nonneg_left (neg_abs_le G) hβ₀1
      have e2 : β₀ * |G| ≤ |B₀| * L := mul_le_mul hb hGL (abs_nonneg _) hB0abs
      nlinarith
    calc m₀ = Real.exp (-(|B₀| * L / 2)) := rfl
      _ ≤ Real.exp (Real.log _) := Real.exp_le_exp.2 h1
      _ = _ := Real.exp_log hZpos
  obtain ⟨hac, hint⟩ := lintegral_rnDeriv_rpow (N := N) hg hp1.le (hfin β hβB1) (hfin β₀ hβ₀B1)
  refine ⟨hac, ?_⟩
  rw [hint, ← KE_eq]
  have hKγ : KE g N (β - p * (β - β₀)) μ =
      ENNReal.ofReal (Zf (Measure.pi fun _ : Fin N => μ) (Wen g N μ) (β - p * (β - β₀))) := by
    rw [← toReal_KE hg, ENNReal.ofReal_toReal (hfin _ hγ)]
  have hZb := Zf_pos hg (hfin β hβB1)
  have hZg := Zf_pos hg (hfin _ hγ)
  have hZ0pos : 0 < Zf (Measure.pi fun _ : Fin N => μ) (Wen g N μ) β₀ := lt_of_lt_of_le hm0 hZ0ge
  have hr : 0 ≤ (Zf (Measure.pi fun _ : Fin N => μ) (Wen g N μ) β /
      Zf (Measure.pi fun _ : Fin N => μ) (Wen g N μ) β₀) ^ p :=
    Real.rpow_nonneg (div_nonneg hZb.le hZ0pos.le) p
  rw [hKγ, ← ENNReal.ofReal_inv_of_pos hZb, ← ENNReal.ofReal_mul hr,
    ← ENNReal.ofReal_mul (inv_nonneg.2 hZb.le)]
  exact ENNReal.ofReal_le_ofReal
    (real_ineq hZb hm0 hZ0ge hp1.le (hZle β hβB1) hZg (hZle _ hγ))

end Helpers

/-- Proposition 4.25, `O:eq:prep-uniform`, uniformly over all bounded probability densities that satisfy
the same density bound `Λ` and the same partition bound `CK` on `[-a, (1 + a)|B₀| + |B|]`. -/
theorem log_prep_uniform_family (hd : 2 ≤ d) (Λ a CK B B₀ : ℝ) (ha : 0 < a) :
    ∃ p : ℝ, 1 < p ∧ ∃ C : ℝ, ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      (∀ N : ℕ, 2 ≤ N → ∀ γ ∈ Set.Icc (-a) ((1 + a) * |B₀| + |B|),
        modNormalizerE (periodicRiesz d 0) N γ (withDensityReal ρ) ≤ ENNReal.ofReal CK) →
      ∀ N : ℕ, 2 ≤ N → ∀ β ∈ Set.Icc (0 : ℝ) B, ∀ β₀ ∈ Set.Icc (0 : ℝ) B₀,
        modulatedGibbs (periodicRiesz d 0) N β₀ (withDensityReal ρ) ≪
            modulatedGibbs (periodicRiesz d 0) N β (withDensityReal ρ) ∧
          ∫⁻ X, ((modulatedGibbs (periodicRiesz d 0) N β₀ (withDensityReal ρ)).rnDeriv
              (modulatedGibbs (periodicRiesz d 0) N β (withDensityReal ρ)) X) ^ p
              ∂(modulatedGibbs (periodicRiesz d 0) N β (withDensityReal ρ)) ≤
            ENNReal.ofReal C := by
  have hs0 : (0 : ℝ) ≤ 0 := le_rfl
  have hsd : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hg : Measurable (periodicRiesz d 0) := PoleCavityAux.measurable_periodicRiesz hd hs0 hsd
  have hgi : Integrable (periodicRiesz d 0) := KernelAux.integrable_periodicRiesz hd hs0 hsd
  obtain ⟨p, hp, C, hC⟩ := uniform_of_partition_bound (g := periodicRiesz d 0) hg a ha CK
    (max Λ 0 * ∫ y, ‖periodicRiesz d 0 y‖) B B₀
  refine ⟨p, hp, C, fun ρ hρ hΛ hPart => ?_⟩
  have := isProb_withDensityReal hρ
  have hI := PreparationAux.integrable_pair_withDensity hg hgi ρ Λ hΛ (ν := withDensityReal ρ) rfl
  exact hC (withDensityReal ρ) hI hPart (abs_interaction_le hg hgi ρ hρ Λ hΛ)

end HRS
