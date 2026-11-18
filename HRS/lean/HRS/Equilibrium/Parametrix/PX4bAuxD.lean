import HRS.Equilibrium.Parametrix.PX4bAuxC

/-!
# Packet PX4b auxiliaries D: linearity of the generators on good slices
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

open HRS.PDE HRS.PDE.MFAux

variable {d : ℕ} {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- A slice `f` of a kernel with singular point `y` on which the generator is linear:
`Nice`, with integrable `Bop f` and `Jop f`. -/
structure Good (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (β : ℝ) (ρ : Torus d → ℝ) (y : Torus d)
    (f : Torus d → ℝ) : Prop where
  nice : Nice ρ y f
  bop : Integrable (fun u => Bop d s V β ρ f u) (withDensityReal ρ)
  jop : Integrable (fun u => Jop d s ρ f u) (withDensityReal ρ)

theorem px4b_kernel_facts (H : ParxHyp d s V β ρ) :
    Integrable (periodicRiesz d s) ∧ Torus.IsSmoothOffZero (periodicRiesz d s) ∧
      ContDiff ℝ ∞' (Torus.lift ρ) := by
  have hd1 : 1 ≤ d := by have := H.two_le; omega
  have hs0 : 0 < s := by
    have h2 : (2 : ℝ) ≤ d := by exact_mod_cast H.two_le
    rw [H.crit]; linarith
  exact ⟨PDE.MFOneLe.integrable_periodicRiesz hd1 s H.s_nonneg H.s_lt,
    (kerBound_periodicRiesz H.two_le hs0 H.s_lt 0).smooth, H.rho_smooth.smooth⟩

theorem Good.lin (H : ParxHyp d s V β ρ) {y : Torus d} {f₁ f₂ : Torus d → ℝ}
    (h₁ : Good d s V β ρ y f₁) (h₂ : Good d s V β ρ y f₂) (a c : ℝ) :
    Good d s V β ρ y (fun w => a * f₁ w + c * f₂ w) := by
  have hd1 : 1 ≤ d := by have := H.two_le; omega
  obtain ⟨hg, hgs, hρ⟩ := px4b_kernel_facts H
  refine ⟨px4b_Nice_lin hd1 h₁.nice h₂.nice a c, ?_, ?_⟩
  · refine ((h₁.bop.const_mul a).add (h₂.bop.const_mul c)).congr ?_
    filter_upwards [px4b_ae_ne_mu hd1 ρ y] with u hu
    simp only [Pi.add_apply]
    rw [px4b_Bop_lin hu h₁.nice h₂.nice a c]
  · refine ((h₁.jop.const_mul a).add (h₂.jop.const_mul c)).congr ?_
    filter_upwards [px4b_ae_ne_mu hd1 ρ y] with u hu
    simp only [Pi.add_apply]
    rw [px4b_Jop_lin hd1 hg hgs hρ hu h₁.nice h₂.nice a c]

/-- Linearity of `𝒜` on good slices. -/
theorem Good.projGen_lin (H : ParxHyp d s V β ρ) {y x : Torus d} (hxy : x ≠ y)
    {f₁ f₂ : Torus d → ℝ} (h₁ : Good d s V β ρ y f₁) (h₂ : Good d s V β ρ y f₂) (a c : ℝ) :
    projGen d s V β ρ (fun w => a * f₁ w + c * f₂ w) x =
      a * projGen d s V β ρ f₁ x + c * projGen d s V β ρ f₂ x := by
  have hd1 : 1 ≤ d := by have := H.two_le; omega
  obtain ⟨hg, hgs, hρ⟩ := px4b_kernel_facts H
  exact px4b_projGen_lin hd1 hg hgs hρ hxy h₁.nice h₂.nice (h₁.bop.add h₁.jop) (h₂.bop.add h₂.jop) a c

/-- Linearity of `P_μ J` on good slices. -/
theorem Good.projJ_lin (H : ParxHyp d s V β ρ) {y x : Torus d} (hxy : x ≠ y)
    {f₁ f₂ : Torus d → ℝ} (h₁ : Good d s V β ρ y f₁) (h₂ : Good d s V β ρ y f₂) (a c : ℝ) :
    projMean (withDensityReal ρ) (fun z => Jop d s ρ (fun w => a * f₁ w + c * f₂ w) z) x =
      a * projMean (withDensityReal ρ) (fun z => Jop d s ρ f₁ z) x +
        c * projMean (withDensityReal ρ) (fun z => Jop d s ρ f₂ z) x := by
  have hd1 : 1 ≤ d := by have := H.two_le; omega
  obtain ⟨hg, hgs, hρ⟩ := px4b_kernel_facts H
  unfold projMean pair
  have hint : ∫ u, Jop d s ρ (fun w => a * f₁ w + c * f₂ w) u ∂(withDensityReal ρ) =
      a * ∫ u, Jop d s ρ f₁ u ∂(withDensityReal ρ) + c * ∫ u, Jop d s ρ f₂ u ∂(withDensityReal ρ) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (h₁.jop.const_mul a) (h₂.jop.const_mul c)]
    refine integral_congr_ae ?_
    filter_upwards [px4b_ae_ne_mu hd1 ρ y] with u hu
    exact px4b_Jop_lin hd1 hg hgs hρ hu h₁.nice h₂.nice a c
  beta_reduce
  rw [hint, px4b_Jop_lin hd1 hg hgs hρ hxy h₁.nice h₂.nice a c]
  ring

theorem Good.of_smooth (H : ParxHyp d s V β ρ) {f : Torus d → ℝ} (hf : Torus.IsCk 2 f)
    (y : Torus d) : Good d s V β ρ y f :=
  let h := px4b_smooth_slice H hf y
  ⟨h.1, h.2.1, h.2.2⟩

end HRS.Parx
end
