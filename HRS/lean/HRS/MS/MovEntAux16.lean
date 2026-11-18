import HRS.MS.MovEntAux14

/-!
# S6.6, packet P6 (part 9): `g * ρ₁ - g * ρ₂` is bounded and measurable

`s66_pot_bdd`: for probability densities `ρ₁, ρ₂` with a common Gaussian bound, whose Euclidean modulated Gibbs laws are well defined,
the difference of the potentials `u = g*ρ₁ - g*ρ₂` (`g = rieszKernel d s`) is measurable and bounded.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovEnt

open HRS.Whole

local notation "wd" => Whole.withDensityReal

variable {d : ℕ}

theorem s66_conv_eq {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) (g : Euc d → ℝ) (x : Euc d) :
    Whole.convMeasure g (wd ρ) x = ∫ y, g (x - y) * ρ y :=
  HRS.MS.Thm.convMeasure_withDensityReal g hρ.measurable hρ.nonneg x

theorem s66_conv_measurable {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) {g : Euc d → ℝ}
    (hg : Measurable g) : Measurable (fun x => Whole.convMeasure g (wd ρ) x) := by
  have : (fun x => Whole.convMeasure g (wd ρ) x) = fun x => ∫ y, g (x - y) * ρ y := funext (s66_conv_eq hρ g)
  rw [this]
  have hm : Measurable (fun p : Euc d × Euc d => g (p.1 - p.2) * ρ p.2) :=
    (hg.comp (measurable_fst.sub measurable_snd)).mul (hρ.measurable.comp measurable_snd)
  exact (hm.stronglyMeasurable.integral_prod_right').measurable

theorem s66_pot_bdd (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {N : ℕ} {β : ℝ}
    {ρ₁ ρ₂ : Euc d → ℝ} (hρ₁ : Whole.IsProbDensity ρ₁) (hρ₂ : Whole.IsProbDensity ρ₂)
    {A cg : ℝ} (hA : 0 ≤ A) (hcg : 0 < cg) (hg₁ : ∀ x, ρ₁ x ≤ A * Real.exp (-cg * ‖x‖ ^ 2))
    (hg₂ : ∀ x, ρ₂ x ≤ A * Real.exp (-cg * ‖x‖ ^ 2))
    (hW₁ : GibbsWellDefined (fun x y => rieszKernel d s (x - y)) N β (wd ρ₁))
    (hW₂ : GibbsWellDefined (fun x y => rieszKernel d s (x - y)) N β (wd ρ₂)) :
    ∃ B : ℝ, (∀ x, |Whole.convMeasure (rieszKernel d s) (wd ρ₁) x - Whole.convMeasure (rieszKernel d s) (wd ρ₂) x| ≤ B) ∧
      Measurable (fun x => Whole.convMeasure (rieszKernel d s) (wd ρ₁) x - Whole.convMeasure (rieszKernel d s) (wd ρ₂) x) := by
  have hd1 : 1 ≤ d := by omega
  have hgm : Measurable (rieszKernel d s) := HRS.MS.Wr.wr9_rieszKernel_meas s
  have hmeas := (s66_conv_measurable hρ₁ hgm).sub (s66_conv_measurable hρ₂ hgm)
  refine ?_
  rcases hs0.eq_or_lt with h0 | hpos
  · -- logarithmic case: cancellation by the zero mass of `ρ₁ - ρ₂`
    subst h0
    have hI : ∀ (ρ : Euc d → ℝ), Whole.IsProbDensity ρ →
        GibbsWellDefined (fun x y => rieszKernel d 0 (x - y)) N β (wd ρ) → ∀ x : Euc d,
        Integrable (fun y => rieszKernel d 0 (x - y) * ρ y) := by
      intro ρ hρ hW x
      have h1 := hW.conv_integrable x
      rw [Whole.withDensityReal, integrable_withDensity_iff_integrable_smul'
        hρ.measurable.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at h1
      refine h1.congr (ae_of_all _ fun y => ?_)
      simp [ENNReal.toReal_ofReal (hρ.nonneg y), mul_comm]
    have hint : ∀ ρ : Euc d → ℝ, Whole.IsProbDensity ρ → Integrable ρ := by
      intro ρ hρ
      by_contra hni
      have := hρ.integral_one
      rw [integral_undef hni] at this
      norm_num at this
    obtain ⟨B, hB⟩ := s66_logpot_bdd hd1 (h := fun y => ρ₁ y - ρ₂ y) (A := 2 * A) (c := cg)
      (by positivity) hcg (hρ₁.measurable.sub hρ₂.measurable) ((hint _ hρ₁).sub (hint _ hρ₂))
      (by rw [integral_sub (hint _ hρ₁) (hint _ hρ₂), hρ₁.integral_one, hρ₂.integral_one]; ring)
      (fun y => by
        have h1 := hg₁ y
        have h2 := hg₂ y
        have h3 := hρ₁.nonneg y
        have h4 := hρ₂.nonneg y
        rw [abs_le]
        constructor <;> nlinarith [Real.exp_pos (-cg * ‖y‖ ^ 2)])
    refine ⟨B, fun x => ?_, hmeas⟩
    have e : Whole.convMeasure (rieszKernel d 0) (wd ρ₁) x - Whole.convMeasure (rieszKernel d 0) (wd ρ₂) x =
        ∫ y, rieszKernel d 0 (x - y) * (ρ₁ y - ρ₂ y) := by
      rw [s66_conv_eq hρ₁, s66_conv_eq hρ₂, ← integral_sub (hI ρ₁ hρ₁ hW₁ x) (hI ρ₂ hρ₂ hW₂ x)]
      congr 1; funext y; ring
    rw [e]
    exact hB x
  · -- `s > 0`: both potentials are bounded
    obtain ⟨Bγ, hBγ0, hBγ⟩ := HRS.MS.Thm.convMeasure_bound_of_le hd1 (s := s) (a := 1) (β := 2 * cg)
      hpos hsd one_pos (by positivity)
    set cγ : ℝ := (2 * cg * 1 / (2 * Real.pi)) ^ ((d : ℝ) / 2) with hcγ
    have hcγpos : 0 < cγ := by positivity
    have hγ : ∀ x : Euc d, gaussianComparison d 1 (2 * cg) x = cγ * Real.exp (-cg * ‖x‖ ^ 2) := by
      intro x
      unfold gaussianComparison
      rw [hcγ]
      congr 2
      ring
    have hM : ∀ (ρ : Euc d → ℝ), (∀ x, ρ x ≤ A * Real.exp (-cg * ‖x‖ ^ 2)) →
        ∀ x, ρ x ≤ (A / cγ) * gaussianComparison d 1 (2 * cg) x := by
      intro ρ hg x
      rw [hγ x]
      calc ρ x ≤ A * Real.exp (-cg * ‖x‖ ^ 2) := hg x
        _ = A / cγ * (cγ * Real.exp (-cg * ‖x‖ ^ 2)) := by field_simp
    have hM0 : 0 ≤ A / cγ := by positivity
    refine ⟨A / cγ * Bγ, fun x => ?_, hmeas⟩
    obtain ⟨-, h1a, h1b⟩ := hBγ (A / cγ) ρ₁ hρ₁ hM0 (hM ρ₁ hg₁) x
    obtain ⟨-, h2a, h2b⟩ := hBγ (A / cγ) ρ₂ hρ₂ hM0 (hM ρ₂ hg₂) x
    rw [abs_le]
    constructor <;> linarith

end HRS.MS.MovEnt

end
