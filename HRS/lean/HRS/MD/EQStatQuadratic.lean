import HRS.MD.EQStatQuadCrudeQ
import HRS.PDE.MeanFieldDecayGap
import HRS.Sections.Q41Aux14

/-!
# EQ-STATIC-U, part 7: `eq_static_quadratic`, uniform in `β ∈ [β₋,β₊]` and the thermal density family

`HRS.quadStat_variance` (Proposition 4.3) with its constant chosen before `β ∈ [β₋,β₊]` and before the density:
`eqstat_quad_large` (large `N`) is combined with `eqstat_quad_crude_Q` (each of the finitely many `N < N₁`), and the
thermal densities are bounded by a common `Λ` through `PDE.MFDecay.exists_thermal_bounds`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.MD.EQStat

open HRS HRS.Quad HRS.External

variable {d : ℕ} {s : ℝ}

/-- `quadStat_variance` with the constant uniform in `β ∈ [β₋,β₊]` and in `ρ ≤ Λ₀`. -/
theorem eqstat_quadStat_variance (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {βm βp : ℝ} (hβm : 0 < βm)
    (hββ : βm ≤ βp) (Λ0 : ℝ) :
    ∃ C : ℝ, ∀ {β : ℝ}, βm ≤ β → β ≤ βp → ∀ (ρ : Torus d → ℝ), SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ0) →
      ∀ (B : ℝ) (h : Torus d → Torus d → ℝ), Measurable (Function.uncurry h) →
      (∀ x y, h x y = h y x) →
      (∀ x y, x ≠ y → |h x y| ≤ B * singEnvelope s (Torus.eucDist x y)) →
      ∀ N : ℕ, 2 ≤ N →
        ∀ ν ∈ ({withDensityReal ρ,
            firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))} :
              Set (Measure (Torus d))),
          (N : ℝ≥0∞) * evariance (fun X : Config d N => quadStat h ν X)
              (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
            ENNReal.ofReal (C * B ^ 2 * deltaN d s N) := by
  obtain ⟨C₁, N₁, h1⟩ := eqstat_quad_large hd hs0 hsd hβm hββ Λ0
  have hc : ∀ N : ℕ, ∃ C : ℝ, 2 ≤ N → ∀ {β : ℝ}, βm ≤ β → β ≤ βp → ∀ (ρ : Torus d → ℝ), SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ0) → ∀ (B : ℝ) (h : Torus d → Torus d → ℝ), Measurable (Function.uncurry h) →
      (∀ x y, x ≠ y → |h x y| ≤ B * singEnvelope s (Torus.eucDist x y)) →
      ∀ ν ∈ ({withDensityReal ρ,
          firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))} :
            Set (Measure (Torus d))),
        (N : ℝ≥0∞) * evariance (fun X : Config d N => quadStat h ν X)
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * B ^ 2 * deltaN d s N) := by
    intro N
    by_cases hN : 2 ≤ N
    · obtain ⟨C, hC⟩ := eqstat_quad_crude_Q hd hs0 hsd hβm hββ Λ0 hN
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h => absurd h hN⟩
  choose Cs hCs using hc
  refine ⟨|C₁| + ∑ N ∈ Finset.range N₁, |Cs N|, ?_⟩
  intro β hβ1 hβ2 ρ hρ hΛ B h hm hsym hh N hN ν hν
  have hD : 0 ≤ B ^ 2 * deltaN d s N := by
    have := Quad.deltaN_pos hd hs0 hsd (N := N) (by omega)
    positivity
  by_cases hNN : N₁ ≤ N
  · refine (h1 hβ1 hβ2 ρ hρ hΛ N hNN hN B h hm hsym hh ν hν).trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : C₁ ≤ |C₁| + ∑ N ∈ Finset.range N₁, |Cs N| := by
      have := le_abs_self C₁
      have : 0 ≤ ∑ N ∈ Finset.range N₁, |Cs N| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
    nlinarith [mul_le_mul_of_nonneg_right h2 hD]
  · have hlt : N < N₁ := not_le.1 hNN
    refine (hCs N hN hβ1 hβ2 ρ hρ hΛ B h hm hh ν hν).trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : Cs N ≤ |C₁| + ∑ N ∈ Finset.range N₁, |Cs N| := by
      have h3 : |Cs N| ≤ ∑ N ∈ Finset.range N₁, |Cs N| :=
        Finset.single_le_sum (f := fun N => |Cs N|) (fun M _ => abs_nonneg (Cs M)) (Finset.mem_range.2 hlt)
      have := le_abs_self (Cs N)
      have := abs_nonneg C₁
      linarith
    nlinarith [mul_le_mul_of_nonneg_right h2 hD]

/-- The thermal setup: a common density bound `Λ` for all thermal densities, `canonicalGibbs = modulatedGibbs`. -/
theorem eqstat_thermal_setup (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) :
    ∃ Lam : ℝ, ∀ β : ℝ, β ∈ Set.Icc βm βp → ∀ ρβ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) V β ρβ →
      ∃ hρs : SmoothPosDensity ρβ, (∀ x, ρβ x ≤ Lam) ∧
        ∀ N : ℕ, canonicalGibbs (periodicRiesz d s) V N β =
          modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρβ) := by
  have hVc : Continuous V :=
    HRS.PDE.MFAux.continuous_of_isCk (ContDiff.of_le
      (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift V) from hV) (by exact_mod_cast le_top))
  obtain ⟨lam, Lam, hlam, hb⟩ :=
    PDE.MFDecay.exists_thermal_bounds (by omega : 1 ≤ d) s hs0 hsd βm βp hβm hββ V hVc
  refine ⟨Lam, fun β hβ ρβ hρ => ?_⟩
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  obtain ⟨hpos, hsm⟩ := Q41.q41_thermal_regular hd hs0 hsd hβ0 hV hρ
  have hρs : SmoothPosDensity ρβ := ⟨hρ.1, hsm, hpos⟩
  refine ⟨hρs, fun x => (hb β hβ ρβ hρ (PoleCavityAux.continuous_of_smoothPos hρs) hpos x).2, fun N => ?_⟩
  obtain ⟨Λ, hΛ0, hΛ'⟩ := PoleCavityAux.exists_density_bound hρs
  refine canonicalGibbs_eq_modulatedGibbs (periodicRiesz d s) V β ρβ hρ
    (fun x => periodicRiesz_neg x) ?_
  intro x
  exact (CoercAux.J_bounds (by omega : 1 ≤ d) hs0 hsd one_pos hρs.density hΛ0.le hΛ' x).1

theorem eq_static_quadratic_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, β ∈ Set.Icc βm βp → ∀ ρβ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) V β ρβ → ∀ (B : ℝ) (h : Torus d → Torus d → ℝ),
      Measurable (Function.uncurry h) → (∀ x y, h x y = h y x) →
      (∀ x y, x ≠ y → |h x y| ≤ B * singEnvelope s (Torus.eucDist x y)) →
      ∀ N : ℕ, 2 ≤ N →
        ∀ ν ∈ ({withDensityReal ρβ, firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)} :
            Set (Measure (Torus d))),
          (N : ℝ≥0∞) * evariance (fun X : Config d N => quadStat h ν X)
              (canonicalGibbs (periodicRiesz d s) V N β) ≤
            ENNReal.ofReal (C * B ^ 2 * deltaN d s N) := by
  obtain ⟨Lam, hLam⟩ := eqstat_thermal_setup hd hs0 hsd V hV βm βp hβm hββ
  obtain ⟨C, hCU⟩ := eqstat_quadStat_variance hd hs0 hsd hβm hββ Lam
  refine ⟨|C| + 1, by positivity, fun β hβ ρβ hρ B h hm hsym hh N hN ν hν => ?_⟩
  obtain ⟨hρs, hΛ, hP⟩ := hLam β hβ ρβ hρ
  rw [hP N] at hν ⊢
  refine (hCU hβ.1 hβ.2 ρβ hρs hΛ B h hm hsym hh N hN ν hν).trans (ENNReal.ofReal_le_ofReal ?_)
  have hδ0 : 0 ≤ deltaN d s N := by
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    exact (inv_nonneg.2 hN0.le).trans (MarginalAux.inv_le_deltaN (d := d) hs0 N (by omega))
  have hD : 0 ≤ B ^ 2 * deltaN d s N := by positivity
  nlinarith [mul_le_mul_of_nonneg_right (show C ≤ |C| + 1 by linarith [le_abs_self C]) hD]

end HRS.MD.EQStat

end
