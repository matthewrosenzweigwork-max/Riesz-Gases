import HRS.Sections.Q66AuxA

/-!
# Packet Q66: regularity of the one-body response, part B (measure-theoretic preliminaries)
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

noncomputable section

namespace HRS.Q66

variable {d : ℕ}

theorem q66_cont_of_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Torus d → E}
    (h : Torus.IsSmooth f) : Continuous f :=
  Torus.continuous_of_continuous_lift (E := E)
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) from h).continuous

theorem q66_mu_le_vol (ρ : Torus d → ℝ) :
    withDensityReal ρ ≪ (volume : Measure (Torus d)) :=
  withDensity_absolutelyContinuous _ _

theorem q66_vol_ac_mu {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    (volume : Measure (Torus d)) ≪ withDensityReal ρ := by
  unfold withDensityReal
  exact withDensity_absolutelyContinuous'
    (ENNReal.measurable_ofReal.comp hρ.density.measurable).aemeasurable
    (Filter.Eventually.of_forall fun x => (ENNReal.ofReal_pos.2 (hρ.pos x)).ne')

theorem q66_bound_of_smooth {f : Torus d → ℝ} (h : Torus.IsSmooth f) : ∃ M : ℝ, ∀ x, |f x| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn
    (q66_cont_of_smooth h).continuousOn
  exact ⟨M, fun x => by simpa using hM x (Set.mem_univ _)⟩

/-- A function in `L²(μ)` times `ρ` lies in `L²(dx)`. -/
theorem q66_memLp_mul_rho {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {h : Torus d → ℝ}
    (hh : MemLp h 2 (withDensityReal ρ)) : MemLp (fun x => ρ x * h x) 2 (volume : Measure (Torus d)) := by
  obtain ⟨Λ, hΛ⟩ := q66_bound_of_smooth hρ.smooth
  have hρm : Measurable ρ := hρ.density.measurable
  have hhm : AEStronglyMeasurable h (volume : Measure (Torus d)) :=
    hh.aestronglyMeasurable.mono_ac (q66_vol_ac_mu hρ)
  have hint : Integrable (fun x => h x ^ 2) (withDensityReal ρ) := hh.integrable_sq
  have hint' : Integrable (fun x => ρ x * h x ^ 2) (volume : Measure (Torus d)) := by
    unfold withDensityReal at hint
    rw [integrable_withDensity_iff (f := fun x => ENNReal.ofReal (ρ x))
      (ENNReal.measurable_ofReal.comp hρm)
      (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)] at hint
    refine hint.congr (Eventually.of_forall fun x => ?_)
    simp [ENNReal.toReal_ofReal (hρ.pos x).le, mul_comm]
  have hΛ0 : 0 ≤ Λ := (abs_nonneg _).trans (hΛ 0)
  refine (memLp_two_iff_integrable_sq (hρm.aestronglyMeasurable.mul hhm)).2 ?_
  refine Integrable.mono' (hint'.const_mul Λ) ((hρm.aestronglyMeasurable.mul hhm).pow 2) ?_
  refine Eventually.of_forall fun x => ?_
  have hx := hΛ x
  have hρx : 0 < ρ x := hρ.pos x
  have : ρ x ≤ Λ := (le_abs_self _).trans hx
  have hnn : 0 ≤ (ρ * h) x ^ 2 := sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  simp only [Pi.mul_apply]
  nlinarith [mul_nonneg hρx.le (sq_nonneg (h x)), mul_le_mul_of_nonneg_right this
    (mul_nonneg hρx.le (sq_nonneg (h x)))]

end HRS.Q66

end
