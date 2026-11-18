import HRS.Sections.Q66AuxD

/-!
# Packet Q66: regularity of the one-body response, part E (the smooth representative)
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate BoundedContinuousFunction

noncomputable section

namespace HRS.Q66

open HRS.PDE HRS.PDE.MFAux HRS.PDE.MFSchauder

variable {d : ℕ}

theorem q66_kop_eq {g : Torus d → ℝ} {μ : Measure (Torus d)} (f : Torus d → ℝ) (x : Torus d) :
    Kop g μ f x = (∫ y, g (x - y) * f y ∂μ) - pair μ (fun x => ∫ y, g (x - y) * f y ∂μ) := rfl

theorem q66_response_regular (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (β : ℝ)
    (hβ : 0 ≤ β) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {φ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) :
    ∃ r : Torus d → ℝ, Torus.IsSmooth r ∧
      IsResponse (periodicRiesz d s) (withDensityReal ρ) β φ r ∧
      ∀ x, r x + β * Kop (periodicRiesz d s) (withDensityReal ρ) r x =
        projMean (withDensityReal ρ) φ x := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ d := by positivity
    linarith
  set g : Torus d → ℝ := periodicRiesz d s with hg
  set μ : Measure (Torus d) := withDensityReal ρ with hμ
  haveI : IsProbabilityMeasure μ := isProb_withDensityReal hρ.density
  have hρc : Continuous ρ := q66_cont_of_smooth hρ.smooth
  have hρm : Measurable ρ := hρ.density.measurable
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => (hρ.pos x).le
  obtain ⟨Λ, hΛ⟩ := q66_bound_of_smooth hρ.smooth
  have hφc : Continuous φ := q66_cont_of_smooth hφ
  have hφL2 : MemLp φ 2 μ :=
    hφc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨h, ⟨hhL2, hhmean, hheq⟩, -⟩ := exists_unique_response hd hs0 hsd ρ hρ.density Λ
    (fun x => (le_abs_self _).trans (hΛ x)) β hβ φ hφL2
  -- the convolution `G = g * (ρ h)` is continuous
  have hu2 : MemLp (fun x => ρ x * h x) 2 (volume : Measure (Torus d)) := q66_memLp_mul_rho hρ hhL2
  have hg2 : MemLp g 2 (volume : Measure (Torus d)) :=
    (memLp_two_iff_integrable_sq (KernelAux.aestronglyMeasurable_periodicRiesz hd hs0 hsd)).2
      (InitialDataAux.riesz_sq_integrable_volume hd hs0 hs)
  set Gc : Torus d → ℝ := convFun g (fun x => ρ x * h x) with hGc
  have hGcc : Continuous Gc := q66_continuous_conv hg2 hu2
  have hE1 : ∀ x, ∫ y, g (x - y) * h y ∂μ = Gc x := by
    intro x
    rw [hμ, integral_withDensityReal_eq ρ hρm hρ0]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hGc]
    ring
  set m : ℝ := pair μ Gc with hm
  set r : Torus d → ℝ := fun x => projMean μ φ x - β * (Gc x - m) with hr
  have hrc : Continuous r := by
    have : Continuous (projMean μ φ) := by
      unfold projMean; exact hφc.sub continuous_const
    exact this.sub (continuous_const.mul (hGcc.sub continuous_const))
  have hKh : ∀ x, Kop g μ h x = Gc x - m := by
    intro x
    rw [q66_kop_eq]
    have : (fun x => ∫ y, g (x - y) * h y ∂μ) = Gc := funext hE1
    rw [this, hE1]
  have hae : h =ᵐ[μ] r := by
    filter_upwards [hheq] with x hx
    rw [hKh] at hx
    simp only [hr]
    linarith
  have hKr : ∀ x, Kop g μ r x = Gc x - m := by
    intro x
    rw [← hKh x, q66_kop_eq, q66_kop_eq]
    have e1 : ∀ z, ∫ y, g (z - y) * r y ∂μ = ∫ y, g (z - y) * h y ∂μ := fun z =>
      integral_congr_ae (by filter_upwards [hae] with y hy; rw [hy])
    simp only [e1]
  have hresp : IsResponse g μ β φ r := by
    refine ⟨hrc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _), ?_, ?_⟩
    · have : pair μ r = pair μ h := integral_congr_ae (by filter_upwards [hae] with y hy; rw [hy])
      rw [this]; exact hhmean
    · refine Eventually.of_forall fun x => ?_
      rw [hKr]
      simp only [hr]
      ring
  refine ⟨r, ?_, hresp, fun x => ?_⟩
  · -- smoothness
    have hGc' : ∀ x, convFun g (fun y => ρ y * r y) x = Gc x := by
      intro x
      have e1 : ∫ y, g (x - y) * r y ∂μ = Gc x := by
        rw [← hE1 x]
        exact integral_congr_ae (by filter_upwards [hae] with y hy; rw [hy])
      rw [hμ, integral_withDensityReal_eq ρ hρm hρ0] at e1
      rw [← e1]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      ring
    refine q66_bootstrap hd hs0 hs hρ hφ β (-pair μ φ + β * m) hrc (fun x => ?_)
    rw [hGc' x]
    simp only [hr, projMean]
    ring
  · rw [hKr]
    simp only [hr]
    ring

end HRS.Q66

end
