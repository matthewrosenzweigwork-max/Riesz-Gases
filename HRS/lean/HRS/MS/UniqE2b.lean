import HRS.MS.UniqE2

/-!
# E2 of `UniqPlan.md`, part 2: the pointwise-in-`x` identity and the Fubini swap

For a family `ς(σ,x)` that is `C¹` in `σ ∈ [0,t]` for each `x` (derivative `ς'`, continuous in `σ`),
and a forward solution with `f_ε(·,x)` integrable:
`ς(τ,x) z_ε(τ,x)² = ∫_{[0,τ]} ( ς'(σ,x) z_ε(σ,x)² + 2 ς(σ,x) z_ε(σ,x) f_ε(σ,x) ) dσ` for **every** `x`.
`e2_fubini` swaps `∫ dx` and `∫_{[0,τ]} dσ` for an integrand supported (in `x`) in a fixed ball.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal Interval ContDiff

namespace HRS.MS.UniqE2

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqT3
  HRS.MS.UniqE1

variable {d : ℕ}

theorem e2_pointwise {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} {t : ℝ} {z : ℝ → Euc d → ℝ} {ε : ℝ}
    (hε : 0 < ε) (hz : IsForwardDistSolutionW D ρ t z)
    (hint : ∀ x, IntegrableOn (fun σ => fEps D ρ t z ε σ x) (Icc 0 t))
    {ς ς' : ℝ → Euc d → ℝ}
    (hς : ∀ x, ∀ σ ∈ Icc (0 : ℝ) t, HasDerivWithinAt (fun σ => ς σ x) (ς' σ x) (Icc 0 t) σ)
    (hς' : ∀ x, ContinuousOn (fun σ => ς' σ x) (Icc 0 t)) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) t)
    (x : Euc d) :
    ς τ x * (moll d ε (z τ) x) ^ 2 = ∫ σ in Icc 0 τ,
      (ς' σ x * (moll d ε (z σ) x) ^ 2 +
        2 * (ς σ x * moll d ε (z σ) x * fEps D ρ t z ε σ x)) := by
  have hrep : ∀ τ ∈ Icc (0 : ℝ) t, moll d ε (z τ) x = ∫ σ in (0 : ℝ)..τ, fEps D ρ t z ε σ x := by
    intro τ hτ
    rw [e1_time_rep hz hε hτ x, intervalIntegral.integral_of_le hτ.1, integral_Icc_eq_integral_Ioc]
  have h := e2_prod (hς x) (hς' x) (hint x) hτ
  rw [← hrep τ hτ, intervalIntegral.integral_of_le hτ.1] at h
  rw [h, integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Ioc fun σ hσ => ?_
  have hσ' : σ ∈ Icc (0 : ℝ) t := ⟨hσ.1.le, hσ.2.trans hτ.2⟩
  rw [← hrep σ hσ']
  ring

/-- `Icc 0 τ ×ˢ univ` is dominated by the product measure of the restricted time interval. -/
theorem e2_prod_le {t τ : ℝ} (hτ : τ ≤ t) :
    (volume.restrict (Icc 0 τ)).prod (volume : Measure (Euc d)) ≤
      (volume.prod (volume : Measure (Euc d))).restrict (Icc 0 t ×ˢ univ) := by
  have := Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Euc d)))
    (Icc 0 τ) univ
  rw [Measure.restrict_univ] at this
  rw [this]
  exact Measure.restrict_mono (prod_mono (Icc_subset_Icc le_rfl hτ) subset_rfl) le_rfl

theorem e2_ae_of_contOn {t τ : ℝ} (hτ : τ ≤ t) {F : ℝ × Euc d → ℝ}
    (hF : ContinuousOn F (Icc 0 t ×ˢ univ)) :
    AEStronglyMeasurable F ((volume.restrict (Icc 0 τ)).prod (volume : Measure (Euc d))) :=
  (hF.aestronglyMeasurable (measurableSet_Icc.prod MeasurableSet.univ)).mono_measure
    (e2_prod_le hτ)

/-- Fubini on `[0,τ] × B̄(0,R)`. -/
theorem e2_fubini {τ R M : ℝ} {G : ℝ → Euc d → ℝ}
    (hG : AEStronglyMeasurable (fun p : ℝ × Euc d => G p.1 p.2)
      ((volume.restrict (Icc 0 τ)).prod (volume : Measure (Euc d))))
    (hout : ∀ σ ∈ Icc (0 : ℝ) τ, ∀ x : Euc d, R < ‖x‖ → G σ x = 0)
    (hin : ∀ σ ∈ Icc (0 : ℝ) τ, ∀ x : Euc d, ‖x‖ ≤ R → |G σ x| ≤ M) :
    ∫ x, ∫ σ in Icc 0 τ, G σ x = ∫ σ in Icc 0 τ, ∫ x, G σ x := by
  set g : Euc d → ℝ := (closedBall (0 : Euc d) R).indicator (fun _ => |M|) with hg
  have hgi : Integrable g volume :=
    (integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const (isCompact_closedBall _ _).measure_lt_top.ne)
  have hbound : Integrable (fun p : ℝ × Euc d => (1 : ℝ) * g p.2)
      ((volume.restrict (Icc 0 τ)).prod (volume : Measure (Euc d))) :=
    (integrable_const (1 : ℝ)).mul_prod hgi
  have hae : ∀ᵐ p ∂((volume.restrict (Icc 0 τ)).prod (volume : Measure (Euc d))),
      p.1 ∈ Icc (0 : ℝ) τ := Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  have hint : Integrable (fun p : ℝ × Euc d => G p.1 p.2)
      ((volume.restrict (Icc 0 τ)).prod (volume : Measure (Euc d))) := by
    refine hbound.mono' hG ?_
    filter_upwards [hae] with p hp
    by_cases hx : ‖p.2‖ ≤ R
    · have : g p.2 = |M| := by
        rw [hg, indicator_of_mem (by simpa [mem_closedBall, dist_zero_right] using hx)]
      rw [this, one_mul, Real.norm_eq_abs]
      exact (hin p.1 hp p.2 hx).trans (le_abs_self _)
    · rw [not_le] at hx
      rw [hout p.1 hp p.2 hx]; simp only [norm_zero]
      rw [one_mul]
      exact indicator_nonneg (fun _ _ => abs_nonneg _) _
  have hswap : Integrable (Function.uncurry fun (x : Euc d) (σ : ℝ) => G σ x)
      (volume.prod (volume.restrict (Icc 0 τ))) := by
    have := hint.swap
    exact this
  exact integral_integral_swap hswap

end HRS.MS.UniqE2
