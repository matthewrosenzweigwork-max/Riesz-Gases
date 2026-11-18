import HRS.MS.UniqE2b

/-!
# E2 of `UniqPlan.md`, part 3: joint measurability of `z_ε` and the cell energy identity

`e2_energy_identity`: for a forward solution `z` with `LocMass B (z τ)` on `[0,t]`, the flow bundle `FlowBundle`
of `b σ = meanFieldDriftW D (ρ (t-σ))`, `ε > 0`, every centre `c` and every `τ ∈ [0,t]`:
`∫ ς_c^τ z_ε(τ)² = ∫_{[0,τ]} ( ∫ (b·∇ς_c^σ) z_ε(σ)² + 2 ⟨𝓛^σ z(σ), η_ε * (ς_c^σ z_ε(σ))⟩ ) dσ`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal Interval ContDiff

namespace HRS.MS.UniqE2

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqT3
  HRS.MS.UniqE1 HRS.MS.UniqC3

variable {d : ℕ}

/-- Joint a.e.-measurability of `(σ,x) ↦ z_ε(σ,x)` on `[0,τ] × ℝ^d` from continuity in each variable. -/
theorem e2_moll_aesm {ε : ℝ} {t τ : ℝ} (ht0 : 0 ≤ t) (hτ : τ ≤ t) {z : ℝ → Euc d → ℝ}
    (hcont : ∀ x, ContinuousOn (fun σ => moll d ε (z σ) x) (Icc 0 t))
    (hsm : ∀ σ ∈ Icc (0 : ℝ) t, Continuous (moll d ε (z σ))) :
    AEStronglyMeasurable (fun p : ℝ × Euc d => moll d ε (z p.1) p.2)
      ((volume.restrict (Icc 0 τ)).prod (volume : Measure (Euc d))) := by
  set cl : ℝ → ℝ := fun σ => max 0 (min σ t) with hcl
  have hclc : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  have hclm : ∀ σ, cl σ ∈ Icc (0 : ℝ) t := fun σ =>
    ⟨le_max_left _ _, max_le ht0 (min_le_right _ _)⟩
  have hU : Measurable (Function.uncurry fun (σ : ℝ) (x : Euc d) => moll d ε (z (cl σ)) x) := by
    refine measurable_uncurry_of_continuous_of_measurable
      (fun x => (hcont x).comp_continuous hclc hclm) (fun σ => ?_)
    exact (hsm _ (hclm σ)).measurable
  have hae : ∀ᵐ p ∂((volume.restrict (Icc 0 τ)).prod (volume : Measure (Euc d))),
      p.1 ∈ Icc (0 : ℝ) τ :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  refine hU.aestronglyMeasurable.congr ?_
  filter_upwards [hae] with p hp
  have : cl p.1 = p.1 := by
    simp only [hcl]
    rw [min_eq_left (hp.2.trans hτ), max_eq_right hp.1]
  simp only [Function.uncurry, this]

end HRS.MS.UniqE2
