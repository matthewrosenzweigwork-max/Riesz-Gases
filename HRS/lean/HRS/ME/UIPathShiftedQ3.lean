import HRS.ME.UIPath
import HRS.MD.EQLawPath
import HRS.Main.MeanPartMetricEval

/-!
# Proof packet SQ3 of `HRS.ui_path_shifted` (shifted-window clause): the a.s. identity on the particle side

Proof of `windowGibbs_fidi_ae_eq` (statement copied verbatim from `HRS/ME/UIPathShiftedSpec.lean`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.ME.UIPathShifted

open HRS HRS.Main

variable {d : ℕ}

/-- **Q3** (a.s. identity of the finite-dimensional vector on the particle side; scope note Q3).  For a process
with a.s. continuous coordinates, a probability measure `μ` and smooth tests `φ_a`, the test vector of the
Gibbs-centred window `windowGibbs m T u μ X` at times `ts a ∈ [0,T]` agrees `P`-a.e. with the vector
`linCoord μ (φ a) (X (u + ts a))` appearing in `ui_comparison`/`ui_qualitative` (so the window junk value `0`
is irrelevant: it lives on a null set).  Needs `d < 2m` (`etaE` continuous in the configuration, hence the
window is continuous a.s.) and `1 ≤ N`.  Route: a.s. continuity (as in `windowGibbs_aemeasurable`,
`eqlaw_continuous_ofMeasureDiff_empirical`), unfold `windowGibbs`/`PathSpace.at'`, then `mp_linCoord_eq_eval`
with `ν = μ₀ = μ` (the shift term `√N (pair μ ψ - pair μ ψ)` vanishes).  The transport of `TendstoInDistribution`
under a.e. equality is Mathlib's `TendstoInDistribution.congr`. -/
theorem windowGibbs_fidi_ae_eq {N : ℕ} (hN : 1 ≤ N) {m : ℝ} (hm : (d : ℝ) < 2 * m) (T u : ℝ)
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → Config d N)
    (hc : ∀ᵐ ω ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ω i)
    (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    (fun ω => (WithLp.toLp 2 fun a =>
        NegSobolev.eval ((windowGibbs m T u μ X ω).at' ⟨ts a, hts a⟩) (φ a) :
        EuclideanSpace ℝ (Fin p))) =ᵐ[P]
      (fun ω => (WithLp.toLp 2 fun a => linCoord μ (φ a) (X (u + ts a).toNNReal ω) :
        EuclideanSpace ℝ (Fin p))) := by
  have hη : Continuous fun Y : Config d N => etaE m Y μ :=
    (HRS.MD.EQLawPath.eqlaw_continuous_ofMeasureDiff_empirical hm μ hN).const_smul (Real.sqrt N)
  filter_upwards [hc] with ω hω
  have hcont : Continuous fun t : Set.Icc (0 : ℝ) T => etaE m (X (Real.toNNReal (u + t)) ω) μ := by
    refine hη.comp ?_
    refine continuous_pi fun i => ?_
    exact (hω i).comp (continuous_real_toNNReal.comp (continuous_const.add continuous_subtype_val))
  have hW : windowGibbs m T u μ X ω = ⟨_, hcont⟩ := by
    unfold windowGibbs
    exact dif_pos hcont
  have hval : ∀ a, NegSobolev.eval ((windowGibbs m T u μ X ω).at' ⟨ts a, hts a⟩) (φ a) =
      linCoord μ (φ a) (X (u + ts a).toNNReal ω) := by
    intro a
    have h1 := mp_linCoord_eq_eval hm hN μ μ (φ a) (hφ a) (X (Real.toNNReal (u + ts a)) ω)
    rw [h1, sub_self, mul_zero, add_zero, hW]
    rfl
  simp only [hval]

end HRS.ME.UIPathShifted
