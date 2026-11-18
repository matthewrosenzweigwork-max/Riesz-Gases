import HRS.MC.E214PD

/-!
# E214N2: the Wick field of the time-shifted stationary field (`shifted_wick`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214N

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan

variable {d : ℕ}

section Wick

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (sd : StatDatum S β₀ m hE)

/-- The density of the stationary datum is constant in time. -/
theorem stat_rho_const (t t' : ℝ) : sd.Ss.ρ t = sd.Ss.ρ t' := by
  have h : (regime sd.Ss S.β sd.hEs).ρ = fun _ => (regime S β₀ hE).ρβ := sd.hρ
  have e : ∀ u, sd.Ss.ρ u = (regime sd.Ss S.β sd.hEs).ρ u := fun u => rfl
  rw [e t, e t', h]

theorem shifted_wick_proof (gds : GaussData sd.Ss S.β sd.hEs) (h : ℝ) (hh : 0 ≤ h) :
    Measurable (Function.uncurry fun u ω => gds.B (h + u) ω) ∧
    (∀ᵐ t ∂(volume.restrict (Set.Ici (0 : ℝ))),
      IsWickQuadraticField sd.Ss.s gds.P₀ (fun ω => gds.η (h + t) ω) (withDensityReal (sd.Ss.ρ t)) (gds.B (h + t))) ∧
    (∀ Rw : ℝ, 0 < Rw → ∀ a : ℝ, 0 ≤ a →
      ∀ᵐ ω ∂gds.P₀, MemLp (fun t => gds.B (h + (a + t)) ω) 2 (volume.restrict (Set.Icc (0 : ℝ) Rw))) := by
  refine ⟨?_, ?_, ?_⟩
  · have hm : Measurable (fun p : ℝ × gds.Ω₀ => (h + p.1, p.2)) :=
      (measurable_const.add measurable_fst).prodMk measurable_snd
    exact gds.B_meas.comp hm
  · have h1 := gds.B_wick
    rw [ae_restrict_iff' measurableSet_Ici] at h1 ⊢
    have h2 : ∀ᵐ t ∂(volume : Measure ℝ), h + t ∈ Set.Ici (0 : ℝ) →
        IsWickQuadraticField sd.Ss.s gds.P₀ (fun ω => gds.η (h + t) ω)
          (withDensityReal (sd.Ss.ρ (h + t))) (gds.B (h + t)) := by
      have := (measurePreserving_add_left (volume : Measure ℝ) h).quasiMeasurePreserving.ae h1
      filter_upwards [this] with t ht using ht
    filter_upwards [h2] with t ht ht0
    have := ht (by simp at ht0 ⊢; linarith)
    rwa [stat_rho_const sd (h + t) t] at this
  · intro Rw hRw a ha
    filter_upwards [gds.B_L2 Rw hRw (h + a) (add_nonneg hh ha)] with ω hω
    simpa only [add_assoc] using hω

end Wick

end HRS.MC.E214N

end
