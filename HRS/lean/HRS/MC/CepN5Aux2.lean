import HRS.Stochastic.Brownian

/-!
# Packet N5, helper 2: the Brownian filtration shifted to start at time `t₁`

`n5_shF ℱ t₁` is the filtration `s ↦ ℱ (t₁ + max s 0)` (constant `ℱ t₁` on `s ≤ 0`) and
`n5_shW B t₁ s = B (t₁ + s) - B t₁`; this is a Brownian filtration started at time `0`, so that the
initial value `G t₁` becomes `𝒢 0`-measurable.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MC.CepN5

open HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The shifted filtration. -/
def n5_shF (ℱ : Filtration ℝ mΩ) (t₁ : ℝ) : Filtration ℝ mΩ where
  seq s := ℱ (t₁ + max s 0)
  mono' := fun a b hab => ℱ.mono (by gcongr)
  le' := fun s => ℱ.le _

theorem n5_shF_apply (ℱ : Filtration ℝ mΩ) (t₁ s : ℝ) : n5_shF ℱ t₁ s = ℱ (t₁ + max s 0) := rfl

/-- The shifted Brownian motion. -/
def n5_shW (B : ℝ≥0 → Ω → ℝ) (t₁ : ℝ≥0) : ℝ≥0 → Ω → Fin 1 → ℝ :=
  fun s ω _ => B (t₁ + s) ω - B t₁ ω

theorem n5_shF_nn (ℱ : Filtration ℝ mΩ) (t₁ s : ℝ≥0) :
    n5_shF ℱ (t₁ : ℝ) (s : ℝ) = ℱ (((t₁ + s : ℝ≥0)) : ℝ) := by
  rw [n5_shF_apply, max_eq_left (NNReal.coe_nonneg s)]; push_cast; rfl

theorem n5_shift_brownian {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianFiltration P ℱ (fun t ω (_ : Fin 1) => B t ω)) (t₁ : ℝ≥0) :
    IsBrownianFiltration P (n5_shF ℱ (t₁ : ℝ)) (n5_shW B t₁) where
  complete := fun t s hs hP => hB.complete _ s hs hP
  adapted := fun t => by
    rw [n5_shF_nn]
    have h1 : Measurable[ℱ (((t₁ + t : ℝ≥0)) : ℝ)] (fun ω => B (t₁ + t) ω) := by
      have := (hB.adapted (t₁ + t))
      exact (measurable_pi_apply (0 : Fin 1)).comp this
    have h2 : Measurable[ℱ (((t₁ + t : ℝ≥0)) : ℝ)] (fun ω => B t₁ ω) := by
      have := (hB.adapted t₁)
      have h3 := (measurable_pi_apply (0 : Fin 1)).comp this
      exact h3.mono (ℱ.mono (by push_cast; linarith [t.2])) le_rfl
    refine @measurable_pi_lambda _ _ _ (ℱ (((t₁ + t : ℝ≥0)) : ℝ)) _ _ (fun _ => ?_)
    exact h1.sub h2
  zero := fun ω => by
    funext k
    simp [n5_shW]
  cont := fun ω => by
    refine continuous_pi fun k => ?_
    have := (continuous_apply (0 : Fin 1)).comp (hB.cont ω)
    exact (this.comp (continuous_const.add continuous_id)).sub continuous_const
  indep_incr := fun s t hst => by
    have h := hB.indep_incr (t₁ + s) (t₁ + t) (by gcongr)
    rw [n5_shF_nn]
    have e : (fun ω => n5_shW B t₁ t ω - n5_shW B t₁ s ω) =
        fun ω => (fun k : Fin 1 => B (t₁ + t) ω) - (fun k : Fin 1 => B (t₁ + s) ω) := by
      funext ω k; simp [n5_shW]
    rw [e]
    exact h
  gaussian_incr := fun s t hst => by
    have h := hB.gaussian_incr (t₁ + s) (t₁ + t) (by gcongr)
    have e : (fun ω => n5_shW B t₁ t ω - n5_shW B t₁ s ω) =
        fun ω => (fun k : Fin 1 => B (t₁ + t) ω) - (fun k : Fin 1 => B (t₁ + s) ω) := by
      funext ω k; simp [n5_shW]
    rw [e]
    have e2 : (t₁ + t) - (t₁ + s) = t - s := by
      rw [add_tsub_add_eq_tsub_left]
    rw [e2] at h
    exact h

end HRS.MC.CepN5
