import HRS.MS.R2InterpAux83

/-!
# S10.2 (worker S10R), part 84 (packet F5d): taking expectations in the duality identity

Abstract step: if a.s. `a τ = a 0 + c I τ - ∫_{[0,τ]} e(r,·) dr` for all `τ ∈ [0,t]` with `E I τ = 0`, `e` integrable on `[0,t] × Ω`, `a τ` integrable,
then the centred identity `a τ - E a τ = (a 0 - E a 0) + c I τ - ∫_{[0,τ]} (e(r,·) - E e(r,·)) dr` holds a.s. for all `τ ∈ [0,t]`.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

theorem s102_centered_identity {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {t c : ℝ}
    (a I : ℝ → Ω → ℝ) (e : ℝ × Ω → ℝ) (he : Integrable e ((volume.restrict (Icc (0 : ℝ) t)).prod P))
    (ha : ∀ τ ∈ Icc (0 : ℝ) t, Integrable (a τ) P) (hI : ∀ τ ∈ Icc (0 : ℝ) t, Integrable (I τ) P)
    (hI0 : ∀ τ ∈ Icc (0 : ℝ) t, ∫ ζ, I τ ζ ∂P = 0) (h0 : (0 : ℝ) ∈ Icc (0 : ℝ) t)
    (hid : ∀ᵐ ζ ∂P, ∀ τ ∈ Icc (0 : ℝ) t, a τ ζ = a 0 ζ + c * I τ ζ - ∫ r in Icc (0 : ℝ) τ, e (r, ζ)) :
    ∀ᵐ ζ ∂P, ∀ τ ∈ Icc (0 : ℝ) t,
      a τ ζ - ∫ ζ', a τ ζ' ∂P = (a 0 ζ - ∫ ζ', a 0 ζ' ∂P) + c * I τ ζ -
        ∫ r in Icc (0 : ℝ) τ, (e (r, ζ) - ∫ ζ', e (r, ζ') ∂P) := by
  have hint_ae : ∀ᵐ ζ ∂P, IntegrableOn (fun r => e (r, ζ)) (Icc (0 : ℝ) t) := he.prod_left_ae.mono fun ζ h => h
  have hee : IntegrableOn (fun r => ∫ ζ', e (r, ζ') ∂P) (Icc (0 : ℝ) t) := he.integral_prod_left
  filter_upwards [hid, hint_ae] with ζ hζ hζi τ hτ
  have hsub : Icc (0 : ℝ) τ ⊆ Icc 0 t := Icc_subset_Icc le_rfl hτ.2
  -- expectation of the identity at `τ`
  have hmono : (volume.restrict (Icc (0 : ℝ) τ)).prod P ≤ (volume.restrict (Icc (0 : ℝ) t)).prod P :=
    Measure.prod_mono (Measure.restrict_mono hsub le_rfl) le_rfl
  have heτ : Integrable e ((volume.restrict (Icc (0 : ℝ) τ)).prod P) := he.mono_measure hmono
  have hJ : Integrable (fun ζ' => ∫ r in Icc (0 : ℝ) τ, e (r, ζ')) P := heτ.integral_prod_right
  have hEτ : ∫ ζ', a τ ζ' ∂P = ∫ ζ', a 0 ζ' ∂P - ∫ ζ', (∫ r in Icc (0 : ℝ) τ, e (r, ζ')) ∂P := by
    have hcongr : ∫ ζ', a τ ζ' ∂P = ∫ ζ', (a 0 ζ' + c * I τ ζ' - ∫ r in Icc (0 : ℝ) τ, e (r, ζ')) ∂P :=
      integral_congr_ae (hid.mono fun ζ' h => h τ hτ)
    have h1 : Integrable (fun ζ' => a 0 ζ' + c * I τ ζ') P := (ha 0 h0).add ((hI τ hτ).const_mul c)
    rw [hcongr, integral_sub h1 hJ, integral_add (ha 0 h0) ((hI τ hτ).const_mul c), integral_const_mul, hI0 τ hτ]
    ring
  have hswap : ∫ ζ', (∫ r in Icc (0 : ℝ) τ, e (r, ζ')) ∂P = ∫ r in Icc (0 : ℝ) τ, ∫ ζ', e (r, ζ') ∂P := by
    exact integral_integral_swap (f := fun ζ' r => e (r, ζ')) heτ.swap
  have hζτ := hζ τ hτ
  have hint1 : IntegrableOn (fun r => e (r, ζ)) (Icc (0 : ℝ) τ) := hζi.mono_set hsub
  have hint2 : IntegrableOn (fun r => ∫ ζ', e (r, ζ') ∂P) (Icc (0 : ℝ) τ) := hee.mono_set hsub
  rw [integral_sub hint1 hint2, hEτ, hswap, hζτ]
  ring

end HRS.MS.R2Interp

end
