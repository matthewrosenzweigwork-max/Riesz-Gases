import HRS.MS.S82RM3

/-!
# S8.2 R02 (S82R), M4: the one-site step of the weighted Lipschitz transfer
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ENNReal BigOperators Classical

namespace HRS.MS.S82R
open HRS.External

variable {E : Type*} [MeasurableSpace E] {n : ℕ}

/-- `S.G` has the density `κ` with respect to `μ`. -/
structure s82r_Dens (μ : Measure E) (S : Spec E n) (κ : Fin n → (Fin n → E) → E → ℝ) : Prop where
  eq : ∀ i x, S.G i x = μ.withDensity (fun z => ENNReal.ofReal (κ i x z))
  nonneg : ∀ i x z, 0 ≤ κ i x z
  meas : ∀ i x, Measurable (κ i x)

lemma s82r_Dens.site {μ : Measure E} {S : Spec E n} {κ : Fin n → (Fin n → E) → E → ℝ}
    (h : s82r_Dens μ S κ) (i : Fin n) (x : Fin n → E) (F : (Fin n → E) → ℝ) :
    S.site i F x = ∫ z, F (update x i z) * κ i x z ∂μ := by
  unfold Spec.site
  rw [h.eq i x, integral_withDensity_eq_integral_toReal_smul (f := fun z => ENNReal.ofReal (κ i x z))
    (ENNReal.measurable_ofReal.comp (h.meas i x)) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (h.nonneg i x z)]
  ring

lemma s82r_Dens.one {μ : Measure E} {S : Spec E n} {κ : Fin n → (Fin n → E) → E → ℝ}
    (h : s82r_Dens μ S κ) (i : Fin n) (x : Fin n → E) :
    Integrable (κ i x) μ ∧ ∫ z, κ i x z ∂μ = 1 := by
  have hp : S.G i x Set.univ = 1 := (S.isMarkov i).isProbabilityMeasure x |>.measure_univ
  rw [h.eq i x, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hp
  have hi : Integrable (κ i x) μ := by
    refine ⟨(h.meas i x).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (h.nonneg i x))]
    rw [hp]; exact ENNReal.one_lt_top
  refine ⟨hi, ?_⟩
  have := ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (h.nonneg i x))
  rw [hp] at this
  have h1 : ENNReal.ofReal (∫ z, κ i x z ∂μ) = ENNReal.ofReal 1 := by rw [this]; simp
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg (h.nonneg i x)) zero_le_one).1 h1

structure s82r_Hyp (μ : Measure E) (Γ : E → E → ℝ) (b : E → ℝ)
    (κ κ' : Fin n → (Fin n → E) → E → ℝ) : Prop where
  Γm : Measurable (uncurry Γ)
  Γ0 : ∀ z u, 0 ≤ Γ z u
  Γb : ∃ G0 : ℝ, ∀ z u, Γ z u ≤ G0
  bm : Measurable b
  b0 : ∀ z, 0 ≤ b z
  bb : ∃ B : ℝ, ∀ z, b z ≤ B
  D : ∀ i x y z, |κ i x z - κ' i y z| ≤ b z +
    ∑ ℓ ∈ Finset.univ.erase i, if x ℓ = y ℓ then 0 else Γ z (x ℓ) + Γ z (y ℓ)

end HRS.MS.S82R

end
