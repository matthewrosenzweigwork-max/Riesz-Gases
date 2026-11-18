import HRS.MS.S113EndAux28
import DGRHS.Attractive.SourceUniform
import DGRHS.CLT.SourceRawEnergy

/-!
# S11.3 endpoint (worker S11X), part 29: the attractive logarithmic kernel in the `DGRHS` convention (whole space)

Whole-space port of `HRS/Equilibrium/PreparationAttractive.lean` (translation between the two conventions): `W(x,y) = -g(x-y)`,
the centred kernel of `DGRHS` is minus the centred logarithmic kernel, and `F_N^g = - sourceCanonicalModulatedEnergy`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S113BD

open HRS.Whole
open HRS (Euc)

variable {d : ℕ} {C₁ a₀ : ℝ}

/-- Kernel of `DGRHS` for the attractive logarithm: `W(x, y) = -g(x - y)`. -/
def s113x_Wk (g : Euc d → ℝ) (x y : Euc d) : ℝ := -g (x - y)

section Port

variable {g : Euc d → ℝ} {μ : Measure (Euc d)}

theorem s113x_Wk_symm (hg : ∀ z, g (-z) = g z) (x y : Euc d) : s113x_Wk g x y = s113x_Wk g y x := by
  unfold s113x_Wk
  rw [← hg (x - y), neg_sub]

theorem s113x_potential_eq (x : Euc d) : DGRHS.potential μ (s113x_Wk g) x = -HRS.Whole.convMeasure g μ x := by
  unfold DGRHS.potential s113x_Wk HRS.Whole.convMeasure
  rw [integral_neg]

theorem s113x_secondPotential_eq (hg : ∀ z, g (-z) = g z) (y : Euc d) :
    DGRHS.secondPotential μ (s113x_Wk g) y = -HRS.Whole.convMeasure g μ y := by
  unfold DGRHS.secondPotential s113x_Wk HRS.Whole.convMeasure
  rw [integral_neg]
  congr 2
  funext x
  rw [← hg (x - y), neg_sub]

theorem s113x_pairIntegral_eq [IsProbabilityMeasure μ]
    (hI : Integrable (fun p : Euc d × Euc d => g (p.1 - p.2)) (μ.prod μ)) :
    ∫ z, s113x_Wk g z.1 z.2 ∂μ.prod μ = -HRS.Whole.energyPairing g μ μ := by
  unfold s113x_Wk HRS.Whole.energyPairing
  rw [integral_neg, integral_prod _ hI]

theorem s113x_interactionEnergy_eq [IsProbabilityMeasure μ]
    (hI : Integrable (fun p : Euc d × Euc d => g (p.1 - p.2)) (μ.prod μ)) :
    DGRHS.interactionEnergy μ (s113x_Wk g) = -(1 / 2) * HRS.Whole.energyPairing g μ μ := by
  unfold DGRHS.interactionEnergy
  rw [s113x_pairIntegral_eq hI]
  ring

/-- The centred kernel of `DGRHS` for `W = -g(x - y)` is minus the centred kernel `g(x-y) - g*μ(x) - g*μ(y) + ∬g`. -/
theorem s113x_centeredKernel_eq [IsProbabilityMeasure μ] (hg : ∀ z, g (-z) = g z)
    (hI : Integrable (fun p : Euc d × Euc d => g (p.1 - p.2)) (μ.prod μ)) (x y : Euc d) :
    DGRHS.centeredKernel μ (s113x_Wk g) x y =
      -(g (x - y) - HRS.Whole.convMeasure g μ x - HRS.Whole.convMeasure g μ y +
        HRS.Whole.energyPairing g μ μ) := by
  unfold DGRHS.centeredKernel
  rw [s113x_potential_eq, s113x_secondPotential_eq hg, s113x_pairIntegral_eq hI]
  unfold s113x_Wk
  ring

theorem s113x_offDiagonalSum_eq {N : ℕ} (h : Euc d → Euc d → ℝ) (X : EucConfig d N) :
    DGRHS.CanonicalVariance.offDiagonalSum (Function.uncurry h) X =
      ∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j) := by
  classical
  unfold DGRHS.CanonicalVariance.offDiagonalSum
  have hoff : (Finset.univ : Finset (Fin N)).offDiag =
      (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin N × Fin N => p.1 ≠ p.2) := by
    ext p; simp [Finset.mem_offDiag]
  rw [hoff, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.uncurry]
  rw [← Finset.sum_filter, Finset.filter_ne]

/-- `F_N^g = -F_N^W` with the `DGRHS` source energy. -/
theorem s113x_modulatedEnergy_eq [IsProbabilityMeasure μ] (hg : ∀ z, g (-z) = g z)
    (hI : Integrable (fun p : Euc d × Euc d => g (p.1 - p.2)) (μ.prod μ))
    {N : ℕ} (hN : 0 < N) (X : EucConfig d N) :
    HRS.Whole.modulatedEnergy g X μ =
      -DGRHS.CLT.sourceCanonicalModulatedEnergy
        (fun p => DGRHS.centeredKernel μ (s113x_Wk g) p.1 p.2)
        (DGRHS.potential μ (s113x_Wk g)) (DGRHS.interactionEnergy μ (s113x_Wk g)) N X := by
  rw [DGRHS.CLT.sourceCanonicalModulatedEnergy_raw μ (s113x_Wk g) (s113x_Wk_symm hg) N hN X]
  have hoff : DGRHS.CanonicalVariance.offDiagonalSum (Function.uncurry (s113x_Wk g)) X =
      -∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j) := by
    rw [s113x_offDiagonalSum_eq]
    simp only [s113x_Wk, Finset.sum_neg_distrib]
  rw [hoff]
  rw [s113x_interactionEnergy_eq hI]
  simp only [s113x_potential_eq, Finset.sum_neg_distrib]
  unfold HRS.Whole.modulatedEnergy
  ring

end Port


section Bounds

/-- `0 ≤ ∫ ℓ dμ ≤ 2∫Φ` for a density under the Gaussian envelope. -/
theorem s113x_ell_integral_bound (hC : 0 ≤ C₁) (ha : 0 < a₀) {ρ : Euc d → ℝ} (hm : Measurable ρ)
    (hρ : ∀ x, 0 ≤ ρ x ∧ ρ x ≤ C₁ * Real.exp (-a₀ * ‖x‖ ^ 2)) :
    0 ≤ ∫ x, q33b_ell x ∂(HRS.Whole.withDensityReal ρ) ∧
      ∫ x, q33b_ell x ∂(HRS.Whole.withDensityReal ρ) ≤ 2 * ∫ x : Euc d, q33b_Phi C₁ a₀ x := by
  refine ⟨integral_nonneg fun x => q33b_ell_nonneg x, ?_⟩
  rw [HRS.MP.RdRem.mrr_integral_withDensityReal ρ hm (fun x => (hρ x).1)]
  have hΦ := (q33b_Phi_integrable (d := d) hC ha).const_mul 2
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => mul_nonneg (hρ x).1 (q33b_ell_nonneg x)) hΦ
    (Filter.Eventually.of_forall fun x => ?_)).trans (le_of_eq (integral_const_mul _ _))
  have h1 := q33b_ell_le (d := d) (ε := 1 / 2) (by norm_num) (by norm_num) x
  unfold q33b_Phi
  calc ρ x * q33b_ell x ≤ (C₁ * Real.exp (-a₀ * ‖x‖ ^ 2)) * q33b_ell x :=
        mul_le_mul_of_nonneg_right (hρ x).2 (q33b_ell_nonneg x)
    _ ≤ (C₁ * Real.exp (-a₀ * ‖x‖ ^ 2)) * (2 * (1 + ‖x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC (Real.exp_pos _).le)
    _ = 2 * (C₁ * ((1 + ‖x‖ ^ 2) * Real.exp (-a₀ * ‖x‖ ^ 2))) := by ring

end Bounds

end HRS.MS.S113BD

end
