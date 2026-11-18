import HRS.MS.S113EndAux22

/-!
# S11.3 endpoint (worker S11X), part 23: the time derivative of the modulated Gibbs density at a fixed configuration

`s113x_Q_timederiv`: `∂_τ q_N^τ(X) = q_N^t(X) (-κ' - βN(-N⁻¹ ∑_a Γ'(X_a) + ½A') + ∑_a D(X_a)/ρ_t(X_a))` for `ρ_τ` in a Gaussian family
with `κ' = d/dτ log K_{N,β}(μ^τ)`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113BD

open HRS HRS.Whole

variable {d N : ℕ}

theorem s113x_energyPairing_eq {ρ : Euc d → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (s : ℝ) :
    HRS.Whole.energyPairing (rieszKernel d s) (HRS.Whole.withDensityReal ρ) (HRS.Whole.withDensityReal ρ) =
      ∫ x, ρ x * ∫ z, rieszKernel d s z * ρ (x - z) := by
  unfold HRS.Whole.energyPairing
  rw [HRS.MP.RdRem.mrr_integral_withDensityReal ρ hρm hρ0]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ρ x * HRS.Whole.convMeasure (rieszKernel d s) (HRS.Whole.withDensityReal ρ) x = _
  rw [s113x_convMeasure_eq hρm hρ0]

theorem s113x_Fm_eq {ρ : Euc d → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (s : ℝ) (X : EucConfig d N) :
    rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) =
      (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, rieszKernel d s (X i - X j) -
        (1 / (N : ℝ)) * ∑ a, (∫ z, rieszKernel d s z * ρ (X a - z)) +
        (1 / 2) * ∫ x, ρ x * ∫ z, rieszKernel d s z * ρ (x - z) := by
  unfold rieszModulatedEnergy HRS.Whole.modulatedEnergy
  rw [s113x_energyPairing_eq hρm hρ0 s]
  simp only [s113x_convMeasure_eq hρm hρ0]

theorem s113x_Q_timederiv {s β : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ρ D : ℝ → Euc d → ℝ} {c B : ℝ}
    (H : S113XGauss ρ D c B) (hpos : ∀ τ, 0 < τ → ∀ y, 0 < ρ τ y)
    (hK : ∀ τ, 0 < τ → 0 < HRS.Whole.gibbsNormalizer (rieszKernel d s) N β (HRS.Whole.withDensityReal (ρ τ)))
    {t : ℝ} (ht : 0 < t) {κ' : ℝ}
    (hκ : HasDerivAt (fun τ => Real.log (HRS.Whole.gibbsNormalizer (rieszKernel d s) N β (HRS.Whole.withDensityReal (ρ τ)))) κ' t)
    (X : EucConfig d N) :
    HasDerivAt (fun τ => movQDensity d s β N (ρ τ) X)
      (movQDensity d s β N (ρ t) X * (-κ' - β * N * (-(1 / (N : ℝ)) * ∑ a, (∫ z, rieszKernel d s z * D t (X a - z)) +
          (1 / 2) * ∫ x, (D t x * (∫ z, rieszKernel d s z * ρ t (x - z)) + ρ t x * ∫ z, rieszKernel d s z * D t (x - z))) +
        ∑ a, D t (X a) / ρ t (X a))) t := by
  have hevt : ∀ᶠ τ in 𝓝 t, 0 < τ := Ioi_mem_nhds ht
  -- the normalizer
  have hKinv : HasDerivAt (fun τ => (HRS.Whole.gibbsNormalizer (rieszKernel d s) N β (HRS.Whole.withDensityReal (ρ τ)))⁻¹)
      (-κ' * (HRS.Whole.gibbsNormalizer (rieszKernel d s) N β (HRS.Whole.withDensityReal (ρ t)))⁻¹) t := by
    have h1 : HasDerivAt (fun τ => Real.exp (-Real.log (HRS.Whole.gibbsNormalizer (rieszKernel d s) N β (HRS.Whole.withDensityReal (ρ τ)))))
        (Real.exp (-Real.log (HRS.Whole.gibbsNormalizer (rieszKernel d s) N β (HRS.Whole.withDensityReal (ρ t)))) * (-κ')) t :=
      (hκ.neg).exp
    refine (h1.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [hevt] with τ hτ
      simp only [Real.exp_neg, Real.exp_log (hK τ hτ)]
    · rw [Real.exp_neg, Real.exp_log (hK t ht)]
      ring
  -- the energy
  have hFm : HasDerivAt (fun τ => rieszModulatedEnergy d s X (HRS.Whole.withDensityReal (ρ τ)))
      (-(1 / (N : ℝ)) * ∑ a, (∫ z, rieszKernel d s z * D t (X a - z)) +
        (1 / 2) * ∫ x, (D t x * (∫ z, rieszKernel d s z * ρ t (x - z)) + ρ t x * ∫ z, rieszKernel d s z * D t (x - z))) t := by
    have hG : ∀ a ∈ (Finset.univ : Finset (Fin N)),
        HasDerivAt (fun τ => ∫ z, rieszKernel d s z * ρ τ (X a - z)) (∫ z, rieszKernel d s z * D t (X a - z)) t :=
      fun a _ => s113x_Gamma_hasDerivAt hd hs0 hsd H ht (X a)
    have hGs := (HasDerivAt.fun_sum hG).const_mul (-(1 / (N : ℝ)))
    have hA := (s113x_A_hasDerivAt hd hs0 hsd H ht).const_mul (1 / 2 : ℝ)
    have h2 := (hGs.add hA).const_add ((1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, rieszKernel d s (X i - X j))
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [hevt] with τ hτ
    rw [s113x_Fm_eq (H.rho_cont τ hτ).measurable (H.rho_nn τ hτ) s X]
    simp only [Pi.add_apply]
    ring
  have hE : HasDerivAt (fun τ => Real.exp (-β * N * rieszModulatedEnergy d s X (HRS.Whole.withDensityReal (ρ τ))))
      (Real.exp (-β * N * rieszModulatedEnergy d s X (HRS.Whole.withDensityReal (ρ t))) * (-β * N *
        (-(1 / (N : ℝ)) * ∑ a, (∫ z, rieszKernel d s z * D t (X a - z)) +
          (1 / 2) * ∫ x, (D t x * (∫ z, rieszKernel d s z * ρ t (x - z)) + ρ t x * ∫ z, rieszKernel d s z * D t (x - z))))) t :=
    (hFm.const_mul (-β * N)).exp
  -- the product of densities
  have hP : HasDerivAt (fun τ => ∏ a, ρ τ (X a))
      ((∏ a, ρ t (X a)) * ∑ a, D t (X a) / ρ t (X a)) t := by
    have hprod : HasDerivAt (fun τ => ∏ a, ρ τ (X a))
        (∑ a, (∏ j ∈ Finset.univ.erase a, ρ t (X j)) • D t (X a)) t :=
      HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Fin N))) (f := fun a τ => ρ τ (X a))
        (f' := fun a => D t (X a)) (x := t) (fun a _ => H.deriv t ht (X a))
    refine hprod.congr_deriv ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hne : ρ t (X a) ≠ 0 := (hpos t ht (X a)).ne'
    rw [smul_eq_mul, ← Finset.mul_prod_erase Finset.univ (fun b => ρ t (X b)) (Finset.mem_univ a)]
    field_simp
  have hcomb := (hKinv.mul hE).mul hP
  unfold movQDensity
  refine hcomb.congr_deriv ?_
  simp only [Pi.mul_apply]
  ring

end HRS.MS.S113BD

end
