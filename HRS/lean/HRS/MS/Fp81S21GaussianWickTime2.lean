import HRS.MS.Fp81S21GaussianCrossDensity
import HRS.MS.Fp81S21PropagatorOsc
import HRS.MS.S21E_Int
import HRS.MS.R2S11Aux1
import HRS.MS.R2ChaosAux11
import HRS.MH.DualityRdB1Aux

/-! Packet 37Time: spatial clauses 2 and 4 of `CubicFormulaIntegrable`.
The moving propagator is used throughout. Thermal L² representatives are
transferred at each fixed time; no time measurability of χ is asserted.
Binder adjustment: the plan's `ha`, `hφ`, `hχ` are explicitly typed below.
The radius precedes δ, R and every supplied physical realization.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S21E HRS.MH.DualityRd

private theorem fp81s21_wick_time_memCb {d : ℕ} {C : WholeCoeff d}
    {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) {r : ℝ} (hr : r ∈ Icc 0 t) :
    MemCb 2 (f r) := by
  refine ⟨hf.c2 r hr, fun j hj => ?_⟩
  obtain ⟨B, hB⟩ := hf.bdd j hj
  exact ⟨B, by rintro _ ⟨x, rfl⟩; exact hB r hr x⟩

private theorem fp81s21_wick_time_thermal_L2
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    {Q : fp81s21_Physical35 p R} {a : ℝ}
    {τ : Fin 3 → Icc (0 : ℝ) p.T} {φ : Fin 3 → Euc p.d → ℝ}
    {χ : Fin 3 → ℝ → Euc p.d → ℝ}
    {hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)}
    (hcross : fp81s21_Cross37 Q a τ φ χ hφ)
    (i : Fin 3) {r : ℝ} (hr : r ∈ Icc 0 (a + p.T)) :
    MemLp (fun x => χ i r x / R.ρβ x) 2 (HRS.Whole.withDensityReal R.ρβ) := by
  obtain ⟨G, hG, hT, hX, u, hu⟩ := hcross
  have hac : HRS.Whole.withDensityReal R.ρβ ≪ (volume : Measure (Euc p.d)) :=
    withDensity_absolutelyContinuous _ _
  apply (Lp.memLp (u i r)).ae_eq
  filter_upwards [hac.ae_le ((hu i r hr).2)] with x hx
  rw [← hx]
  exact (mul_div_cancel_right₀ _ (u4_thermal_pos R.thermal x).ne').symm

private theorem fp81s21_wick_time_kernel_L2
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {f : Euc p.d → ℝ} (hf : MemCb 2 f) :
    MemLp (fun z : Euc p.d × Euc p.d =>
      commutatorKernel p.d p.s (gradient f) z.1 z.2) 2
      ((HRS.Whole.withDensityReal R.ρβ).prod (HRS.Whole.withDensityReal R.ρβ)) := by
  obtain ⟨B, hB, hbound⟩ := db1_iteratedFDeriv_bdd hf (j := 2) le_rfl
  have hd : Differentiable ℝ (gradient f) := db1_gradient_differentiable hf.1
  have hb : ∀ x, ‖fderiv ℝ (gradient f) x‖ ≤ B := by
    intro x
    refine (db1_fderiv_gradient_le hf.1 x).trans ?_
    have he : ‖fderiv ℝ (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
      rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    rw [he]
    exact hbound x
  have hk : IsBoundedPairKernel p.s ((p.s + 1) * B)
      (commutatorKernel p.d p.s (gradient f)) := by
    refine ⟨HRS.MS.Comm.comm_meas _ hd.continuous.measurable,
      HRS.MS.Comm.comm_symm _, ?_⟩
    intro x y hxy
    have hmv : ‖gradient f x - gradient f y‖ ≤ B * ‖x - y‖ :=
      Convex.norm_image_sub_le_of_norm_fderiv_le
        (fun z (_ : z ∈ (univ : Set (Euc p.d))) => hd z)
        (fun z _ => hb z) (convex_univ : Convex ℝ (univ : Set (Euc p.d)))
        (mem_univ y) (mem_univ x)
    exact HRS.MS.R2S11.s11_inner_bound p.hs0 (sub_ne_zero.mpr hxy) hB hmv
  obtain ⟨M, L, c, hρ, hG⟩ :=
    HRS.MS.R2S11.s11_thermal_round2 p.hd p.hs0 p.hs p.ha p.hβ R.thermal
  exact HRS.MS.R2Chaos.s94_env_memLp p.hd p.hs0 p.hs hρ hk

/-- Clause 2: the moving commutator times the two physical cross-densities
is absolutely integrable on product volume at every drift time. -/
theorem fp81s21_gaussian_wick_time_spatial_drift (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      ∀ Q : fp81s21_Physical35 p R, ∀ (a : ℝ) (_ha : 0 ≤ a)
        (τ : Fin 3 → Icc (0 : ℝ) p.T) (φ : Fin 3 → Euc p.d → ℝ)
        (χ : Fin 3 → ℝ → Euc p.d → ℝ)
        (_hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)),
      S21eChiClause p.d p.s p.a p.β p.γ R.ρ p.T a τ φ χ →
      let f := fun i r => propagatorW
        ((quadraticGradientDyn p.d p.s p.a p.β).coeff R.ρ) r (a + τ i) (φ i)
      ∀ i : Fin 3, ∀ r ∈ Icc (0 : ℝ) (a + τ i),
        Integrable (fun z : Euc p.d × Euc p.d =>
          commutatorKernel p.d p.s (gradient (f i r)) z.1 z.2 *
            χ (i + 1) r z.1 * χ (i + 2) r z.2) := by
  obtain ⟨δ₀, hδ₀, hhalf, hcross⟩ := fp81s21_gaussian_cross_density p
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hδle R Q a ha τ φ χ hφ hχ f i r hr
  have hC := hcross δ hδ hδle R Q a ha τ φ χ hφ hχ
  have hrH : r ∈ Icc (0 : ℝ) (a + p.T) :=
    ⟨hr.1, hr.2.trans (by linarith [(τ i).property.2])⟩
  let : IsProbabilityMeasure (HRS.Whole.withDensityReal R.ρβ) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  exact s21e_pair_integrable R.thermal.1.1.measurable (u4_thermal_pos R.thermal)
    (fp81s21_wick_time_thermal_L2 hC (i + 1) hrH)
    (fp81s21_wick_time_thermal_L2 hC (i + 2) hrH)
    (fp81s21_wick_time_kernel_L2 p R (fp81s21_wick_time_memCb
      (fp81s21_U_osc_test_classical p R (hφ i) (add_nonneg ha (τ i).property.1)) hr))

/-- Clause 4: the moving gradient pairing times the physical cross-density
is absolutely integrable in space at every admissible covariance time. -/
theorem fp81s21_gaussian_wick_time_spatial_cov (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      ∀ Q : fp81s21_Physical35 p R, ∀ (a : ℝ) (_ha : 0 ≤ a)
        (τ : Fin 3 → Icc (0 : ℝ) p.T) (φ : Fin 3 → Euc p.d → ℝ)
        (χ : Fin 3 → ℝ → Euc p.d → ℝ)
        (_hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)),
      S21eChiClause p.d p.s p.a p.β p.γ R.ρ p.T a τ φ χ →
      let f := fun i r => propagatorW
        ((quadraticGradientDyn p.d p.s p.a p.β).coeff R.ρ) r (a + τ i) (φ i)
      ∀ i : Fin 3, ∀ r ∈ Icc (0 : ℝ) (min (a + τ i) (a + τ (i + 1))),
        Integrable (fun x => inner ℝ (gradient (f i r) x)
          (gradient (f (i + 1) r) x) * χ (i + 2) r x) := by
  obtain ⟨δ₀, hδ₀, hhalf, hcross⟩ := fp81s21_gaussian_cross_density p
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hδle R Q a ha τ φ χ hφ hχ f i r hr
  have hC := hcross δ hδ hδle R Q a ha τ φ χ hφ hχ
  have hr1 : r ∈ Icc (0 : ℝ) (a + τ i) := ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
  have hr2 : r ∈ Icc (0 : ℝ) (a + τ (i + 1)) :=
    ⟨hr.1, hr.2.trans (min_le_right _ _)⟩
  have hrH : r ∈ Icc (0 : ℝ) (a + p.T) :=
    ⟨hr.1, hr1.2.trans (by linarith [(τ i).property.2])⟩
  have hf (j : Fin 3) (hrj : r ∈ Icc (0 : ℝ) (a + τ j)) :
      MemCb 2 (r26t3_U R r (a + τ j) (φ j)) :=
    fp81s21_wick_time_memCb
      (fp81s21_U_osc_test_classical p R (hφ j) (add_nonneg ha (τ j).property.1)) hrj
  obtain ⟨B1, hB1, hb1⟩ := db1_grad_bound (hf i hr1)
  obtain ⟨B2, hB2, hb2⟩ := db1_grad_bound (hf (i + 1) hr2)
  have hc1 : Continuous (gradient (r26t3_U R r (a + τ i) (φ i))) :=
    (show Differentiable ℝ _ from db1_gradient_differentiable (hf i hr1).1).continuous
  have hc2 : Continuous (gradient (r26t3_U R r (a + τ (i + 1)) (φ (i + 1)))) :=
    (show Differentiable ℝ _ from db1_gradient_differentiable (hf (i + 1) hr2).1).continuous
  let : IsProbabilityMeasure (HRS.Whole.withDensityReal R.ρβ) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  apply s21e_noise_integrable R.thermal.1.1.measurable (u4_thermal_pos R.thermal)
    (fp81s21_wick_time_thermal_L2 hC (i + 2) hrH) (B1 * B2)
  · intro x
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul (hb1 x) (hb2 x) (norm_nonneg _) hB1)
  · exact (hc1.inner hc2).aestronglyMeasurable

end HRS.Fp81.S21
end

#print axioms HRS.Fp81.S21.fp81s21_gaussian_wick_time_spatial_drift
#print axioms HRS.Fp81.S21.fp81s21_gaussian_wick_time_spatial_cov
