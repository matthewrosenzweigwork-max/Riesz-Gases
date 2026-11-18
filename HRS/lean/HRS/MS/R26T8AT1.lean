import HRS.MS.R26T8AP20
import HRS.MS.R26T8AP17

/-!
# S8.2 T8A T1: row integrability of conormal pair functions and linearity of the double centring
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_T1_integrability (hd : 2 ≤ d) (a beta M sigma : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (hsd : sigma < d) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {k b : ℕ} {A : ℝ} (hA : 0 ≤ A) {R : Euc d → Euc d → ℝ}
    (hR : Conormal k b M sigma A R) :
    (∀ x, Integrable (R x) (HRS.Whole.withDensityReal rho)) ∧
    (∀ y, Integrable (fun x => R x y) (HRS.Whole.withDensityReal rho)) ∧
    Integrable (fun x => ∫ y, R x y ∂(HRS.Whole.withDensityReal rho)) (HRS.Whole.withDensityReal rho) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨hρs, hg⟩ := HRS.MS.Mov0.mv0_hgauss hd (by unfold criticalS; linarith) (by unfold criticalS; linarith)
    ha hbeta hrho
  obtain ⟨Cρ, cρ, hCρ, hcρ, hρb⟩ := r26t8a_f23_rho_unif hg 0
  obtain ⟨Kp, hKp0, hKp⟩ := r26t8a_f25_rho_poly hCρ hcρ hρb (M + (d : ℝ) + 1)
  have hKρ : ∀ y : Euc d, rho y ≤ Kp * (1 + ‖y‖) ^ (-(M + (d : ℝ) + 1)) := fun y => by
    have := hKp 0 le_rfl y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_nonneg (hrho.1.1.nonneg y)] at this
  obtain ⟨Bq, hBq0, hfub⟩ := r26t8a_f25_fubini hd b hM hsd hrho.1.1 hρs.continuous hKp0 hKρ
  haveI hprob := s85_isProb hrho.1.1
  obtain ⟨hprod, hrow, -, -⟩ := hfub hA hR
  have hRT : Conormal k b M sigma A (fun x y => R y x) := r26t8a_f24_conormal_swap hchi hR
  obtain ⟨-, hcol, -, -⟩ := hfub hA hRT
  exact ⟨hrow, hcol, hprod.integral_prod_left⟩

theorem r26t8a_T1_center_lin (mu : Measure (Euc d)) {k1 k2 : Euc d → Euc d → ℝ} (c : ℝ)
    (h1r : ∀ x, Integrable (k1 x) mu) (h2r : ∀ x, Integrable (k2 x) mu)
    (h1c : ∀ y, Integrable (fun x => k1 x y) mu) (h2c : ∀ y, Integrable (fun x => k2 x y) mu)
    (h1a : Integrable (fun x => ∫ y, k1 x y ∂mu) mu) (h2a : Integrable (fun x => ∫ y, k2 x y ∂mu) mu)
    (x y : Euc d) :
    r2CenterKernel mu (fun x y => k1 x y + c * k2 x y) x y =
      r2CenterKernel mu k1 x y + c * r2CenterKernel mu k2 x y := by
  unfold r2CenterKernel
  have e1 : ∀ x, ∫ y', (k1 x y' + c * k2 x y') ∂mu = ∫ y', k1 x y' ∂mu + c * ∫ y', k2 x y' ∂mu := fun x => by
    rw [integral_add (h1r x) ((h2r x).const_mul c), integral_const_mul]
  have e2 : ∫ x', (k1 x' y + c * k2 x' y) ∂mu = ∫ x', k1 x' y ∂mu + c * ∫ x', k2 x' y ∂mu := by
    rw [integral_add (h1c y) ((h2c y).const_mul c), integral_const_mul]
  simp only [e1]
  rw [e2, integral_add h1a (h2a.const_mul c), integral_const_mul]
  ring

theorem r26t8a_T1_center_congr (hd : 2 ≤ d) (rho : Euc d → ℝ) {k1 k2 : Euc d → Euc d → ℝ}
    (h : ∀ x y, x ≠ y → k1 x y = k2 x y) {x y : Euc d} (hxy : x ≠ y) :
    r2CenterKernel (HRS.Whole.withDensityReal rho) k1 x y = r2CenterKernel (HRS.Whole.withDensityReal rho) k2 x y := by
  haveI := r26t8a_nontrivial hd
  have hmu : HRS.Whole.withDensityReal rho ≪ (volume : Measure (Euc d)) := withDensity_absolutelyContinuous _ _
  have hae : ∀ p : Euc d, ∀ᵐ u ∂(HRS.Whole.withDensityReal rho), u ≠ p :=
    fun p => hmu.ae_le (compl_mem_ae_iff.mpr (measure_singleton p))
  have hrow : ∀ x, ∫ y', k1 x y' ∂(HRS.Whole.withDensityReal rho) = ∫ y', k2 x y' ∂(HRS.Whole.withDensityReal rho) :=
    fun x => integral_congr_ae (by filter_upwards [hae x] with u hu using h x u (Ne.symm hu))
  have hcol : ∀ y, ∫ x', k1 x' y ∂(HRS.Whole.withDensityReal rho) = ∫ x', k2 x' y ∂(HRS.Whole.withDensityReal rho) :=
    fun y => integral_congr_ae (by filter_upwards [hae y] with u hu using h u y hu)
  unfold r2CenterKernel
  rw [h x y hxy, hrow x, hcol y]
  simp only [hrow]

end HRS.MS.R26T8A
