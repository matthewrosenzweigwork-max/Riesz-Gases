import HRS.MC.E214H5
import HRS.MD.EQGaussLyapDet2
import HRS.Sections.Q41Aux20

/-!
# E214H6: positive semidefiniteness of the noise covariance matrix

For the frozen (stationary) dynamics the matrix `M_{ab} = 2β⁻¹ ∫_{[0, τ_a ∧ τ_b]} E_{ab}(σ) dσ` of the Gaussian noise part
of a linear fluctuation solution is positive semidefinite.  It equals `Λ - SA`, where `Λ` is the stationary lag
covariance and `SA_{ab} = C_β(ψ_a, ψ_b)` with `ψ_a = S_{τ_a} φ_a`; this is the covariance of the vector
`(U_{τ_a}(φ_a) - U_0(S_{τ_a}φ_a))_a` of the stationary field, so it is the congruence `Lᵀ Λ_ext L` of the
positive semidefinite stationary lag covariance (`q41_lagcov_psd`) of the `2p` observations
`(τ_a, φ_a), (0, ψ_a)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped Matrix
open HRS HRS.PDE HRS.MD.EQGaussLyapDet HRS.MD.EQGaussLyapDet2

namespace HRS.MC.E214H

variable {d : ℕ}

theorem noise_psd (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) {p : ℕ} (τ : Fin p → ℝ)
    (hτ : ∀ a, 0 ≤ τ a) (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a)) :
    (Matrix.of fun a b => 2 * β⁻¹ * ∫ σ in Set.Icc 0 (min (τ a) (τ b)),
      eqgld_E (mfData d s hs0 hsd V β hβ) ρβ (φ a) (φ b) (τ a) (τ b) σ).PosSemidef := by
  classical
  obtain ⟨hpos, hρC, c₀, Λ₀, ⟨Hz⟩⟩ := eqgld_frozen hd hs0 hsd V hV hβ ρβ hρβ
  have hd1 : 1 ≤ d := by omega
  have hprob := hρβ.1
  haveI : IsProbabilityMeasure (withDensityReal ρβ) := isProb_withDensityReal hprob
  set D := mfData d s hs0 hsd V β hβ with hD
  have htot := eqgld_cov_total hd hs0 hsd V hV hβ ρβ hρβ τ hτ φ hφ
  have hsm : ∀ f, Torus.IsSmooth f → ∀ r t : ℝ, 0 ≤ r → r ≤ t →
      Torus.IsSmooth (propagator D (fun _ => ρβ) r t f) := fun f hf r t hr hrt =>
    eqgld_prop_smooth hd1 hs0 hsd V hV hβ ρβ hprob hρC hpos f hf r t hr hrt
  have hSsm : ∀ f, Torus.IsSmooth f → ∀ v : ℝ, 0 ≤ v →
      Torus.IsSmooth (equilibriumSemigroup D ρβ v f) := by
    intro f hf v hv
    have h := hsm f hf 0 v le_rfl hv
    unfold equilibriumSemigroup projMean
    unfold Torus.IsSmooth at h ⊢
    exact h.sub contDiff_const
  -- the extended observations
  set ψ : Fin p → Torus d → ℝ := fun a => equilibriumSemigroup D ρβ (τ a) (φ a) with hψ
  have hψs : ∀ a, Torus.IsSmooth (ψ a) := fun a => hSsm _ (hφ a) _ (hτ a)
  set τe : Fin (p + p) → ℝ := Fin.append τ (fun _ => 0) with hτe
  set φe : Fin (p + p) → Torus d → ℝ := Fin.append φ ψ with hφe
  have hτe0 : ∀ i, 0 ≤ τe i := by
    intro i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · rw [hτe, Fin.append_left]; exact hτ a
    · rw [hτe, Fin.append_right]
  have hφes : ∀ i, Torus.IsSmooth (φe i) := by
    intro i
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i
    · rw [hφe, Fin.append_left]; exact hφ a
    · rw [hφe, Fin.append_right]; exact hψs a
  have hPSD := HRS.Q41.q41_lagcov_psd hd hs0 hsd hβ hV hρβ (MFLinear.continuous_of_isSmooth hρC) hpos τe hτe0 φe hφes
  set C : (Torus d → ℝ) → (Torus d → ℝ) → ℝ :=
    susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β with hC
  -- identification of `M` with `Λ - SA`
  set M : Matrix (Fin p) (Fin p) ℝ := Matrix.of fun a b => 2 * β⁻¹ * ∫ σ in Set.Icc 0 (min (τ a) (τ b)),
      eqgld_E D ρβ (φ a) (φ b) (τ a) (τ b) σ with hM
  have hMeq : ∀ a b, M a b = stationaryLagCov d s β D ρβ τ φ a b -
      C (propagator D (fun _ => ρβ) 0 (τ a) (φ a)) (propagator D (fun _ => ρβ) 0 (τ b) (φ b)) := by
    intro a b
    have := congrFun (congrFun htot a) b
    simp only [Matrix.of_apply] at this
    simp only [hM, Matrix.of_apply]
    linarith
  -- single-slot invariance of `C` under `projMean`
  have hpm_idem : ∀ f : Torus d → ℝ, projMean (withDensityReal ρβ) (projMean (withDensityReal ρβ) f) =
      projMean (withDensityReal ρβ) f := fun f => eqgld_projMean_idem f
  have hCL : ∀ f h, C (projMean (withDensityReal ρβ) f) h = C f h := by
    intro f h
    have e1 := eqgld_cs_projMean (μ := withDensityReal ρβ) (periodicRiesz d s) β
      (projMean (withDensityReal ρβ) f) h
    have e2 := eqgld_cs_projMean (μ := withDensityReal ρβ) (periodicRiesz d s) β f h
    rw [hpm_idem f] at e1
    exact e1.symm.trans e2
  have hCR : ∀ f h, C f (projMean (withDensityReal ρβ) h) = C f h := by
    intro f h
    have e1 := eqgld_cs_projMean (μ := withDensityReal ρβ) (periodicRiesz d s) β f
      (projMean (withDensityReal ρβ) h)
    have e2 := eqgld_cs_projMean (μ := withDensityReal ρβ) (periodicRiesz d s) β f h
    rw [hpm_idem h] at e1
    exact e1.symm.trans e2
  have hS0 : ∀ f, Torus.IsSmooth f → equilibriumSemigroup D ρβ 0 f = projMean (withDensityReal ρβ) f :=
    fun f hf => (HRS.PDE.MFOneLe.equilibriumSemigroup_generator_of_one_le hd1 s hs0 hsd β hβ V hV ρβ
      hρβ hρC hpos f hf).1
  have hψpm : ∀ a, ψ a = projMean (withDensityReal ρβ) (propagator D (fun _ => ρβ) 0 (τ a) (φ a)) :=
    fun a => rfl
  have hCψ : ∀ a b, C (propagator D (fun _ => ρβ) 0 (τ a) (φ a)) (propagator D (fun _ => ρβ) 0 (τ b) (φ b)) =
      C (ψ a) (ψ b) := by
    intro a b
    rw [hψpm a, hψpm b]
    exact (eqgld_cs_projMean (μ := withDensityReal ρβ) (periodicRiesz d s) β _ _).symm
  -- entries of the extended lag covariance
  set Λe := stationaryLagCov d s β D ρβ τe φe with hΛe
  have hLL : ∀ a b, Λe (Fin.castAdd p a) (Fin.castAdd p b) = stationaryLagCov d s β D ρβ τ φ a b := by
    intro a b
    simp only [hΛe, PDE.stationaryLagCov, Matrix.of_apply, hτe, hφe, Fin.append_left]
  have hLR : ∀ a b, Λe (Fin.castAdd p a) (Fin.natAdd p b) = C (ψ a) (ψ b) := by
    intro a b
    simp only [hΛe, PDE.stationaryLagCov, Matrix.of_apply, hτe, hφe, Fin.append_left, Fin.append_right]
    by_cases h : τ a ≤ 0
    · have h0 : τ a = 0 := le_antisymm h (hτ a)
      have hψa : ψ a = projMean (withDensityReal ρβ) (φ a) := by
        show equilibriumSemigroup D ρβ (τ a) (φ a) = _
        rw [h0]; exact hS0 _ (hφ a)
      rw [if_pos h, h0, sub_self, hS0 _ (hψs b)]
      refine (hCR _ _).trans ?_
      rw [hψa]
      exact (hCL _ _).symm
    · rw [if_neg h, sub_zero]
  have hRL : ∀ a b, Λe (Fin.natAdd p a) (Fin.castAdd p b) = C (ψ a) (ψ b) := by
    intro a b
    simp only [hΛe, PDE.stationaryLagCov, Matrix.of_apply, hτe, hφe, Fin.append_left, Fin.append_right]
    rw [if_pos (hτ b), sub_zero]
  have hRR : ∀ a b, Λe (Fin.natAdd p a) (Fin.natAdd p b) = C (ψ a) (ψ b) := by
    intro a b
    simp only [hΛe, PDE.stationaryLagCov, Matrix.of_apply, hτe, hφe, Fin.append_right]
    rw [if_pos le_rfl, sub_self, hS0 _ (hψs b)]
    exact hCR _ _
  have hMeq' : ∀ a b, M a b = stationaryLagCov d s β D ρβ τ φ a b - C (ψ a) (ψ b) := by
    intro a b; rw [hMeq, hCψ]
  have herm : M.IsHermitian := by
    refine Matrix.IsHermitian.ext fun i j => ?_
    change M j i = M i j
    simp only [hM, Matrix.of_apply]
    rw [min_comm]
    congr 1
    refine setIntegral_congr_fun measurableSet_Icc fun σ _ => ?_
    unfold eqgld_E
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [real_inner_comm]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg herm (fun ξ => ?_)
  have hq := hPSD.dotProduct_mulVec_nonneg (Fin.append ξ (fun i => -ξ i))
  have key : star (Fin.append ξ (fun i => -ξ i)) ⬝ᵥ Λe *ᵥ Fin.append ξ (fun i => -ξ i) =
      star ξ ⬝ᵥ M *ᵥ ξ := by
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_add, Fin.append_left, Fin.append_right, hLL,
      hLR, hRL, hRR, Pi.star_apply, star_trivial, hMeq']
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [mul_add, Finset.sum_add_distrib, mul_sub, sub_mul, Finset.sum_sub_distrib, mul_neg,
      Finset.mul_sum, neg_mul, Finset.sum_neg_distrib]
    ring_nf
  rw [← key]
  exact hq

end HRS.MC.E214H

end
