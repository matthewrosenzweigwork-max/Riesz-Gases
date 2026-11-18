import HRS.MC.S7PIRA
import HRS.MC.S7PIRDrift
import HRS.MC.S7PIS3Heat
import HRS.MC.S7PIS3Cov3
import HRS.MC.S7PIF5D

/-!
# Packet piF10, part A: deterministic helpers for `s7_PIF_cyl_concl_proof`

* uniform bounds of the derivatives of the finite-dimensional heat function (`gaussHeat` is an average over a probability measure);
* continuity of `gaussHeat` in the space variable;
* `IsJValue` depends on `z` only through its values on the interval;
* `obsVec (𝖳_T w) = obsVec w`;
* measurability of the cut-off energy density `S7PIS3_h` and the integrability of the cross products of locally square integrable
  vector integrands.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIF10

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIS3

variable {d : ℕ}

/-- the derivatives of `gaussHeat` are bounded by those of `G` -/
theorem S7PIF10_heat_deriv_bound {q : ℕ} (S : ℝ → Matrix (Fin q) (Fin q) ℝ)
    {G : EuclideanSpace ℝ (Fin q) → ℝ} {k : ℕ} (hG : MemCb k G) {j : ℕ} (hj : j ≤ k) (u : ℝ)
    (c : EuclideanSpace ℝ (Fin q)) :
    ‖iteratedFDeriv ℝ j (gaussHeat S G u) c‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ j G z‖ := by
  have h := S7PIS3_heat_deriv (multivariateGaussian 0 (S u)) hG hj c
  have e : gaussHeat S G u = fun y => ∫ x, G (y + x) ∂(multivariateGaussian 0 (S u)) := rfl
  rw [e, h]
  refine (norm_integral_le_of_norm_le_const (C := ⨆ z, ‖iteratedFDeriv ℝ j G z‖) ?_).trans (by simp)
  exact Filter.Eventually.of_forall fun x => S7PIS3_cb_bound hG hj _

/-- the partial derivatives of `gaussHeat` are bounded -/
theorem S7PIF10_fderiv_bound {q : ℕ} (S : ℝ → Matrix (Fin q) (Fin q) ℝ)
    {G : EuclideanSpace ℝ (Fin q) → ℝ} (hG : MemCb 1 G) (u : ℝ) (c : EuclideanSpace ℝ (Fin q)) (i : Fin q) :
    |fderiv ℝ (gaussHeat S G u) c (EuclideanSpace.single i 1)| ≤ ⨆ z, ‖iteratedFDeriv ℝ 1 G z‖ := by
  have h := S7PIF10_heat_deriv_bound S hG (j := 1) le_rfl u c
  have h2 := (iteratedFDeriv ℝ 1 (gaussHeat S G u) c).le_opNorm (fun _ : Fin 1 => EuclideanSpace.single i (1 : ℝ))
  rw [iteratedFDeriv_one_apply] at h2
  simp only [Fin.prod_univ_one, PiLp.norm_single, norm_one, mul_one] at h2
  rw [← Real.norm_eq_abs]
  exact h2.trans h

/-- `gaussHeat` is continuous in the space variable -/
theorem S7PIF10_gaussHeat_cont {q : ℕ} (S : ℝ → Matrix (Fin q) (Fin q) ℝ)
    {G : EuclideanSpace ℝ (Fin q) → ℝ} {k : ℕ} (hG : MemCb k G) (u : ℝ) :
    Continuous (gaussHeat S G u) := by
  have hGc : Continuous G := hG.1.continuous
  unfold gaussHeat
  refine continuous_of_dominated (bound := fun _ => ⨆ z, ‖iteratedFDeriv ℝ 0 G z‖) ?_ ?_
    (integrable_const _) ?_
  · intro c
    exact (hGc.comp (by fun_prop : Continuous fun x : EuclideanSpace ℝ (Fin q) => c + x)).aestronglyMeasurable
  · intro c
    refine Filter.Eventually.of_forall fun x => ?_
    have := S7PIS3_cb_bound (j := 0) hG (Nat.zero_le _) (c + x)
    simpa using this
  · refine Filter.Eventually.of_forall fun x => ?_
    exact hGc.comp (by fun_prop : Continuous fun c : EuclideanSpace ℝ (Fin q) => c + x)

/-- `IsJValue` depends on `z` only through its values on `I ∩ [0,T]` -/
theorem S7PIF10_isJValue_congr (D : DynData d) (ρ : ℝ → Torus d → ℝ) (m T : ℝ)
    {z z' : ℝ → NegSobolev d m} {I : Set ℝ} (hI : MeasurableSet I)
    (hz : ∀ u ∈ I ∩ Set.Icc (0 : ℝ) T, z u = z' u) {J : TensorDual (PathSpace d m T) 2}
    (h : IsJValue D ρ m T z' I J) : IsJValue D ρ m T z I J := by
  refine ⟨h.1, fun ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂ => ?_⟩
  rw [h.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂]
  congr 1
  refine setIntegral_congr_fun (hI.inter measurableSet_Icc) fun u hu => ?_
  have hu' : u ∈ I ∩ Set.Icc (0 : ℝ) T := ⟨hu.1, hu.2.1, hu.2.2.trans ((min_le_left _ _).trans hta.2)⟩
  rw [hz u hu']

/-- the observation vector of the predicted continuation at the final time is the observation vector of the path -/
theorem S7PIF10_obs_predicted_T (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T)
    (w : PathSpace d m T) :
    obsVec m T t φ (predicted R.D R.ρ w T) = obsVec m T t φ w := by
  have hPath := (HRS.MC.Sec7.S7PIS1.s7_PIS_path_facts_proof R m hm T hT).1
  ext i
  show NegSobolev.eval (pathAt (predicted R.D R.ρ w T) (t i)) (φ i) = NegSobolev.eval (pathAt w (t i)) (φ i)
  rw [hPath w T (t i) ⟨hT.le, le_rfl⟩ (ht i)]
  simp [(ht i).2]

/-- the cut-off energy density is Borel -/
theorem S7PIF10_h_meas (R : Regime d) {T : ℝ} {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i)) (i j : Fin q) :
    Measurable (S7PIS3_h R t φ i j) := by
  classical
  have hg : ContinuousOn (S7PIS3_g R t φ i j) (Set.Icc 0 (min (t i) (t j))) :=
    S7PIS3_g_cont R (ht i).1 (ht j).1 (hφ i) (hφ j)
  have : S7PIS3_h R t φ i j = (Set.Icc 0 (min (t i) (t j))).piecewise (S7PIS3_g R t φ i j) 0 := by
    unfold S7PIS3_h
    exact (Set.piecewise_eq_indicator).symm
  rw [this]
  exact hg.measurable_piecewise continuousOn_const measurableSet_Icc

/-- cross products of a locally square integrable vector integrand are integrable -/
theorem S7PIF10_cross_integrable {ι : Type*} [Fintype ι] {q : ℕ} {T : ℝ}
    (Φ : ℝ → ι → EuclideanSpace ℝ (Fin q))
    (hmeas : AEMeasurable Φ (volume.restrict (Set.Icc 0 T)))
    (hsq : ∫⁻ s in Set.Icc 0 T, ∑ k, ‖Φ s k‖ₑ ^ 2 < ∞) (i j : Fin q) :
    IntegrableOn (fun s => ∑ k, Φ s k i * Φ s k j) (Set.Icc 0 T) := by
  classical
  have hmk : ∀ k : ι, AEMeasurable (fun s => Φ s k) (volume.restrict (Set.Icc 0 T)) :=
    fun k => (measurable_pi_apply k).comp_aemeasurable hmeas
  have hmc : ∀ k : ι, ∀ i : Fin q, AEMeasurable (fun s => Φ s k i) (volume.restrict (Set.Icc 0 T)) :=
    fun k i => ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin q) →L[ℝ] ℝ).continuous.measurable).comp_aemeasurable
      (hmk k)
  have hsum : AEStronglyMeasurable (fun s => ∑ k, Φ s k i * Φ s k j) (volume.restrict (Set.Icc 0 T)) :=
    (Finset.aemeasurable_fun_sum _ fun k _ => (hmc k i).mul (hmc k j)).aestronglyMeasurable
  have hbd : AEStronglyMeasurable (fun s => ∑ k, ‖Φ s k‖ ^ 2) (volume.restrict (Set.Icc 0 T)) :=
    (Finset.aemeasurable_fun_sum _ fun k _ => ((hmk k).norm).pow_const 2).aestronglyMeasurable
  have hbi : Integrable (fun s => ∑ k, ‖Φ s k‖ ^ 2) (volume.restrict (Set.Icc 0 T)) := by
    refine ⟨hbd, ?_⟩
    refine lt_of_le_of_lt (lintegral_mono fun s => ?_) hsq
    have h1 : ‖∑ k, ‖Φ s k‖ ^ 2‖ₑ ≤ ∑ k, ‖(‖Φ s k‖ ^ 2)‖ₑ := enorm_sum_le _ _
    refine h1.trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
    rw [enorm_pow, enorm_norm]
  refine Integrable.mono' hbi hsum (Filter.Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  have hi : |Φ s k i| ≤ ‖Φ s k‖ := by
    simpa using PiLp.norm_apply_le (Φ s k) i
  have hj : |Φ s k j| ≤ ‖Φ s k‖ := by
    simpa using PiLp.norm_apply_le (Φ s k) j
  calc |Φ s k i| * |Φ s k j| ≤ ‖Φ s k‖ * ‖Φ s k‖ := mul_le_mul hi hj (abs_nonneg _) (norm_nonneg _)
    _ = ‖Φ s k‖ ^ 2 := (sq _).symm

end HRS.MC.Sec7.S7PIF10

end
