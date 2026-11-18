import HRS.MS.R2InterpAux46
import HRS.MC.S7PIS2RS
import HRS.MC.S7PIF6D

/-!
# S10.2 (worker S102), part 47 (packet F8): the drift Riemann--Stieltjes integral of a cylindrical functional (deterministic)

For a cylindrical functional `G ∘ obs` the sums `∑ D u_{G∘obs}(τ, Y_τ)[𝒟_b((a,a'])]` converge to `∫_{(0,T]} ∑_i ∂_iF(r, obs Y_r) b^r(obsTest_i r) dr`.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIL HRS.MC.Sec7.S7PIF6 HRS.MS.FixEq

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}
  {b : ℝ → (Euc d → ℝ) → ℝ} {Mb : ℝ → ℝ}

/-- The test density of the `i`-th observation: `u ↦ 1_{u ≤ τ_i} b^u(U^{u,τ_i}φ_{α_i})`. -/
def s102_hh (C : WholeCoeff d) (m : ℝ) {q : ℕ} {T : ℝ} (τ : Fin q → Icc (0 : ℝ) T) (α : Fin q → MultiIndex d)
    (b : ℝ → (Euc d → ℝ) → ℝ) (i : Fin q) (u : ℝ) : ℝ :=
  (Iic (τ i : ℝ)).indicator (fun u => b u (propagatorW C u (τ i) (oscTestFun m (α i)))) u

theorem s102_orbit_integrableOn (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c)
    (hb : S102Drift C m T r Pw b Mb) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (α : MultiIndex d) :
    IntegrableOn (fun u => b u (propagatorW C u t (oscTestFun m α))) (Icc 0 t) := by
  have hI : IntegrableOn Mb (Icc 0 t) := hb.Mb_int.mono_set (Icc_subset_Icc le_rfl ht.2)
  refine Integrable.mono' (hI.mul_const (s57pC d r Pw * c α)) (hb.meas t ht α) ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun u hu => ?_)
  have huT : u ∈ Icc (0 : ℝ) T := ⟨hu.1, hu.2.trans ht.2⟩
  obtain ⟨h1, h2⟩ := s102_orbit_test hP hD huT (t := t) ⟨hu.2, ht.2⟩ α
  rw [Real.norm_eq_abs]
  calc _ ≤ Mb u * (weightedSobolevE r Pw _).toReal := hb.hM u huT _ h1
    _ ≤ Mb u * (s57pC d r Pw * c α) := mul_le_mul_of_nonneg_left h2 (hb.Mb_nonneg u)

theorem s102_hh_integrableOn (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c)
    (hb : S102Drift C m T r Pw b Mb) {q : ℕ} (τ : Fin q → Icc (0 : ℝ) T) (α : Fin q → MultiIndex d) (i : Fin q) :
    IntegrableOn (s102_hh C m τ α b i) (Icc 0 T) := by
  have ht : (τ i : ℝ) ∈ Icc (0 : ℝ) T := (τ i).2
  have hI := (s102_orbit_integrableOn hP hD hb ht (α i)).mono_set
    (show Iic (τ i : ℝ) ∩ Icc 0 T ⊆ Icc 0 (τ i : ℝ) from fun u hu => ⟨hu.2.1, hu.1⟩)
  unfold s102_hh IntegrableOn
  refine (integrable_indicator_iff measurableSet_Iic).2 ?_
  rwa [IntegrableOn, Measure.restrict_restrict measurableSet_Iic]

/-- `∫_{(a,a']} hh_i = ∫_{(a,a'∧τ_i]} b^u(U^{u,τ_i}φ)`. -/
theorem s102_hh_integral {q : ℕ} (τ : Fin q → Icc (0 : ℝ) T) (α : Fin q → MultiIndex d) (i : Fin q) (a a' : ℝ) :
    ∫ u in Ioc a a', s102_hh C m τ α b i u =
      ∫ u in Ioc a (min a' (τ i : ℝ)), b u (propagatorW C u (τ i) (oscTestFun m (α i))) := by
  unfold s102_hh
  rw [setIntegral_indicator measurableSet_Iic]
  have : Ioc a a' ∩ Iic (τ i : ℝ) = Ioc a (min a' (τ i : ℝ)) := by
    ext u
    simp [and_assoc]
  rw [this]

/-- The derivative of the cylindrical heat function on a vector. -/
theorem s102_heat_fderiv_apply (γ : ℝ → Measure (OscPath d m T))
    (hγ : ∀ u ∈ Icc (0 : ℝ) T, IsR2FutureGaussian C m T u (γ u)) {q : ℕ}
    (τ : Fin q → Icc (0 : ℝ) T) (α : Fin q → MultiIndex d) {G : EuclideanSpace ℝ (Fin q) → ℝ} (hG : MemCb 2 G)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T) (y v : OscPath d m T) :
    fderiv ℝ (r2HeatFn γ (fun w => G (s102_obs τ α w)) u) y v =
      ∑ i, fderiv ℝ (gaussHeat (s102_obsCov C m τ α) G u) (s102_obs τ α y) (EuclideanSpace.single i 1) *
        s102_obs τ α v i := by
  rw [(s102_heat_obs_deriv C γ hγ τ α G hG u hu y).1, ContinuousLinearMap.comp_apply]
  conv_lhs => rw [S7PIF6_vec_expand (s102_obs τ α v)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

end HRS.MS.R2Interp

end
