import HRS.MS.R26T8AA01q

/-!
# S8.2 T8A A01 (part r): `∫ ρ ⟨c, ∇_xQ(u,·)⟩ = 0` for a canonical `Q` (limit on exterior regions)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 3200000 in
theorem r26t8a_a01_limDx (hd : 2 ≤ d) (a beta M A : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (hA : 0 ≤ A) {rho : Euc d → ℝ} (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    {f : Euc d → ℝ} {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) (u c p q : Euc d) :
    (∀ ε : ℝ, 0 < ε → Integrable (Set.indicator {z : Euc d | ε < ‖p - z‖ ∧ ε < ‖q - z‖}
        (fun z => rho z * inner ℝ c (pairGradX Q u z)))) ∧
    Tendsto (fun ε : ℝ => ∫ z, Set.indicator {z : Euc d | ε < ‖p - z‖ ∧ ε < ‖q - z‖}
        (fun z => rho z * inner ℝ c (pairGradX Q u z)) z) (𝓝[>] 0) (𝓝 0) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < criticalS d := by unfold criticalS; linarith
  have hsd : criticalS d < d := by unfold criticalS; linarith
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  have hρs : ContDiff ℝ ∞ rho :=
    (HRS.MS.Mov0.mv0_hgauss hd hs0.le hsd ha hbeta hrho).1
  have hρc : Continuous rho := hρs.continuous
  have hQ2 : ContDiffOn ℝ 2 (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2} :=
    hQ.smooth.of_le (by norm_num)
  have hQt : Conormal (4 + 2) 1 M (criticalS d - 2) A Q := hQ.tangential
  have hcan : ∀ w, ∫ y, rho y * Q w y = 0 := fun w => by
    rw [← r26t8a_f25_wd_integral hprob (Q w)]; exact hQ.canonical.2.2.2 w
  have hgi := (r26t8a_a01_grad_int hd a beta M A ha hbeta hM hA hrho hQ u).2
  have hcoord : ∀ j : Fin d, Integrable (fun z => rho z * pairGradX Q u z j) := by
    intro j
    refine Integrable.mono' hgi ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact (hρc.aestronglyMeasurable).mul
        (r26t8a_p10a_aesm hd u (((EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous).comp_continuousOn
          (r26t8a_a01_gradX_cont_snd hQ2 u)))
    · rw [norm_mul, Real.norm_of_nonneg (hprob.nonneg z)]
      exact mul_le_mul_of_nonneg_left ((Real.norm_eq_abs _ ▸ r26t8a_abs_coord_le _ j)) (hprob.nonneg z)
  have hψi : Integrable (fun z => rho z * inner ℝ c (pairGradX Q u z)) := by
    have : ∀ z, rho z * inner ℝ c (pairGradX Q u z) = ∑ j : Fin d, c j * (rho z * pairGradX Q u z j) := by
      intro z
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp only [this]
    exact integrable_finset_sum _ fun j _ => (hcoord j).const_mul _
  have hψ0 : ∫ z, rho z * inner ℝ c (pairGradX Q u z) = 0 := by
    have : ∀ z, rho z * inner ℝ c (pairGradX Q u z) = ∑ j : Fin d, c j * (rho z * pairGradX Q u z j) := by
      intro z
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp only [this]
    rw [integral_finset_sum _ fun j _ => (hcoord j).const_mul _]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_const_mul]
    have := r26t8a_a01_row_deriv d hd 4 1 a beta M (criticalS d) ha hbeta hM hsd hrho hA hQt hcan j u
    have e : ∀ z, pairGradX Q u z j = r26t8a_dx j Q u z := fun z => by
      unfold pairGradX r26t8a_dx; rw [movtr_gradient_apply]
    simp only [e]
    rw [this, mul_zero]
  have hmeasS : ∀ ε : ℝ, MeasurableSet {z : Euc d | ε < ‖p - z‖ ∧ ε < ‖q - z‖} := fun ε =>
    (measurableSet_lt measurable_const (measurable_const.sub measurable_id).norm).inter
      (measurableSet_lt measurable_const (measurable_const.sub measurable_id).norm)
  refine ⟨fun ε _ => hψi.indicator (hmeasS ε), ?_⟩
  have := r26t8a_a01_limint hd p q hψi
  rwa [hψ0] at this

end HRS.MS.R26T8A
