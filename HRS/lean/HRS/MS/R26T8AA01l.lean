import HRS.MS.R26T8AA01k

/-!
# S8.2 T8A A01 (part l): the force as a principal value on a punctured exterior region
`∫_{ε<‖u-z‖, ε<‖v-z‖} ρ(z) ⟨∇g(u-z), w⟩ dz → ⟨forceMean ρ u, w⟩`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

/-- Integrability of a bounded-kernel piece on the exterior region. -/
theorem r26t8a_a01_ext_int (hd : 2 ≤ d) (j : Fin d) {ψ : Euc d → ℝ} (hψm : AEStronglyMeasurable ψ volume)
    (hψi : Integrable ψ) (u : Euc d) {ε : ℝ} (hε : 0 < ε) (S : Set (Euc d)) (hS : MeasurableSet S)
    (hSε : ∀ z ∈ S, ε < ‖u - z‖) :
    Integrable (Set.indicator S (fun z => ψ z * r26t8a_a01_kappa d j (u - z))) := by
  have hs0 : 0 < criticalS d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    unfold criticalS; linarith
  obtain ⟨B, hB⟩ := r26t8a_a01_kappa_far hs0 j ε hε
  have hk : AEStronglyMeasurable (fun z => r26t8a_a01_kappa d j (u - z)) volume :=
    ((r26t8a_a01_kappa_meas j).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  refine Integrable.mono' (hψi.norm.const_mul |B|) ((hψm.mul hk).indicator hS) (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ S
  · rw [Set.indicator_of_mem hz, norm_mul, Real.norm_eq_abs]
    calc ‖ψ z‖ * |r26t8a_a01_kappa d j (u - z)| ≤ ‖ψ z‖ * |B| :=
          mul_le_mul_of_nonneg_left ((hB _ (hSε z hz).le).trans (le_abs_self B)) (norm_nonneg _)
      _ = |B| * ‖ψ z‖ := mul_comm _ _
  · rw [Set.indicator_of_notMem hz]; simp only [norm_zero]; positivity

theorem r26t8a_a01_limF (hd : 2 ≤ d) {a beta : ℝ} (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) {u v : Euc d} (huv : u ≠ v) (w : Euc d) :
    Tendsto (fun ε : ℝ => ∫ z, Set.indicator {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖}
        (fun z => rho z * inner ℝ (rieszKernelGrad d (criticalS d) (u - z)) w) z) (𝓝[>] 0)
      (𝓝 (inner ℝ (forceMean rho u) w)) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < criticalS d := by unfold criticalS; linarith
  obtain ⟨hdiff, C, c, hC, hc, hb⟩ := HRS.MS.Wad.s84_thermal_gaussReg hd ha hbeta hrho
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  have hρs : ContDiff ℝ ∞ rho :=
    (HRS.MS.Mov0.mv0_hgauss hd hs0.le (by unfold criticalS; linarith) ha hbeta hrho).1
  have hρi : Integrable rho := Integrable.of_integral_ne_zero (by rw [hprob.integral_one]; norm_num)
  have hlip : ∀ z : Euc d, ‖z - u‖ < 1 / 4 → |rho z - rho u| ≤ C * ‖z - u‖ := by
    intro z _
    have hbd : ∀ t ∈ (Set.univ : Set (Euc d)), ‖fderiv ℝ rho t‖ ≤ C := by
      intro t _
      refine (hb t).2.trans ?_
      have : Real.exp (-c * ‖t‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖t‖])
      nlinarith
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := rho) (fun t _ => (hρs.differentiable (by simp)) t)
      hbd convex_univ (Set.mem_univ u) (Set.mem_univ z)
    rwa [Real.norm_eq_abs] at this
  have hC0 : 0 ≤ C := hC
  have hj : ∀ j : Fin d, Tendsto (fun ε : ℝ => ∫ z, Set.indicator {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖}
        (fun z => rho z * r26t8a_a01_kappa d j (u - z)) z) (𝓝[>] 0)
      (𝓝 ((convGradConvW (rieszKernelGrad d (criticalS d)) rho u) j)) := fun j =>
    r26t8a_a01_pv_coord hd j huv hρs.continuous.aestronglyMeasurable hρi (by norm_num) le_rfl hC0 hlip
  have hsum := tendsto_finset_sum Finset.univ (fun j _ => (hj j).const_mul (w j))
  have hlim : ∑ j : Fin d, w j * (convGradConvW (rieszKernelGrad d (criticalS d)) rho u) j =
      inner ℝ (forceMean rho u) w := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, forceMean]
  rw [hlim] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hms : ∀ j : Fin d, Integrable (Set.indicator {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖}
      (fun z => rho z * r26t8a_a01_kappa d j (u - z))) := fun j =>
    r26t8a_a01_ext_int hd j hρs.continuous.aestronglyMeasurable hρi u hε _
      ((measurableSet_lt measurable_const (measurable_const.sub measurable_id).norm).inter
        (measurableSet_lt measurable_const (measurable_const.sub measurable_id).norm)) (fun z hz => hz.1)
  have hconst : ∑ j : Fin d, w j * ∫ z, Set.indicator {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖}
      (fun z => rho z * r26t8a_a01_kappa d j (u - z)) z =
      ∑ j : Fin d, ∫ z, w j * Set.indicator {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖}
        (fun z => rho z * r26t8a_a01_kappa d j (u - z)) z :=
    Finset.sum_congr rfl fun j _ => (integral_const_mul _ _).symm
  rw [hconst, ← integral_finset_sum _ fun j _ => (hms j).const_mul (w j)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖}
  · simp only [Set.indicator_of_mem hz, Finset.sum_apply]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, r26t8a_a01_kappa, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · simp [Set.indicator_of_notMem hz]

end HRS.MS.R26T8A
