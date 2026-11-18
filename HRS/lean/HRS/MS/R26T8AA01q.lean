import HRS.MS.R26T8AA01p

/-!
# S8.2 T8A A01 (part q): the centred force integrates to zero on exterior regions in the limit
`∫_{Ω_ε} ρ ⟨∇g(u-z) - F(u), w⟩ → 0` (with integrability for every `ε > 0`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_a01_limFc (hd : 2 ≤ d) {a beta : ℝ} (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) {u v : Euc d} (huv : u ≠ v) (w : Euc d) :
    (∀ ε : ℝ, 0 < ε → Integrable (Set.indicator {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖}
        (fun z => rho z * inner ℝ (rieszKernelGrad d (criticalS d) (u - z) - forceMean rho u) w))) ∧
    Tendsto (fun ε : ℝ => ∫ z, Set.indicator {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖}
        (fun z => rho z * inner ℝ (rieszKernelGrad d (criticalS d) (u - z) - forceMean rho u) w) z) (𝓝[>] 0)
      (𝓝 0) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < criticalS d := by unfold criticalS; linarith
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  have hρs : ContDiff ℝ ∞ rho :=
    (HRS.MS.Mov0.mv0_hgauss hd hs0.le (by unfold criticalS; linarith) ha hbeta hrho).1
  have hρi : Integrable rho := Integrable.of_integral_ne_zero (by rw [hprob.integral_one]; norm_num)
  have hρm : AEStronglyMeasurable rho volume := hρs.continuous.aestronglyMeasurable
  have hsplit : ∀ z, rho z * inner ℝ (rieszKernelGrad d (criticalS d) (u - z) - forceMean rho u) w =
      rho z * inner ℝ (rieszKernelGrad d (criticalS d) (u - z)) w - inner ℝ (forceMean rho u) w * rho z := by
    intro z; rw [inner_sub_left]; ring
  have hmeasS : ∀ ε : ℝ, MeasurableSet {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖} := fun ε =>
    (measurableSet_lt measurable_const (measurable_const.sub measurable_id).norm).inter
      (measurableSet_lt measurable_const (measurable_const.sub measurable_id).norm)
  have hint1 : ∀ ε : ℝ, 0 < ε → Integrable (Set.indicator {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖}
      (fun z => rho z * inner ℝ (rieszKernelGrad d (criticalS d) (u - z)) w)) := by
    intro ε hε
    refine r26t8a_a01_ext_int_inner hd hprob.nonneg hρm (W := fun _ => w) aestronglyMeasurable_const
      (hρi.mul_const ‖w‖) u hε _ (hmeasS ε) (fun z hz => hz.1)
  have hint2 : ∀ ε : ℝ, Integrable (Set.indicator {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖}
      (fun z => inner ℝ (forceMean rho u) w * rho z)) := fun ε =>
    (hρi.const_mul _).indicator (hmeasS ε)
  constructor
  · intro ε hε
    have := (hint1 ε hε).sub (hint2 ε)
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖}
    · simp only [Set.indicator_of_mem hz, Pi.sub_apply, hsplit]
    · simp [Set.indicator_of_notMem hz]
  · have t1 := r26t8a_a01_limF hd ha hbeta hrho huv w
    have t2 := (r26t8a_a01_limint hd u v hρi).const_mul (inner ℝ (forceMean rho u) w)
    have h3 := t1.sub t2
    rw [hprob.integral_one, mul_one, sub_self] at h3
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have e : ∀ z, Set.indicator {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖}
        (fun z => rho z * inner ℝ (rieszKernelGrad d (criticalS d) (u - z) - forceMean rho u) w) z =
        Set.indicator {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖}
          (fun z => rho z * inner ℝ (rieszKernelGrad d (criticalS d) (u - z)) w) z -
        Set.indicator {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖}
          (fun z => inner ℝ (forceMean rho u) w * rho z) z := by
      intro z
      by_cases hz : z ∈ {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖}
      · simp only [Set.indicator_of_mem hz, hsplit]
      · simp [Set.indicator_of_notMem hz]
    have hc : ∫ z, Set.indicator {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖}
        (fun z => inner ℝ (forceMean rho u) w * rho z) z =
        inner ℝ (forceMean rho u) w * ∫ z, Set.indicator {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖} rho z := by
      rw [← integral_const_mul]
      congr 1; funext z
      by_cases hz : z ∈ {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖}
      · simp [Set.indicator_of_mem hz]
      · simp [Set.indicator_of_notMem hz]
    simp only [e]
    rw [integral_sub (hint1 ε hε) (hint2 ε), hc]

end HRS.MS.R26T8A
