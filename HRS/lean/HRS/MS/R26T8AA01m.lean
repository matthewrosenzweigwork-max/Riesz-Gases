import HRS.MS.R26T8AA01l
import HRS.MS.R26T8AP10a

/-!
# S8.2 T8A A01 (part m): `oneJ` as a principal value on a punctured exterior region
For a `PairCorrector` `Q`, `u ≠ v`:
`∫_{ε<‖u-z‖, ε<‖v-z‖} ρ(z) ⟨∇g(u-z), ∇Q(·,v)(z)⟩ dz → oneJ C (Q(·,v)) u`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem r26t8a_a01_limJ (hd : 2 ≤ d) (a beta M A : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (hA : 0 ≤ A) {rho : Euc d → ℝ} (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    {f : Euc d → ℝ} {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) {u v : Euc d} (huv : u ≠ v) :
    Tendsto (fun ε : ℝ => ∫ z, Set.indicator {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖}
        (fun z => rho z * inner ℝ (rieszKernelGrad d (criticalS d) (u - z)) (pairGradX Q z v)) z) (𝓝[>] 0)
      (𝓝 (oneJ (critCoeff d a beta rho) (fun t => Q t v) u)) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < criticalS d := by unfold criticalS; linarith
  have hsd : criticalS d < d := by unfold criticalS; linarith
  obtain ⟨hdiff, C, c, hC, hc, hb⟩ := HRS.MS.Wad.s84_thermal_gaussReg hd ha hbeta hrho
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  have hρs : ContDiff ℝ ∞ rho :=
    (HRS.MS.Mov0.mv0_hgauss hd hs0.le hsd ha hbeta hrho).1
  have hρc : Continuous rho := hρs.continuous
  have hQt : Conormal (4 + 2) 1 M (criticalS d - 2) A Q := hQ.tangential
  obtain ⟨τ, H⟩ := r26t8a_p10a_hyp hd hM hsd hA hQt hρs hC hc (fun x => (hb x).1) (fun x => (hb x).2) v
  set h : Euc d → Euc d := fun z => rho z • gradient (fun t => Q t v) z with hh
  obtain ⟨r1, hr1, hr14, L, hL, hlipv⟩ := r26t8a_p10a_lip H.C1 huv
  have hQ2 : ContDiffOn ℝ 2 (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2} :=
    hQ.smooth.of_le (by norm_num)
  have hgi := (r26t8a_a01_grad_int hd a beta M A ha hbeta hM hA hrho hQ v).1
  have hjc : ∀ j : Fin d, ContinuousOn (fun z => h z j) {v}ᶜ := fun j =>
    ((EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous).comp_continuousOn H.C1.continuousOn
  have hjm : ∀ j : Fin d, AEStronglyMeasurable (fun z => h z j) volume := fun j =>
    r26t8a_p10a_aesm hd v (hjc j)
  have hji : ∀ j : Fin d, Integrable (fun z => h z j) := by
    intro j
    refine Integrable.mono' hgi (hjm j) (Filter.Eventually.of_forall fun z => ?_)
    have : |h z j| ≤ rho z * ‖pairGradX Q z v‖ := by
      simp only [hh, PiLp.smul_apply, smul_eq_mul]
      rw [abs_mul, abs_of_nonneg (hprob.nonneg z)]
      exact mul_le_mul_of_nonneg_left ((r26t8a_abs_coord_le _ j).trans (le_of_eq rfl)) (hprob.nonneg z)
    rwa [Real.norm_eq_abs]
  have hj : ∀ j : Fin d, Tendsto (fun ε : ℝ => ∫ z, Set.indicator {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖}
        (fun z => h z j * r26t8a_a01_kappa d j (u - z)) z) (𝓝[>] 0)
      (𝓝 ((convGradConvW (rieszKernelGrad d (criticalS d)) (fun w => h w j) u) j)) := by
    intro j
    refine r26t8a_a01_pv_coord hd j huv (hjm j) (hji j) hr1 hr14 hL ?_
    intro z hz
    have := hlipv z hz
    calc |h z j - h u j| = |(h z - h u) j| := by simp
      _ ≤ ‖h z - h u‖ := r26t8a_abs_coord_le _ j
      _ ≤ _ := this
  have hsum := tendsto_finset_sum Finset.univ (fun j _ => hj j)
  have hlim : ∑ j : Fin d, (convGradConvW (rieszKernelGrad d (criticalS d)) (fun w => h w j) u) j =
      oneJ (critCoeff d a beta rho) (fun t => Q t v) u := by
    rw [r26t8a_oneJ_crit]
    rfl
  rw [hlim] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hms : ∀ j : Fin d, Integrable (Set.indicator {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖}
      (fun z => h z j * r26t8a_a01_kappa d j (u - z))) := fun j =>
    r26t8a_a01_ext_int hd j (hjm j) (hji j) u hε _
      ((measurableSet_lt measurable_const (measurable_const.sub measurable_id).norm).inter
        (measurableSet_lt measurable_const (measurable_const.sub measurable_id).norm)) (fun z hz => hz.1)
  rw [← integral_finset_sum _ fun j _ => hms j]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ {z : Euc d | ε < ‖u - z‖ ∧ ε < ‖v - z‖}
  · simp only [Set.indicator_of_mem hz, Finset.sum_apply]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, r26t8a_a01_kappa, hh, PiLp.smul_apply,
      smul_eq_mul, pairGradX, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · simp [Set.indicator_of_notMem hz]

end HRS.MS.R26T8A
