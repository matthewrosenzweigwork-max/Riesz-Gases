import HRS.MS.SA12LimitL18
import HRS.MH.CoercTestW1
import HRS.MH.AdjointRdDefs

/-!
# S.A.12(c), packet E7.07 (worker S82Z2), part A: the exact Plancherel jet identity

`sa12de7_sobolevNormSq_jet`: for `u ∈ C_c^∞`, `sobolevNormSq m u = jetSq m 1 u`, i.e.
`∫ (1+4π²|ξ|²)^m |û|² = ∑_{j ≤ m} C(m,j) ∑_{idx ∈ [d]^j} ∫ (∂^idx u)²`, with ordered indices and binomial weights
(`sa12y_fourier_partial`, the `2π` convention).  `sa12de7_sobolevNormE_jet`: the extended-norm form (spec `sobolev_jet_eq`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MS.SA12DE7

open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Limit

variable {d : ℕ}

theorem sa12de7_pd_cont {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u) {j : ℕ} (idx : Fin j → Fin d) :
    Continuous (partialDeriv idx u) := by
  unfold partialDeriv
  have h := hu.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ
    (fun l => EuclideanSpace.single (idx l) (1 : ℝ))).continuous.comp h

theorem sa12de7_pd_compact {u : Euc d → ℝ} (hc : HasCompactSupport u) {j : ℕ} (idx : Fin j → Fin d) :
    HasCompactSupport (partialDeriv idx u) := by
  unfold partialDeriv
  exact (hc.iteratedFDeriv j).comp_left (g := fun A : (Euc d) [×j]→L[ℝ] ℝ =>
    A (fun l => EuclideanSpace.single (idx l) (1 : ℝ))) (by simp)

theorem sa12de7_pd_memLp {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) {j : ℕ}
    (idx : Fin j → Fin d) : MemLp (partialDeriv idx u) 2 volume :=
  (sa12de7_pd_cont hu idx).memLp_of_hasCompactSupport (sa12de7_pd_compact hc idx)

theorem sa12de7_pd_integrable {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) {j : ℕ}
    (idx : Fin j → Fin d) : Integrable (partialDeriv idx u) volume :=
  (sa12de7_pd_cont hu idx).integrable_of_hasCompactSupport (sa12de7_pd_compact hc idx)

/-- `∂^0 u = u`. -/
theorem sa12de7_pd_zero (u : Euc d → ℝ) (idx : Fin 0 → Fin d) : partialDeriv idx u = u := by
  funext x
  simp [partialDeriv]

/-- Fourier side of one ordered derivative: `|\widehat{∂^idx u}|² = (2π)^{2j} ∏ ξ_{idx l}² |û|²` a.e. -/
theorem sa12de7_fourier_pd {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) {j : ℕ}
    (idx : Fin j → Fin d) :
    ∀ᵐ ξ ∂(volume : Measure (Euc d)),
      ‖fourierL2 (partialDeriv idx u) ξ‖ ^ 2 =
        (2 * Real.pi) ^ (2 * j) * (∏ l, (ξ (idx l)) ^ 2) * ‖fourierL2 u ξ‖ ^ 2 := by
  have h1 := HRS.MH.CoercTest.p_wt1_fourierL2_eq (partialDeriv idx u) (sa12de7_pd_integrable hu hc idx)
    (sa12de7_pd_memLp hu hc idx)
  have h2 := HRS.MH.CoercTest.p_wt1_fourierL2_eq u (sa12de7_pd_integrable (j := 0) hu hc (Fin.elim0)
    |>.congr (Eventually.of_forall fun x => by rw [sa12de7_pd_zero])) (by
      have := sa12de7_pd_memLp hu hc (j := 0) Fin.elim0
      rwa [sa12de7_pd_zero] at this)
  filter_upwards [h1, h2] with ξ e1 e2
  rw [e1, e2]
  have h3 := sa12y_fourier_partial (k := j) (hu.of_le (by exact_mod_cast le_top)) hc le_rfl idx ξ
  have hn : ‖(2 * (Real.pi : ℂ) * Complex.I) ^ j * ∏ i, ((ξ (idx i) : ℝ) : ℂ)‖ ^ 2 =
      (2 * Real.pi) ^ (2 * j) * ∏ l, (ξ (idx l)) ^ 2 := by
    have hπ : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
      simp [abs_of_pos Real.pi_pos]
    rw [norm_mul, norm_pow, hπ, norm_prod, mul_pow, ← pow_mul, mul_comm j 2, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [h3, norm_mul, mul_pow, hn]


theorem sa12de7_sum_sq (ξ : Euc d) (j : ℕ) :
    (∑ i : Fin d, ξ i ^ 2) ^ j = ∑ idx : Fin j → Fin d, ∏ l, ξ (idx l) ^ 2 := by
  have h1 : (∑ i : Fin d, ξ i ^ 2) ^ j = ∏ _l : Fin j, ∑ i : Fin d, ξ i ^ 2 := by
    simp [Finset.prod_const]
  rw [h1, Finset.prod_univ_sum, Fintype.piFinset_univ]

theorem sa12de7_weight (m : ℕ) (ξ : Euc d) (a : ℝ) :
    (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (m : ℝ) * a =
      ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
        ∑ idx : Fin j → Fin d, ((2 * Real.pi) ^ (2 * j) * (∏ l, ξ (idx l) ^ 2) * a) := by
  have hX : 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 = (2 * Real.pi) ^ 2 * ∑ i : Fin d, ξ i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    ring
  rw [Real.rpow_natCast, add_comm, hX, add_pow, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_pow, ← pow_mul, sa12de7_sum_sq, one_pow, mul_one]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun idx _ => ?_
  ring

/-- **Exact Plancherel jet identity** (ordered indices, binomial weights, `2π` convention). -/
theorem sa12de7_sobolevNormSq_jet (m : ℕ) {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    sobolevNormSq (m : ℝ) u = jetSq m (fun _ => 1) u := by
  have hall : ∀ᵐ ξ ∂(volume : Measure (Euc d)), ∀ j ∈ Finset.range (m + 1), ∀ idx : Fin j → Fin d,
      ‖fourierL2 (partialDeriv idx u) ξ‖ ^ 2 =
        (2 * Real.pi) ^ (2 * j) * (∏ l, (ξ (idx l)) ^ 2) * ‖fourierL2 u ξ‖ ^ 2 :=
    (Filter.eventually_all_finset (Finset.range (m + 1))).2 fun j _ =>
      Filter.eventually_all.2 fun idx => sa12de7_fourier_pd hu hc idx
  have hint : ∀ {j : ℕ} (idx : Fin j → Fin d), Integrable (fun ξ => ‖fourierL2 (partialDeriv idx u) ξ‖ ^ 2) volume :=
    fun idx => integrable_norm_sq_fourierL2 (sa12de7_pd_memLp hu hc idx)
  unfold sobolevNormSq jetSq
  have e1 : ∫ ξ : Euc d, (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (m : ℝ) * ‖fourierL2 u ξ‖ ^ 2 =
      ∫ ξ : Euc d, ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
        ∑ idx : Fin j → Fin d, ‖fourierL2 (partialDeriv idx u) ξ‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [hall] with ξ hξ
    rw [sa12de7_weight]
    refine Finset.sum_congr rfl fun j hj => ?_
    congr 1
    exact Finset.sum_congr rfl fun idx _ => (hξ j hj idx).symm
  rw [e1, integral_finset_sum _ fun j _ => (integrable_finset_sum _ fun idx _ => hint idx).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_finset_sum _ fun idx _ => hint idx]
  congr 1
  refine Finset.sum_congr rfl fun idx _ => ?_
  rw [integral_norm_sq_fourierL2 (sa12de7_pd_memLp hu hc idx)]
  simp


theorem sa12de7_weighted_ae (m : ℕ) {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    ∀ᵐ ξ ∂(volume : Measure (Euc d)), (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (m : ℝ) * ‖fourierL2 u ξ‖ ^ 2 =
      ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
        ∑ idx : Fin j → Fin d, ‖fourierL2 (partialDeriv idx u) ξ‖ ^ 2 := by
  have hall : ∀ᵐ ξ ∂(volume : Measure (Euc d)), ∀ j ∈ Finset.range (m + 1), ∀ idx : Fin j → Fin d,
      ‖fourierL2 (partialDeriv idx u) ξ‖ ^ 2 =
        (2 * Real.pi) ^ (2 * j) * (∏ l, (ξ (idx l)) ^ 2) * ‖fourierL2 u ξ‖ ^ 2 :=
    (Filter.eventually_all_finset (Finset.range (m + 1))).2 fun j _ =>
      Filter.eventually_all.2 fun idx => sa12de7_fourier_pd hu hc idx
  filter_upwards [hall] with ξ hξ
  rw [sa12de7_weight]
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 1
  exact Finset.sum_congr rfl fun idx _ => (hξ j hj idx).symm

theorem sa12de7_memSobolev (m : ℕ) {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) u := by
  have h0 : MemLp u 2 volume := by
    have := sa12de7_pd_memLp hu hc (j := 0) Fin.elim0
    rwa [sa12de7_pd_zero] at this
  refine ⟨h0, ?_⟩
  have hint : ∀ {j : ℕ} (idx : Fin j → Fin d), Integrable (fun ξ => ‖fourierL2 (partialDeriv idx u) ξ‖ ^ 2) volume :=
    fun idx => integrable_norm_sq_fourierL2 (sa12de7_pd_memLp hu hc idx)
  have hsum : Integrable (fun ξ : Euc d => ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
      ∑ idx : Fin j → Fin d, ‖fourierL2 (partialDeriv idx u) ξ‖ ^ 2) volume :=
    integrable_finset_sum _ fun j _ => (integrable_finset_sum _ fun idx _ => hint idx).const_mul _
  exact hsum.congr ((sa12de7_weighted_ae m hu hc).mono fun ξ hξ => hξ.symm)

/-- The extended-norm form (the sorry spec `sobolev_jet_eq` of `HRS.MH.AdjointRdSpec`). -/
theorem sa12de7_sobolevNormE_jet (m : ℕ) {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    sobolevNormE (m : ℝ) u = ENNReal.ofReal (Real.sqrt (jetSq m (fun _ => 1) u)) := by
  unfold sobolevNormE
  rw [if_pos (sa12de7_memSobolev m hu hc), sa12de7_sobolevNormSq_jet m hu hc]

end HRS.MS.SA12DE7
