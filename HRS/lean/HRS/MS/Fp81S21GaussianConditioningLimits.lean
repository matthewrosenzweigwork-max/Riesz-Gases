import HRS.MS.Fp81S21GaussianConditioningFinite
import HRS.MS.Fp81S21RSValue5

/-! Generic expectation transfer for supplied conditioning and RS data. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators

namespace HRS.Fp81.S21

/-- Transfer the expectations of conditioned right-endpoint sums to the
unconditioned endpoint pairing. The summand identities are the outputs of
finite-to-L¹ conditioning; domination concerns the sums themselves. -/
theorem fp81s21_conditioned_rs_expectation_limit
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Measure Ω) (H : ℝ) (hH : 0 ≤ H)
    (A : Ω → ℝ → E →L[ℝ] ℝ) (F : Ω → ℝ → E)
    (W : fp81s21_RSBVWindow P H A F)
    (L : Ω → E →L[ℝ] ℝ) (D : Ω → E)
    (N : ℕ → ℕ) (t : ℕ → ℕ → ℝ) (mesh : ℕ → ℝ)
    (ht0 : ∀ n, t n 0 = 0) (htN : ∀ n, t n (N n) = H)
    (htmono : ∀ n i, i < N n → t n i ≤ t n (i + 1))
    (htmesh : ∀ n i, i < N n → t n (i + 1) - t n i ≤ mesh n)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hzero : ∀ᵐ ω ∂P, F ω 0 = 0)
    (hend : ∀ᵐ ω ∂P, F ω H = D ω)
    (hcond : ∀ n i, i < N n → Integrable
      (fun ω => A ω (t n (i + 1)) (F ω (t n (i + 1)) - F ω (t n i))) P)
    (huncond : ∀ n i, i < N n → Integrable
      (fun ω => L ω (F ω (t n (i + 1)) - F ω (t n i))) P)
    (hpair : ∀ n i, i < N n →
      (∫ ω, A ω (t n (i + 1)) (F ω (t n (i + 1)) - F ω (t n i)) ∂P) =
      ∫ ω, L ω (F ω (t n (i + 1)) - F ω (t n i)) ∂P)
    (V : Ω → ℝ) (hV : Integrable V P)
    (hsum_meas : ∀ n, AEStronglyMeasurable
      (fun ω => ∑ i ∈ Finset.range (N n),
        A ω (t n (i + 1)) (F ω (t n (i + 1)) - F ω (t n i))) P)
    (hsum_bound : ∀ n, ∀ᵐ ω ∂P,
      ‖∑ i ∈ Finset.range (N n),
        A ω (t n (i + 1)) (F ω (t n (i + 1)) - F ω (t n i))‖ ≤ V ω)
    (hsum_limit : ∀ᵐ ω ∂P, Tendsto
      (fun n => ∑ i ∈ Finset.range (N n),
        A ω (t n (i + 1)) (F ω (t n (i + 1)) - F ω (t n i)))
      atTop (𝓝 (W.value 0 H ω))) :
    Integrable (W.value 0 H) P ∧ Integrable (fun ω => L ω (D ω)) P ∧
      (∫ ω, W.value 0 H ω ∂P) = ∫ ω, L ω (D ω) ∂P := by
  classical
  let S : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ Finset.range (N n),
    A ω (t n (i + 1)) (F ω (t n (i + 1)) - F ω (t n i))
  let U : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ Finset.range (N n),
    L ω (F ω (t n (i + 1)) - F ω (t n i))
  have hU : ∀ n, U n =ᵐ[P] fun ω => L ω (D ω) := by
    intro n
    filter_upwards [hzero, hend] with ω hz he
    dsimp [U]
    simp only [map_sub]
    rw [Finset.sum_range_sub (fun i => L ω (F ω (t n i)))]
    rw [htN, ht0, he, hz, map_zero, sub_zero]
  have hUi (n : ℕ) : Integrable (U n) P := by
    exact integrable_finset_sum _ (fun i hi => huncond n i (Finset.mem_range.mp hi))
  have hDi : Integrable (fun ω => L ω (D ω)) P := (hUi 0).congr (hU 0)
  have hEq (n : ℕ) : (∫ ω, S n ω ∂P) = ∫ ω, L ω (D ω) ∂P := by
    calc
      (∫ ω, S n ω ∂P) = ∑ i ∈ Finset.range (N n),
          ∫ ω, A ω (t n (i + 1)) (F ω (t n (i + 1)) - F ω (t n i)) ∂P :=
        integral_finset_sum _ (fun i hi => hcond n i (Finset.mem_range.mp hi))
      _ = ∑ i ∈ Finset.range (N n),
          ∫ ω, L ω (F ω (t n (i + 1)) - F ω (t n i)) ∂P := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hpair n i (Finset.mem_range.mp hi)
      _ = ∫ ω, U n ω ∂P :=
        (integral_finset_sum _ (fun i hi => huncond n i (Finset.mem_range.mp hi))).symm
      _ = ∫ ω, L ω (D ω) ∂P := integral_congr_ae (hU n)
  have hlim : Tendsto (fun n => ∫ ω, S n ω ∂P) atTop
      (𝓝 (∫ ω, W.value 0 H ω ∂P)) :=
    tendsto_integral_of_dominated_convergence V hsum_meas hV hsum_bound hsum_limit
  have hconst : Tendsto (fun n => ∫ ω, S n ω ∂P) atTop
      (𝓝 (∫ ω, L ω (D ω) ∂P)) := by
    simpa only [hEq] using tendsto_const_nhds
  exact ⟨W.value_integrable 0 H le_rfl hH le_rfl, hDi, tendsto_nhds_unique hlim hconst⟩

/-- L¹ convergence of directions is preserved by uniformly bounded random
linear functionals. Measurability is stated for the scalar pairings, so no
separability of an operator dual is required. -/
theorem fp81s21_integral_pairing_tendsto_of_l1
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Measure Ω) (L : Ω → E →L[ℝ] ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hL : ∀ ω, ‖L ω‖ ≤ K)
    (D : Ω → E) (Dn : ℕ → Ω → E)
    (hD : Integrable D P) (hDn : ∀ n, Integrable (Dn n) P)
    (hm : AEStronglyMeasurable (fun ω => L ω (D ω)) P)
    (hmn : ∀ n, AEStronglyMeasurable (fun ω => L ω (Dn n ω)) P)
    (hlim : Tendsto (fun n => ∫ ω, ‖Dn n ω - D ω‖ ∂P) atTop (𝓝 0)) :
    Integrable (fun ω => L ω (D ω)) P ∧
    (∀ n, Integrable (fun ω => L ω (Dn n ω)) P) ∧
    Tendsto (fun n => ∫ ω, L ω (Dn n ω) ∂P) atTop
      (𝓝 (∫ ω, L ω (D ω) ∂P)) := by
  have hpair (f : Ω → E) (hf : Integrable f P)
      (hmf : AEStronglyMeasurable (fun ω => L ω (f ω)) P) :
      Integrable (fun ω => L ω (f ω)) P := by
    apply (hf.norm.const_mul K).mono' hmf
    filter_upwards [] with ω
    exact (L ω).le_opNorm (f ω) |>.trans
      (mul_le_mul_of_nonneg_right (hL ω) (norm_nonneg _))
  have hi := hpair D hD hm
  have hin n := hpair (Dn n) (hDn n) (hmn n)
  refine ⟨hi, hin, ?_⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hupper : Tendsto (fun n => K * ∫ ω, ‖Dn n ω - D ω‖ ∂P) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun n => norm_nonneg _) ?_
  intro n
  have hdiff := (hin n).sub hi
  calc
    ‖(∫ ω, L ω (Dn n ω) ∂P) - (∫ ω, L ω (D ω) ∂P)‖ =
        ‖∫ ω, (L ω (Dn n ω) - L ω (D ω)) ∂P‖ := by
          rw [integral_sub (hin n) hi]
    _ ≤ ∫ ω, ‖L ω (Dn n ω) - L ω (D ω)‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, K * ‖Dn n ω - D ω‖ ∂P := by
      apply integral_mono_ae hdiff.norm ((hDn n).sub hD |>.norm.const_mul K)
      filter_upwards [] with ω
      change ‖L ω (Dn n ω) - L ω (D ω)‖ ≤ K * ‖Dn n ω - D ω‖
      rw [← map_sub]
      exact ((L ω).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hL ω) (norm_nonneg _))
    _ = K * ∫ ω, ‖Dn n ω - D ω‖ ∂P := integral_const_mul _ _

#print axioms fp81s21_integral_pairing_tendsto_of_l1
#print axioms fp81s21_conditioned_rs_expectation_limit
end HRS.Fp81.S21
end
