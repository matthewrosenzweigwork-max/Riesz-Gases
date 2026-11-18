import HRS.MS.SA12DE7B

/-!
# S.A.12(c), packet E7.07 (worker S82Z2), part C: `H^m` convergence of mollified `C_c^∞` functions
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.SA12DE7

open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Limit HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12V3

variable {d : ℕ}

theorem sa12de7_mollify_H {η : Euc d → ℝ} (hη : IsMollifier η) (m : ℕ) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), sobolevNormSq (m : ℝ) (fun x => mollify η ε ψ x - ψ x) ≤ δ := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  have hRψ : ∀ x : Euc d, R < ‖x‖ → ψ x = 0 := fun x hx => by
    by_contra h
    have := hR (subset_tsupport _ (Function.mem_support.2 h))
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  have hRpd : ∀ {j : ℕ} (idx : Fin j → Fin d) (x : Euc d), R < ‖x‖ → partialDeriv idx ψ x = 0 := by
    intro j idx x hx
    by_contra h
    have h1 : iteratedFDeriv ℝ j ψ x ≠ 0 := fun h0 => h (by simp [partialDeriv, h0])
    have h2 := support_iteratedFDeriv_subset (𝕜 := ℝ) (n := j) (f := ψ) (Function.mem_support.2 h1)
    have := hR h2
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  set V : ℝ := (volume (Metric.closedBall (0 : Euc d) (R + 1))).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set K : ℝ := ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * (d : ℝ) ^ j with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (by positivity)
  set δ' : ℝ := min 1 (δ / (K * V + 1)) with hδ'
  have hKV : 0 < K * V + 1 := by positivity
  have hδ'0 : 0 < δ' := lt_min one_pos (div_pos hδ hKV)
  have hδ'1 : δ' ≤ 1 := min_le_left _ _
  have hδ'2 : K * V * δ' ^ 2 ≤ δ := by
    have h1 : δ' ^ 2 ≤ δ' := by nlinarith
    have h2 : δ' ≤ δ / (K * V + 1) := min_le_right _ _
    calc K * V * δ' ^ 2 ≤ K * V * δ' := mul_le_mul_of_nonneg_left h1 (mul_nonneg hK0 hV0)
      _ ≤ (K * V + 1) * δ' := by nlinarith
      _ ≤ (K * V + 1) * (δ / (K * V + 1)) := mul_le_mul_of_nonneg_left h2 hKV.le
      _ = δ := by field_simp
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ j ∈ Finset.range (m + 1), ∀ idx : Fin j → Fin d, ∀ x,
      |mollify η ε (partialDeriv idx ψ) x - partialDeriv idx ψ x| ≤ δ' :=
    (Filter.eventually_all_finset _).2 fun j _ => Filter.eventually_all.2 fun idx =>
      sa12de7_mollify_unif hη (sa12de7_pd_cont hψ idx) (sa12de7_pd_compact hc idx) hδ'0
  have hε1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with ε hε using hε.2.le
  filter_upwards [hev, hε1, self_mem_nhdsWithin] with ε hε hε1 hε0
  have hε0 : 0 < ε := hε0
  have hψli : LocallyIntegrable ψ volume := hψ.continuous.locallyIntegrable
  have hmoll : ContDiff ℝ ∞ (mollify η ε ψ) := sa12v3_mollify_smooth hη hε0 hψli
  set w : Euc d → ℝ := fun x => mollify η ε ψ x - ψ x with hw
  have hwsm : ContDiff ℝ ∞ w := hmoll.sub hψ
  have hwsupp : ∀ x, R + 1 < ‖x‖ → w x = 0 := fun x hx => by
    simp only [hw]
    rw [sa12de7_mollify_supp hη hε0 hε1 hRψ hx, hRψ x (by linarith)]; simp
  have hwc : HasCompactSupport w :=
    HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) (R + 1)) fun x hx => by
      apply hwsupp
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      linarith
  rw [sa12de7_sobolevNormSq_jet m hwsm hwc]
  unfold jetSq
  -- jets of `w`
  have hjet : ∀ {j : ℕ} (idx : Fin j → Fin d) (x : Euc d),
      partialDeriv idx w x = mollify η ε (partialDeriv idx ψ) x - partialDeriv idx ψ x := by
    intro j idx x
    have e1 : partialDeriv idx (mollify η ε ψ) x = mollify η ε (partialDeriv idx ψ) x := by
      rw [sa12de7_mollify_eq_H, sa12de7_mollify_eq_H]
      exact (sa12v3_H_partial (sa12v3_G_cont hη ε).locallyIntegrable hψ hc).2 idx x
    rw [← e1]
    exact sa12de7_pd_sub hmoll hψ idx x
  have hterm : ∀ j ∈ Finset.range (m + 1), ∀ idx : Fin j → Fin d,
      ∫ x, ((fun _ : Euc d => (1 : ℝ)) x * partialDeriv idx w x) ^ 2 ≤ δ' ^ 2 * V := by
    intro j hj idx
    have hint : Integrable (fun x => ((fun _ : Euc d => (1 : ℝ)) x * partialDeriv idx w x) ^ 2) volume := by
      have := (sa12de7_pd_memLp hwsm hwc idx).integrable_sq
      simpa using this
    have hpt : ∀ x, ((fun _ : Euc d => (1 : ℝ)) x * partialDeriv idx w x) ^ 2 ≤
        (Metric.closedBall (0 : Euc d) (R + 1)).indicator (fun _ => δ' ^ 2) x := by
      intro x
      by_cases hx : x ∈ Metric.closedBall (0 : Euc d) (R + 1)
      · rw [Set.indicator_of_mem hx, one_mul, hjet idx x]
        have := hε j hj idx x
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
      · rw [Set.indicator_of_notMem hx, one_mul, hjet idx x]
        rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
        rw [sa12de7_mollify_supp hη hε0 hε1 (fun y hy => hRpd idx y hy) hx, hRpd idx x (by linarith)]
        simp
    refine (integral_mono hint ?_ hpt).trans (le_of_eq ?_)
    · exact (integrable_indicator_iff measurableSet_closedBall).2
        (integrableOn_const (by exact measure_closedBall_lt_top.ne))
    · rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, mul_comm]
      rfl
  calc ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) *
        ∑ idx : Fin j → Fin d, ∫ x, ((fun _ : Euc d => (1 : ℝ)) x * partialDeriv idx w x) ^ 2
      ≤ ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * ∑ _idx : Fin j → Fin d, (δ' ^ 2 * V) := by
        refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        exact Finset.sum_le_sum fun idx _ => hterm j hj idx
    _ = K * V * δ' ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, hK,
          Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        push_cast
        ring
    _ ≤ δ := hδ'2

end HRS.MS.SA12DE7
