import HRS.MS.R26T8AP06c

/-!
# S8.2 local Newton layer, packet T8A.P06c (part 2): uniqueness and parameter continuity of limits
`r26t8a_limit_unique`: a limit with a power rate is unique.  `r26t8a_param_limit_continuousAt`: if `f X z -> Lambda X` as `z -> 0` with a rate
`K |z|^eps` uniform for `X` in a ball and each `f . z` is continuous, then `Lambda` is continuous at the centre (uniform limit of continuous maps).
-/

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace HRS.MS.R26T8A
open HRS

theorem r26t8a_unit_vec {d : ℕ} (hd : 1 ≤ d) : ∃ e : Euc d, ‖e‖ = 1 :=
  ⟨EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ), by simp⟩

theorem r26t8a_limit_unique {d : ℕ} (hd : 1 ≤ d) {V : Type} [NormedAddCommGroup V] (f : Euc d → V) {ε K K' : ℝ}
    (hε : 0 < ε) {Λ Λ' : V} (h1 : ∀ z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 1 / 2 → ‖f z - Λ‖ ≤ K * ‖z‖ ^ ε)
    (h2 : ∀ z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 1 / 2 → ‖f z - Λ'‖ ≤ K' * ‖z‖ ^ ε) : Λ = Λ' := by
  obtain ⟨e, he⟩ := r26t8a_unit_vec hd
  have hlim : Tendsto (fun t : ℝ => (K + K') * t ^ ε) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun t : ℝ => (K + K') * t ^ ε := continuous_const.mul (Real.continuous_rpow_const hε.le)
    have := hc.tendsto (0 : ℝ)
    rw [Real.zero_rpow hε.ne', mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖Λ - Λ'‖ ≤ (K + K') * t ^ ε := by
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with t ht
    have hn : ‖t • e‖ = t := by rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos ht.1]
    have a1 := h1 (t • e) (by rw [hn]; exact ht.1) (by rw [hn]; exact ht.2)
    have a2 := h2 (t • e) (by rw [hn]; exact ht.1) (by rw [hn]; exact ht.2)
    rw [hn] at a1 a2
    calc ‖Λ - Λ'‖ = ‖(f (t • e) - Λ') - (f (t • e) - Λ)‖ := by congr 1; abel
      _ ≤ ‖f (t • e) - Λ'‖ + ‖f (t • e) - Λ‖ := norm_sub_le _ _
      _ ≤ _ := by nlinarith
  have := ge_of_tendsto hlim hle
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

theorem r26t8a_param_limit_continuousAt {d : ℕ} (hd : 1 ≤ d) {S V : Type} [NormedAddCommGroup S] [NormedSpace ℝ S]
    [NormedAddCommGroup V] (f : S → Euc d → V) (Λ : S → V) {ε : ℝ} (hε : 0 < ε) (X0 : S) {r K : ℝ} (hr : 0 < r)
    (hf : ∀ z : Euc d, 0 < ‖z‖ → ContinuousOn (fun X => f X z) (Metric.ball X0 r))
    (hb : ∀ X ∈ Metric.ball X0 r, ∀ z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 1 / 2 → ‖f X z - Λ X‖ ≤ K * ‖z‖ ^ ε) :
    ContinuousAt Λ X0 := by
  obtain ⟨e, he⟩ := r26t8a_unit_vec hd
  set zn : ℕ → Euc d := fun n => ((1 / 2 : ℝ) ^ (n + 1)) • e with hzn
  have hnn : ∀ n, ‖zn n‖ = (1 / 2 : ℝ) ^ (n + 1) := fun n => by
    rw [hzn]; simp only [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < (1 / 2) ^ (n + 1))]
  have hs : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp (tendsto_add_atTop_nat 1)
  have hK : Tendsto (fun n : ℕ => K * ((1 / 2 : ℝ) ^ (n + 1)) ^ ε) atTop (𝓝 0) := by
    have hc : Continuous fun t : ℝ => K * t ^ ε := continuous_const.mul (Real.continuous_rpow_const hε.le)
    have := (hc.tendsto (0 : ℝ)).comp hs
    rw [Real.zero_rpow hε.ne', mul_zero] at this
    exact this
  have hu : TendstoUniformlyOn (fun n X => f X (zn n)) Λ atTop (Metric.ball X0 r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro η hη
    have := (hK.eventually (gt_mem_nhds hη)).and (eventually_ge_atTop 0)
    filter_upwards [this] with n hn X hX
    have hpos : 0 < ‖zn n‖ := by rw [hnn]; positivity
    have hle : ‖zn n‖ ≤ 1 / 2 := by
      rw [hnn]; calc (1 / 2 : ℝ) ^ (n + 1) ≤ (1 / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ = 1 / 2 := pow_one _
    have := hb X hX (zn n) hpos hle
    rw [hnn] at this
    rw [dist_eq_norm, ← norm_neg, neg_sub]
    exact lt_of_le_of_lt this hn.1
  have hcont : ContinuousOn Λ (Metric.ball X0 r) :=
    hu.continuousOn (Eventually.of_forall fun n => hf (zn n) (by rw [hnn]; positivity)).frequently
  exact hcont.continuousAt (Metric.ball_mem_nhds X0 hr)

end HRS.MS.R26T8A
