import HRS.MS.R26T8AP06c2

/-!
# S8.2 local Newton layer, packet T8A.P06d (part 5): continuous extension across `z = 0` from a uniform Cauchy rate
`r26t8a_cauchy_ext`: let `W` be a complete normed space and `nu : E -> E -> W` with (i) `|nu X z - nu X z'| <= K X (|z|^eps + |z'|^eps)` for `0 < |z|, |z'| <= 1/2`,
(ii) `nu` jointly continuous on `{z != 0}`, (iii) `K` locally bounded.  Then `(X,z) |-> nu X z` (`z != 0`) has a continuous extension to `E x E`.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_cauchy_ext (hd : 1 ≤ d) {W : Type} [NormedAddCommGroup W] [CompleteSpace W]
    (nu : Euc d → Euc d → W) (K : Euc d → ℝ) (hK0 : ∀ X, 0 ≤ K X) {ε : ℝ} (hε : 0 < ε)
    (hC : ∀ X z z' : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 1 / 2 → 0 < ‖z'‖ → ‖z'‖ ≤ 1 / 2 →
      ‖nu X z - nu X z'‖ ≤ K X * (‖z‖ ^ ε + ‖z'‖ ^ ε))
    (hcont : ContinuousOn (fun w : Euc d × Euc d => nu w.1 w.2) {w | w.2 ≠ 0})
    (hK : ∀ X0 : Euc d, ∃ r K0 : ℝ, 0 < r ∧ ∀ X ∈ Metric.ball X0 r, K X ≤ K0) :
    ∃ g : Euc d × Euc d → W, Continuous g ∧ ∀ w : Euc d × Euc d, w.2 ≠ 0 → g w = nu w.1 w.2 := by
  obtain ⟨e, he⟩ := r26t8a_unit_vec hd
  set zn : ℕ → Euc d := fun n => ((1 / 2 : ℝ) ^ (n + 1)) • e with hzn
  have hnn : ∀ n, ‖zn n‖ = (1 / 2 : ℝ) ^ (n + 1) := fun n => by
    rw [hzn]; simp only [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < (1 / 2) ^ (n + 1))]
  have hzpos : ∀ n, 0 < ‖zn n‖ := fun n => by rw [hnn]; positivity
  have hzle : ∀ n, ‖zn n‖ ≤ 1 / 2 := fun n => by
    rw [hnn]
    calc (1 / 2 : ℝ) ^ (n + 1) ≤ (1 / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 2 := pow_one _
  have hs : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp (tendsto_add_atTop_nat 1)
  have hrate : Tendsto (fun n : ℕ => ‖zn n‖ ^ ε) atTop (𝓝 0) := by
    have hc : Continuous fun t : ℝ => t ^ ε := Real.continuous_rpow_const hε.le
    have := (hc.tendsto (0 : ℝ)).comp hs
    rw [Real.zero_rpow hε.ne'] at this
    convert this using 1
    funext n
    simp only [Function.comp, hnn]
  -- the limit
  have hcauchy : ∀ X, CauchySeq (fun n => nu X (zn n)) := fun X => by
    rw [Metric.cauchySeq_iff']
    intro η hη
    have h1 : Tendsto (fun n : ℕ => 2 * K X * ‖zn n‖ ^ ε) atTop (𝓝 0) := by
      simpa using hrate.const_mul (2 * K X)
    obtain ⟨N, hN⟩ := ((h1.eventually (gt_mem_nhds hη)).and (eventually_ge_atTop 0)).exists_forall_of_atTop
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    have hmono : ‖zn n‖ ^ ε ≤ ‖zn N‖ ^ ε := by
      refine Real.rpow_le_rpow (norm_nonneg _) ?_ hε.le
      rw [hnn, hnn]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hb := hC X (zn n) (zn N) (hzpos n) (hzle n) (hzpos N) (hzle N)
    have hKnn : 0 ≤ K X := hK0 X
    calc ‖nu X (zn n) - nu X (zn N)‖ ≤ K X * (‖zn n‖ ^ ε + ‖zn N‖ ^ ε) := hb
      _ ≤ K X * (‖zn N‖ ^ ε + ‖zn N‖ ^ ε) := by gcongr
      _ = 2 * K X * ‖zn N‖ ^ ε := by ring
      _ < η := (hN N le_rfl).1
  choose Λ hΛ using fun X => cauchySeq_tendsto_of_complete (hcauchy X)
  have hlim : ∀ X z, 0 < ‖z‖ → ‖z‖ ≤ 1 / 2 → ‖nu X z - Λ X‖ ≤ K X * ‖z‖ ^ ε := fun X z hz hz1 => by
    have h1 : Tendsto (fun n => ‖nu X z - nu X (zn n)‖) atTop (𝓝 ‖nu X z - Λ X‖) :=
      (tendsto_const_nhds.sub (hΛ X)).norm
    have h2 : Tendsto (fun n => K X * (‖z‖ ^ ε + ‖zn n‖ ^ ε)) atTop (𝓝 (K X * (‖z‖ ^ ε + 0))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.add hrate)
    have := le_of_tendsto_of_tendsto h1 h2 (Eventually.of_forall fun n => hC X z (zn n) hz hz1 (hzpos n) (hzle n))
    simpa using this
  -- continuity of the limit in X
  have hΛc : Continuous Λ := by
    rw [continuous_iff_continuousAt]
    intro X0
    obtain ⟨r, K0, hr, hKb⟩ := hK X0
    refine r26t8a_param_limit_continuousAt hd (fun X z => nu X z) Λ hε X0 hr (K := K0) ?_ ?_
    · intro z hz
      exact hcont.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun X _ => show (X, z).2 ≠ 0 from norm_pos_iff.1 hz)
    · intro X hX z hz hz1
      exact (hlim X z hz hz1).trans (mul_le_mul_of_nonneg_right (hKb X hX) (Real.rpow_nonneg (norm_nonneg _) _))
  classical
  set g : Euc d × Euc d → W := fun w => if w.2 = 0 then Λ w.1 else nu w.1 w.2 with hg
  refine ⟨g, ?_, fun w hw => by simp [hg, hw]⟩
  rw [continuous_iff_continuousAt]
  intro w0
  by_cases hw0 : w0.2 = 0
  · obtain ⟨r, K0, hr, hKb⟩ := hK w0.1
    have hK00 : 0 ≤ K0 := (hK0 w0.1).trans (hKb w0.1 (Metric.mem_ball_self hr))
    have hgw0 : g w0 = Λ w0.1 := by simp [hg, hw0]
    have h1 : Tendsto (fun w : Euc d × Euc d => Λ w.1) (𝓝 w0) (𝓝 (Λ w0.1)) := (hΛc.tendsto w0.1).comp (continuous_fst.tendsto w0)
    have h3 : Tendsto (fun w : Euc d × Euc d => K0 * ‖w.2‖ ^ ε) (𝓝 w0) (𝓝 0) := by
      have hc : Continuous fun w : Euc d × Euc d => K0 * ‖w.2‖ ^ ε :=
        continuous_const.mul ((Real.continuous_rpow_const hε.le).comp continuous_snd.norm)
      have := hc.tendsto w0
      rwa [hw0, norm_zero, Real.zero_rpow hε.ne', mul_zero] at this
    have hev : ∀ᶠ w in 𝓝 w0, ‖g w - Λ w.1‖ ≤ K0 * ‖w.2‖ ^ ε := by
      have hn1 : ∀ᶠ w in 𝓝 w0, w.1 ∈ Metric.ball w0.1 r := continuous_fst.continuousAt.preimage_mem_nhds
        (Metric.ball_mem_nhds _ hr)
      have hn2 : ∀ᶠ w in 𝓝 w0, ‖w.2‖ < 1 / 2 := by
        have : ContinuousAt (fun w : Euc d × Euc d => ‖w.2‖) w0 := continuous_snd.norm.continuousAt
        exact this.eventually (gt_mem_nhds (show ‖w0.2‖ < 1 / 2 by rw [hw0, norm_zero]; norm_num))
      filter_upwards [hn1, hn2] with w h1 h2
      by_cases hz : w.2 = 0
      · simp [hg, hz, Real.zero_rpow hε.ne']
      · have := hlim w.1 w.2 (norm_pos_iff.2 hz) h2.le
        simp only [hg, hz, if_false]
        exact this.trans (mul_le_mul_of_nonneg_right (hKb _ h1) (Real.rpow_nonneg (norm_nonneg _) _))
    have h4 : Tendsto (fun w : Euc d × Euc d => g w - Λ w.1) (𝓝 w0) (𝓝 0) :=
      squeeze_zero_norm' hev h3
    have := h4.add h1
    rw [zero_add] at this
    rw [ContinuousAt, hgw0]
    simpa using this
  · have hopen : IsOpen {w : Euc d × Euc d | w.2 ≠ 0} := isOpen_ne.preimage continuous_snd
    have : ContinuousAt (fun w : Euc d × Euc d => nu w.1 w.2) w0 := hcont.continuousAt (hopen.mem_nhds hw0)
    refine this.congr ?_
    filter_upwards [hopen.mem_nhds hw0] with w hw
    simp [hg, show w.2 ≠ 0 from hw]

end HRS.MS.R26T8A
