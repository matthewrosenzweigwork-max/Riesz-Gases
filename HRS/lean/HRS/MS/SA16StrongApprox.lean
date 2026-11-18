import HRS.MS.SA16StrongConvN

/-!
# S.A.16: Schwartz approximation of a `C_b^k` coefficient

`sa16y_approx`: if `μ ∈ C^k` with `‖D^j μ‖ ≤ B` (`j ≤ k`), there are Schwartz functions `μ_n` with
`‖D^j μ_n‖ ≤ B'` (`B'` depending only on `d, k, B`) and `D^j μ_n → D^j μ` pointwise (`j ≤ k`).
They are `μ_n = χ_{n+1} (ρ_n ⋆ μ)` (mollification then cutoff).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16
open HRS HRS.Whole HRS.Whole.AppendixA

section Approx
variable {d : ℕ}

/-- the mollifier bump at scale `1/(n+1)` -/
def sa16y_bumpn (d n : ℕ) : ContDiffBump (0 : Euc d) :=
  ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity, by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have h2 : 1 / (2 * ((n : ℝ) + 1)) = (1 / ((n : ℝ) + 1)) / 2 := by field_simp
    rw [h2]; linarith⟩

/-- the normalised mollifier -/
def sa16y_rho (d n : ℕ) : Euc d → ℝ := (sa16y_bumpn d n).normed volume

lemma sa16y_rho_nonneg (n : ℕ) (z : Euc d) : 0 ≤ sa16y_rho d n z := (sa16y_bumpn d n).nonneg_normed z

lemma sa16y_rho_int (n : ℕ) : ∫ z, sa16y_rho d n z = 1 := (sa16y_bumpn d n).integral_normed

lemma sa16y_rho_smooth (n : ℕ) : ContDiff ℝ ∞ (sa16y_rho d n) := (sa16y_bumpn d n).contDiff_normed

lemma sa16y_rho_supp (n : ℕ) (z : Euc d) (hz : 1 / ((n : ℝ) + 1) < ‖z‖) : sa16y_rho d n z = 0 := by
  have : z ∉ Function.support (sa16y_rho d n) := by
    unfold sa16y_rho
    rw [(sa16y_bumpn d n).support_normed_eq]
    intro h
    rw [Metric.mem_ball, dist_zero_right] at h
    have : (sa16y_bumpn d n).rOut = 1 / ((n : ℝ) + 1) := rfl
    linarith
  simpa using this

lemma sa16y_rho_compact (n : ℕ) : HasCompactSupport (sa16y_rho d n) :=
  (sa16y_bumpn d n).hasCompactSupport_normed

lemma sa16y_rho_integrable (n : ℕ) : Integrable (sa16y_rho d n) :=
  (sa16y_rho_smooth n).continuous.integrable_of_hasCompactSupport (sa16y_rho_compact n)

lemma sa16y_conv_eq_convolution (k g : Euc d → ℝ) (x : Euc d) :
    sa16j_conv k g x = (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
  rw [convolution_def]
  simp [sa16j_conv]

lemma sa16y_mollify_smooth (n : ℕ) {g : Euc d → ℝ} (hg : Continuous g) :
    ContDiff ℝ ∞ (sa16j_conv (sa16y_rho d n) g) := by
  have : sa16j_conv (sa16y_rho d n) g = fun x => (sa16y_rho d n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
    funext x; exact sa16y_conv_eq_convolution _ _ x
  rw [this]
  exact (sa16y_rho_compact n).contDiff_convolution_left _ (sa16y_rho_smooth n) hg.locallyIntegrable

lemma sa16y_mollify_bound (n : ℕ) {g : Euc d → ℝ} (hg : Continuous g) {B : ℝ}
    (hB : ∀ y, |g y| ≤ B) (x : Euc d) : |sa16j_conv (sa16y_rho d n) g x| ≤ B := by
  unfold sa16j_conv
  have hint : Integrable (fun z => sa16y_rho d n z * g (x - z)) := by
    refine Integrable.mono' ((sa16y_rho_integrable n).norm.mul_const B)
      ((sa16y_rho_integrable n).aestronglyMeasurable.mul
        (hg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall fun z => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hB _) (norm_nonneg _)
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  calc ∫ z, ‖sa16y_rho d n z * g (x - z)‖ ≤ ∫ z, sa16y_rho d n z * B := by
        refine integral_mono hint.norm ((sa16y_rho_integrable n).mul_const B) fun z => ?_
        rw [norm_mul, Real.norm_of_nonneg (sa16y_rho_nonneg n z)]
        exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hB _) (sa16y_rho_nonneg n z)
    _ = B := by rw [integral_mul_const, sa16y_rho_int, one_mul]

lemma sa16y_mollify_tendsto {g : Euc d → ℝ} (hg : Continuous g) (x : Euc d) :
    Tendsto (fun n => sa16j_conv (sa16y_rho d n) g x) atTop (𝓝 (g x)) := by
  have h := ContDiffBump.convolution_tendsto_right_of_continuous (μ := (volume : Measure (Euc d)))
    (φ := fun n : ℕ => sa16y_bumpn d n) (l := atTop) ?_ hg x
  · simpa [sa16y_conv_eq_convolution, sa16y_rho] using h
  · have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact this

theorem sa16y_approx (d k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (μ : Euc d → ℝ), ContDiff ℝ k μ → ∀ B : ℝ,
      (∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j μ x‖ ≤ B) →
      ∃ μs : ℕ → 𝓢(Euc d, ℝ),
        (∀ n, ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (⇑(μs n)) x‖ ≤ K * B) ∧
        ∀ j ≤ k, ∀ x, Tendsto (fun n => ‖iteratedFDeriv ℝ j (⇑(μs n)) x - iteratedFDeriv ℝ j μ x‖)
          atTop (𝓝 0) := by
  obtain ⟨Bχ, hBχ0, hBχ⟩ := sa16j_cut_bound d k
  refine ⟨2 ^ k * Bχ * ((d : ℝ) + 1) ^ k, by positivity, fun μ hμ B hB => ?_⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  have hμc : Continuous μ := hμ.continuous
  -- mollified functions
  set m : ℕ → Euc d → ℝ := fun n => sa16j_conv (sa16y_rho d n) μ with hm
  have hmsm : ∀ n, ContDiff ℝ ∞ (m n) := fun n => sa16y_mollify_smooth n hμc
  -- coordinate derivatives of the mollified functions
  have hpdm : ∀ n, ∀ j ≤ k, ∀ r : Fin j → Fin d,
      partialDeriv r (m n) = sa16j_conv (sa16y_rho d n) (partialDeriv r μ) := by
    intro n j hj r
    have hsupp : ∀ z, 1 / ((n : ℝ) + 1) < ‖z‖ → sa16y_rho d n z = 0 := fun z hz => sa16y_rho_supp n z hz
    exact sa16y_conv_pdN hsupp (by positivity) (sa16y_rho_integrable n) j (k - j) r μ (by
      have : j + (k - j) = k := by omega
      rw [this]; exact hμ)
  have hpdc : ∀ j ≤ k, ∀ r : Fin j → Fin d, Continuous (partialDeriv r μ) := by
    intro j hj r
    have := sa16y_pd_contDiffN (j := j) (r := k - j) (f := μ) (by
      have : j + (k - j) = k := by omega
      rw [this]; exact hμ) r
    exact this.continuous
  have hpdB : ∀ j ≤ k, ∀ r : Fin j → Fin d, ∀ y, |partialDeriv r μ y| ≤ B := fun j hj r y =>
    (sa16y_pd_le_iter μ y r).trans (hB j hj y)
  -- bounds for the mollified functions
  have hmB : ∀ n, ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (m n) x‖ ≤ ((d : ℝ) + 1) ^ k * B := by
    intro n j hj x
    refine (sa16j_norm_iter_le (m n) x j).trans ?_
    have h1 : ∀ r : Fin j → Fin d, |partialDeriv r (m n) x| ≤ B := by
      intro r
      rw [hpdm n j hj r]
      exact sa16y_mollify_bound n (hpdc j hj r) (hpdB j hj r) x
    calc ∑ r : Fin j → Fin d, |partialDeriv r (m n) x| ≤ ∑ r : Fin j → Fin d, B :=
          Finset.sum_le_sum fun r _ => h1 r
      _ = (d : ℝ) ^ j * B := by simp [Finset.sum_const]
      _ ≤ ((d : ℝ) + 1) ^ k * B := by
          refine mul_le_mul_of_nonneg_right ?_ hB0
          calc (d : ℝ) ^ j ≤ ((d : ℝ) + 1) ^ j :=
                pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) _
            _ ≤ ((d : ℝ) + 1) ^ k :=
                pow_le_pow_right₀ (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg _; linarith) hj
  -- convergence of the mollified derivatives
  have hmT : ∀ j ≤ k, ∀ x, Tendsto (fun n => ‖iteratedFDeriv ℝ j (m n) x - iteratedFDeriv ℝ j μ x‖)
      atTop (𝓝 0) := by
    intro j hj x
    have hD : ContDiff ℝ (j + (k - j) : ℕ) μ := by
      have : j + (k - j) = k := by omega
      rw [this]; exact hμ
    have hcoord : ∀ r : Fin j → Fin d, Tendsto (fun n => |partialDeriv r (m n) x - partialDeriv r μ x|)
        atTop (𝓝 0) := by
      intro r
      have h := sa16y_mollify_tendsto (hpdc j hj r) x
      have h' : Tendsto (fun n => partialDeriv r (m n) x) atTop (𝓝 (partialDeriv r μ x)) := by
        refine h.congr fun n => ?_
        rw [hpdm n j hj r]
      have := (h'.sub_const (partialDeriv r μ x)).abs
      simpa using this
    have hsum : Tendsto (fun n => ∑ r : Fin j → Fin d, |partialDeriv r (m n) x - partialDeriv r μ x|)
        atTop (𝓝 0) := by
      have := tendsto_finsetSum (Finset.univ : Finset (Fin j → Fin d)) (fun r _ => hcoord r)
      simpa using this
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hsum
    refine (sa16j_ml _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [partialDeriv]
  -- cutoff
  set μs : ℕ → 𝓢(Euc d, ℝ) := fun n =>
    (sa16j_cutf_support (m n) (show (0 : ℝ) < (n : ℝ) + 1 by positivity)).toSchwartzMap
      (sa16j_cutf_contDiff (hmsm n) ((n : ℝ) + 1)) with hμs
  have hμsfun : ∀ n, ⇑(μs n) = sa16j_cutf d ((n : ℝ) + 1) (m n) := fun n => rfl
  refine ⟨μs, ?_, ?_⟩
  · intro n j hj x
    rw [hμsfun]
    have h4 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (sa16j_chi_contDiff d ((n : ℝ) + 1)) (hmsm n) x
      (n := j) (by exact_mod_cast le_top)
    refine h4.trans ?_
    have hR1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg _; linarith
    have h5 : ∀ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (sa16j_chi d ((n : ℝ) + 1)) x‖ *
        ‖iteratedFDeriv ℝ (j - i) (m n) x‖ ≤ (j.choose i : ℝ) * (Bχ * (((d : ℝ) + 1) ^ k * B)) := by
      intro i hi
      have hi' : i ≤ j := by have := Finset.mem_range.1 hi; omega
      have hd1 := hBχ ((n : ℝ) + 1) hR1 i (hi'.trans hj) x
      have hd2 := hmB n (j - i) (by omega) x
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hd1 hd2 (norm_nonneg _) hBχ0) (Nat.cast_nonneg _)
    refine (Finset.sum_le_sum h5).trans ?_
    rw [← Finset.sum_mul]
    have hch : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) = 2 ^ j := by
      exact_mod_cast Nat.sum_range_choose j
    rw [hch]
    have : (2 : ℝ) ^ j ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hj
    calc (2 : ℝ) ^ j * (Bχ * (((d : ℝ) + 1) ^ k * B)) ≤ 2 ^ k * (Bχ * (((d : ℝ) + 1) ^ k * B)) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = 2 ^ k * Bχ * ((d : ℝ) + 1) ^ k * B := by ring
  · intro j hj x
    refine (hmT j hj x).congr' ?_
    filter_upwards [eventually_gt_atTop ⌈‖x‖⌉₊] with n hn
    have hxn : ‖x‖ < (n : ℝ) + 1 := by
      have := Nat.le_ceil ‖x‖
      have h2 : (⌈‖x‖⌉₊ : ℝ) < n := by exact_mod_cast hn
      linarith
    have hev : sa16j_cutf d ((n : ℝ) + 1) (m n) =ᶠ[𝓝 x] m n := by
      have : Metric.ball (0 : Euc d) ((n : ℝ) + 1) ∈ 𝓝 x :=
        Metric.isOpen_ball.mem_nhds (by simpa using hxn)
      filter_upwards [this] with y hy
      have hy' : ‖y‖ ≤ (n : ℝ) + 1 := by simpa using (mem_ball_zero_iff.1 hy).le
      simp [sa16j_cutf, sa16j_chi_one d (show (0 : ℝ) < (n : ℝ) + 1 by positivity) hy']
    rw [hμsfun, (hev.iteratedFDeriv ℝ j).self_of_nhds]

end Approx

end HRS.Whole.AppendixA.Phase2SA16
