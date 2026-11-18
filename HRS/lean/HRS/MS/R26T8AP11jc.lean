import HRS.MS.R26T8AP11fin

/-!
# S8.2 nonlocal layer: cutoff jets and the envelope shift (P11e, part 4 constants)
`r26t8a_chi_jet_zero`, `r26t8a_chi_jet_bound`: the jets of the cutoff vanish for `|z| >= 2` and are bounded.
`r26t8a_env_shift`: `1 + t^(alpha-sigma-(q-i)) (1+|log t|)^(b+1) <= K (1 + (min 1 t)^(-(sigma-alpha+q)) (1+|log min 1 t|)^(b+1))` on `0 < t < 2`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_chi_jet_zero {d : ℕ} {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (i : ℕ) {z : Euc d}
    (hz : 2 ≤ ‖z‖) : iteratedFDeriv ℝ i chi z = 0 := by
  have hf : Continuous (iteratedFDeriv ℝ i chi) :=
    hchi.1.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have ht : Tendsto (fun t : ℝ => t • z) (𝓝[>] (1 : ℝ)) (𝓝 z) := by
    have : Tendsto (fun t : ℝ => t • z) (𝓝 (1 : ℝ)) (𝓝 ((1 : ℝ) • z)) :=
      (continuous_id.smul continuous_const).tendsto 1
    rw [one_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun t : ℝ => iteratedFDeriv ℝ i chi (t • z)) (𝓝[>] (1 : ℝ))
      (𝓝 (iteratedFDeriv ℝ i chi z)) := (hf.tendsto z).comp ht
  have h2 : (fun _ : ℝ => (0 : (Euc d) [×i]→L[ℝ] ℝ)) =ᶠ[𝓝[>] (1 : ℝ)]
      fun t : ℝ => iteratedFDeriv ℝ i chi (t • z) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (1 : ℝ) < t := ht
    have hn : 2 < ‖t • z‖ := by
      rw [norm_smul, Real.norm_of_nonneg (by linarith)]
      nlinarith
    have hev : chi =ᶠ[𝓝 (t • z)] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hn] with w hw
      exact hchi.2.2.2.2 w hw.le
    rw [(hev.iteratedFDeriv ℝ i).self_of_nhds]
    simp
  exact tendsto_nhds_unique h1 (tendsto_const_nhds.congr' h2)

theorem r26t8a_chi_jet_bound {d : ℕ} {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (k : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ i ≤ k, ∀ z : Euc d, ‖iteratedFDeriv ℝ i chi z‖ ≤ D := by
  have h : ∀ i : ℕ, ∃ Di : ℝ, ∀ z ∈ closedBall (0 : Euc d) 2, ‖iteratedFDeriv ℝ i chi z‖ ≤ Di := fun i =>
    (isCompact_closedBall _ _).exists_bound_of_continuousOn
      (hchi.1.continuous_iteratedFDeriv (by exact_mod_cast le_top)).continuousOn
  choose Dm hDm using h
  have hs0 : 0 ≤ ∑ i ∈ Finset.range (k + 1), |Dm i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  refine ⟨∑ i ∈ Finset.range (k + 1), |Dm i|, hs0, fun i hi z => ?_⟩
  by_cases hz : ‖z‖ ≤ 2
  · exact (hDm i z (by simpa using hz)).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |Dm i|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega))))
  · rw [r26t8a_chi_jet_zero hchi i (le_of_lt (not_le.1 hz)), norm_zero]
    exact hs0

theorem r26t8a_env_shift (b k : ℕ) (alpha sigma : ℝ) (q i : ℕ) (hi : i ≤ q) (hq : q ≤ k) (t : ℝ)
    (ht : 0 < t) (ht2 : t < 2) :
    1 + t ^ (alpha - sigma - ((q - i : ℕ) : ℝ)) * (1 + |Real.log t|) ^ (b + 1) ≤
      (1 + 2 ^ (b + 1) * 2 ^ (|alpha - sigma| + k)) *
        (1 + (min 1 t) ^ (-((sigma - alpha) + (q : ℝ))) * (1 + |Real.log (min 1 t)|) ^ (b + 1)) := by
  have hK : (1 : ℝ) ≤ 1 + 2 ^ (b + 1) * 2 ^ (|alpha - sigma| + k) := by
    have : (0 : ℝ) ≤ 2 ^ (b + 1) * 2 ^ (|alpha - sigma| + k) := by positivity
    linarith
  set E : ℝ := 1 + (min 1 t) ^ (-((sigma - alpha) + (q : ℝ))) * (1 + |Real.log (min 1 t)|) ^ (b + 1) with hE
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  rcases le_total t 1 with h1 | h1
  · rw [min_eq_right h1] at hE
    have hexp : alpha - sigma - ((q - i : ℕ) : ℝ) = (-((sigma - alpha) + (q : ℝ))) + (i : ℝ) := by
      rw [Nat.cast_sub hi]; ring
    have hti : t ^ (i : ℝ) ≤ 1 := by
      rw [Real.rpow_natCast]; exact pow_le_one₀ ht.le h1
    have : t ^ (alpha - sigma - ((q - i : ℕ) : ℝ)) ≤ t ^ (-((sigma - alpha) + (q : ℝ))) := by
      rw [hexp, Real.rpow_add ht]
      exact mul_le_of_le_one_right (Real.rpow_nonneg ht.le _) hti
    have hL : 0 ≤ (1 + |Real.log t|) ^ (b + 1) := by positivity
    calc 1 + t ^ (alpha - sigma - ((q - i : ℕ) : ℝ)) * (1 + |Real.log t|) ^ (b + 1)
        ≤ E := by rw [hE]; linarith [mul_le_mul_of_nonneg_right this hL]
      _ ≤ _ := by nlinarith
  · have hmin : min 1 t = 1 := min_eq_left h1
    have hE2 : E = 2 := by rw [hE, hmin]; simp; norm_num
    rw [hE2]
    have hg : |alpha - sigma - ((q - i : ℕ) : ℝ)| ≤ |alpha - sigma| + k := by
      have h3 : |((q - i : ℕ) : ℝ)| ≤ k := by
        rw [Nat.abs_cast]; exact_mod_cast (by omega : q - i ≤ k)
      calc |alpha - sigma - ((q - i : ℕ) : ℝ)| ≤ |alpha - sigma| + |((q - i : ℕ) : ℝ)| := abs_sub _ _
        _ ≤ _ := by linarith
    have hpow : t ^ (alpha - sigma - ((q - i : ℕ) : ℝ)) ≤ 2 ^ (|alpha - sigma| + k : ℝ) := by
      calc t ^ (alpha - sigma - ((q - i : ℕ) : ℝ)) ≤ t ^ |alpha - sigma - ((q - i : ℕ) : ℝ)| :=
            Real.rpow_le_rpow_of_exponent_le h1 (le_abs_self _)
        _ ≤ 2 ^ |alpha - sigma - ((q - i : ℕ) : ℝ)| := Real.rpow_le_rpow ht.le ht2.le (abs_nonneg _)
        _ ≤ 2 ^ (|alpha - sigma| + k : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hg
    have hlog : 1 + |Real.log t| ≤ 2 := by
      have h0 : 0 ≤ Real.log t := Real.log_nonneg h1
      have h4 := Real.log_le_sub_one_of_pos ht
      rw [abs_of_nonneg h0]; linarith
    have hlogp : (1 + |Real.log t|) ^ (b + 1) ≤ 2 ^ (b + 1) := pow_le_pow_left₀ (by positivity) hlog _
    have hp0 : 0 ≤ t ^ (alpha - sigma - ((q - i : ℕ) : ℝ)) := Real.rpow_nonneg ht.le _
    have h5 : t ^ (alpha - sigma - ((q - i : ℕ) : ℝ)) * (1 + |Real.log t|) ^ (b + 1) ≤
        2 ^ (|alpha - sigma| + k : ℝ) * 2 ^ (b + 1) :=
      mul_le_mul hpow hlogp (by positivity) (by positivity)
    nlinarith [mul_comm ((2 : ℝ) ^ (b + 1)) (2 ^ (|alpha - sigma| + k : ℝ))]

end HRS.MS.R26T8A
