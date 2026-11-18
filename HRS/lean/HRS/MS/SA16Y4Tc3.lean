import HRS.MS.SA16Y4Tc2
import HRS.MS.SA16Y4Ap2
import HRS.MS.SA16Y4Cv1

/-!
# S.A.16 (SA16Y4) Tc3: the interpolated truncated mollified drift converges to the drift, locally uniformly (only `C^0`)

`sa16y4_mol_lip`: `|(ρ_n ⋆ h)(x) - h(x)| ≤ L/(n+1)` for `L`-Lipschitz `h`.
`sa16y4_bcInt_tendsto`: for `σ ∈ [0,t]`, `R0`, `ε` and `N` large, `|bcInt N σ j x - b (t-σ) x j| ≤ ε` for `‖x‖ ≤ R0`, given equi-Lipschitz
components of `b r` and pointwise continuity in `r`.  No derivative of the drift enters.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Tc3
variable {d : ℕ}

lemma sa16y4_mol_lip {h : EuclideanSpace ℝ (Fin d) → ℝ} {L : ℝ} (hL : 0 ≤ L) (hh : Continuous h)
    (hlip : ∀ x y, |h x - h y| ≤ L * ‖x - y‖) (n : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    |(∫ y, h y * sa16y_rho d n (x - y)) - h x| ≤ L / ((n : ℝ) + 1) := by
  have hρ0 : ∀ z, 0 ≤ sa16y_rho d n z := sa16y_rho_nonneg n
  have hρ1 := sa16y_rho_int (d := d) n
  have hρi : Integrable (fun y => sa16y_rho d n (x - y)) :=
    ((sa16y_rho_smooth (d := d) n).continuous.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
      (sa16y4_cc_shift (sa16y4_rho_cc n) x)
  have hsub : (∫ y, h y * sa16y_rho d n (x - y)) - h x = ∫ y, (h y - h x) * sa16y_rho d n (x - y) := by
    have : ∫ y, (h y - h x) * sa16y_rho d n (x - y) =
        (∫ y, h y * sa16y_rho d n (x - y)) - h x * ∫ y, sa16y_rho d n (x - y) := by
      rw [← integral_const_mul, ← integral_sub]
      · refine integral_congr_ae (Eventually.of_forall fun y => ?_); ring
      · exact (hh.mul ((sa16y_rho_smooth (d := d) n).continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
          (sa16y4_cc_shift (sa16y4_rho_cc n) x).mul_left
      · exact hρi.const_mul _
    rw [this, sa16y4_shift_integral hρ1 x, mul_one]
  rw [hsub]
  have := norm_integral_le_of_norm_le (hρi.const_mul (L / ((n : ℝ) + 1))) (μ := volume)
    (f := fun y => (h y - h x) * sa16y_rho d n (x - y)) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 _)]
      by_cases hz : 1 / ((n : ℝ) + 1) < ‖x - y‖
      · rw [sa16y_rho_supp n _ hz]; simp
      · refine mul_le_mul_of_nonneg_right ?_ (hρ0 _)
        have hz' : ‖x - y‖ ≤ 1 / ((n : ℝ) + 1) := not_lt.1 hz
        calc |h y - h x| ≤ L * ‖y - x‖ := hlip y x
          _ = L * ‖x - y‖ := by rw [norm_sub_rev]
          _ ≤ L * (1 / ((n : ℝ) + 1)) := mul_le_mul_of_nonneg_left hz' hL
          _ = L / ((n : ℝ) + 1) := by rw [mul_one_div])
  rw [integral_const_mul, sa16y4_shift_integral hρ1 x, mul_one] at this
  simpa [Real.norm_eq_abs] using this

theorem sa16y4_bcInt_tendsto (t L : ℝ) (ht : 0 < t) (hL : 0 ≤ L)
    (b : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hbc : ∀ r ∈ Icc (0 : ℝ) t, ∀ j, Continuous (fun y => b r y j))
    (hlip : ∀ r ∈ Icc (0 : ℝ) t, ∀ j x y, |b r x j - b r y j| ≤ L * ‖x - y‖)
    (hpt : ∀ x j, ContinuousOn (fun r => b r x j) (Icc (0 : ℝ) t)) {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) t)
    (R0 : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ j : Fin d, ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≤ R0 →
      |sa16y4_bcInt d N t b σ j x - b (t - σ) x j| ≤ ε := by
  have hr : t - σ ∈ Icc (0 : ℝ) t := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
  -- the time modulus, uniformly in `j`
  have hδ : ∀ j : Fin d, ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ Icc (0 : ℝ) t, |r - (t - σ)| < δ → ∀ x : EuclideanSpace ℝ (Fin d),
      ‖x‖ ≤ R0 → |b r x j - b (t - σ) x j| ≤ ε / 2 := fun j =>
    sa16y4_locunif hL (fun r x => b r x j) (fun r hr x y => hlip r hr j x y) (fun x => hpt x j) R0 hr (by positivity)
  choose δ hδ0 hδ1 using hδ
  have hδmin : ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ j, δ0 ≤ δ j := by
    by_cases hd0 : d = 0
    · exact ⟨1, one_pos, fun j => (Fin.elim0 (hd0 ▸ j))⟩
    · haveI : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero hd0⟩⟩
      refine ⟨Finset.univ.inf' Finset.univ_nonempty δ, ?_, fun j => Finset.inf'_le _ (Finset.mem_univ j)⟩
      exact (Finset.lt_inf'_iff _).2 fun j _ => hδ0 j
  obtain ⟨δ0, hδ00, hδ0⟩ := hδmin
  have hev1 : ∀ᶠ N : ℕ in atTop, t / (N : ℝ) < δ0 := by
    obtain ⟨M, hM⟩ := exists_nat_gt (t / δ0)
    refine (eventually_ge_atTop (max M 1)).mono fun N hN => ?_
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (le_max_right M 1).trans hN
    have hMN : (M : ℝ) ≤ N := by exact_mod_cast (le_max_left M 1).trans hN
    rw [div_lt_iff₀ (by linarith)]
    rw [div_lt_iff₀ hδ00] at hM
    nlinarith
  have hev2 : ∀ᶠ N : ℕ in atTop, L / ((N : ℝ) + 1) ≤ ε / 2 := by
    obtain ⟨M, hM⟩ := exists_nat_gt (2 * L / ε)
    refine (eventually_ge_atTop M).mono fun N hN => ?_
    have hMN : (M : ℝ) ≤ N := by exact_mod_cast hN
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hM
    nlinarith
  have hev3 : ∀ᶠ N : ℕ in atTop, R0 ≤ (N : ℝ) + 1 := by
    obtain ⟨M, hM⟩ := exists_nat_gt R0
    exact (eventually_ge_atTop M).mono fun N hN => by
      have : (M : ℝ) ≤ N := by exact_mod_cast hN
      linarith
  filter_upwards [hev1, hev2, hev3, eventually_ge_atTop 1] with N h1 h2 h3 hN1 j x hx
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw0 : ∀ i ∈ Finset.range (N + 1), 0 ≤ sa16y4_hat N t i σ := fun i _ => sa16y4_hat_nonneg N t i σ
  have hw1 := sa16y4_hat_sum hN1 ht hσ
  have hχ : sa16j_chi d ((N : ℝ) + 1) x = 1 := sa16j_chi_one d (by positivity) (hx.trans h3)
  have hexp : sa16y4_bcInt d N t b σ j x - b (t - σ) x j = ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ *
      (((∫ y, b (t - (i : ℝ) * t / N) y j * sa16y_rho d N (x - y)) - b (t - (i : ℝ) * t / N) x j) +
        (b (t - (i : ℝ) * t / N) x j - b (t - σ) x j)) := by
    have e : ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ *
        ((∫ y, b (t - (i : ℝ) * t / N) y j * sa16y_rho d N (x - y)) - b (t - σ) x j) =
        (∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ * ∫ y, b (t - (i : ℝ) * t / N) y j * sa16y_rho d N (x - y)) -
          b (t - σ) x j := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul]
    have e2 : sa16y4_bcInt d N t b σ j x = ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ *
        ∫ y, b (t - (i : ℝ) * t / N) y j * sa16y_rho d N (x - y) := by
      unfold sa16y4_bcInt sa16y4_tm
      simp only [hχ, one_mul]
    rw [e2, ← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hexp]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i ∈ Finset.range (N + 1), |sa16y4_hat N t i σ * (((∫ y, b (t - (i : ℝ) * t / N) y j * sa16y_rho d N (x - y)) -
        b (t - (i : ℝ) * t / N) x j) + (b (t - (i : ℝ) * t / N) x j - b (t - σ) x j))|
      ≤ ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ * ε := by
        refine Finset.sum_le_sum fun i hi => ?_
        by_cases hhat : sa16y4_hat N t i σ = 0
        · rw [hhat]; simp
        rw [abs_mul, abs_of_nonneg (hw0 i hi)]
        refine mul_le_mul_of_nonneg_left ?_ (hw0 i hi)
        have hri : t - (i : ℝ) * t / N ∈ Icc (0 : ℝ) t := sa16y4_node_mem hN1 ht hi
        refine (abs_add_le _ _).trans ?_
        have hA := sa16y4_mol_lip hL (hbc _ hri j) (hlip _ hri j) N x
        have hs := sa16y4_hat_supp hN1 ht hhat
        have hd : |(t - (i : ℝ) * t / N) - (t - σ)| < δ j := by
          have : (t - (i : ℝ) * t / N) - (t - σ) = σ - i * t / N := by ring
          rw [this]
          exact lt_of_lt_of_le (lt_of_lt_of_le hs (le_of_lt h1)) (hδ0 j)
        have hB := hδ1 j _ hri hd x hx
        linarith
    _ = ε := by rw [← Finset.sum_mul, hw1, one_mul]

end Tc3

end HRS.Whole.AppendixA.Phase2SA16R
