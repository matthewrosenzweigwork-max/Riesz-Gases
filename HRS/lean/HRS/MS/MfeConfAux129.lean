import HRS.MS.MfeConfAux128

/-!
# S.B.1 (SB5), R1 (part 6): `Sb1HBAll d` — the vanishing remainder `SM` (hypothesis `hB`) is proved

`sb1eta_tendsto`: `η_M = ∫_{|z| ≤ 1/(M+1)} |z|^{-s} dz → 0`.  `sb1_hB_all : Sb1HBAll d` combines the estimates E0 (Aux126), E1 (Aux127), E2 (Aux128)
with the remainder bound `sb1_B_bound` (Aux183) and the uniform envelope `sb1kM_grad_env`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.RdGen HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d : ℕ}

theorem sb1eta_tendsto (hd : 1 ≤ d) {s : ℝ} (hsd : s < d) :
    Tendsto (fun M : ℕ => sb1eta d s (1 / ((M : ℝ) + 1))) atTop (𝓝 0) := by
  have hint : Integrable (Set.indicator (Metric.closedBall (0 : Euc d) 1) (fun z : Euc d => ‖z‖ ^ (-s))) := by
    rw [integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
    exact sb1_nsup_integrable hd hsd le_rfl
  have h := tendsto_integral_of_dominated_convergence (μ := (volume : Measure (Euc d)))
    (F := fun (M : ℕ) (z : Euc d) => Set.indicator (Metric.closedBall (0 : Euc d) (1 / ((M : ℝ) + 1))) (fun z : Euc d => ‖z‖ ^ (-s)) z)
    (f := fun _ => (0 : ℝ))
    (bound := Set.indicator (Metric.closedBall (0 : Euc d) 1) (fun z : Euc d => ‖z‖ ^ (-s)))
    (fun M => ((sb1_nsup_integrable hd hsd (sb1_rM_le M)).integrable_indicator
      Metric.isClosed_closedBall.measurableSet).aestronglyMeasurable) hint
    (fun M => Eventually.of_forall fun z => by
      by_cases hz : z ∈ Metric.closedBall (0 : Euc d) (1 / ((M : ℝ) + 1))
      · have hz1 : z ∈ Metric.closedBall (0 : Euc d) 1 := Metric.closedBall_subset_closedBall (sb1_rM_le M) hz
        rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz1, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
      · rw [Set.indicator_of_notMem hz, norm_zero]
        exact Set.indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg z) _) z)
    (by
      filter_upwards [movtr_ae_ne_zero (d := d) hd] with z hz
      have hzp : 0 < ‖z‖ := norm_pos_iff.2 hz
      have hlim := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hlim.eventually (gt_mem_nhds hzp)] with M hM
      rw [Set.indicator_of_notMem]
      simpa using hM)
  simpa [sb1eta, integral_indicator Metric.isClosed_closedBall.measurableSet] using h

theorem sb1_hB_all (d : ℕ) : Sb1HBAll d := by
  intro D T C B C3 ρ H hT N hN hβ Kf hLip
  have hs0 := H.tr.hs0
  have hd := H.tr.hd
  have hsd := H.tr.hsd
  obtain ⟨A, hA0, hA⟩ := sb1_dk_rgKer (d := d) hs0
  obtain ⟨Ae, hAe0, hAe⟩ := sb1kM_grad_env (d := d) D.s hs0
  set σ := Whole.movtr_sigma D.s with hσdef
  have hσ : 0 ≤ σ := sb1_sigma_nonneg hs0
  set K1 : ℝ := (A + σ) * ((4 * 2 ^ ((d : ℝ) + 3)) * C3) with hK1
  have hK10 : 0 ≤ K1 := mul_nonneg (add_nonneg hA0 hσ) (mul_nonneg (by positivity) H.C3nn)
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set Cε : ℝ := d * K1 + d * d * K1 with hCε
  have hCε0 : 0 ≤ Cε := by positivity
  set η : ℕ → ℝ := fun M => Cε * sb1eta d D.s (1 / ((M : ℝ) + 1)) with hη
  have hηt : Tendsto η atTop (𝓝 0) := by
    simpa [hη] using (sb1eta_tendsto hd hsd).const_mul Cε
  have hη0 : ∀ M, 0 ≤ η M := fun M => mul_nonneg hCε0 (sb1eta_nonneg _ _)
  obtain ⟨b, hb⟩ : ∃ b : ℝ, ∀ M, η M ≤ b := by
    obtain ⟨b, hb⟩ := hηt.bddAbove_range
    exact ⟨b, fun M => hb ⟨M, rfl⟩⟩
  have hb0 : 0 ≤ b := (hη0 0).trans (hb 0)
  obtain ⟨A3, A4, hA3, hA4, hmain⟩ := sb1_B_bound H hT hN hβ Kf hLip (Ak := Ae + 1) (ε1 := b) (by linarith) hb0
  refine ⟨η, A3, A4, hηt, hη0, hA3, hA4, fun M r hr Z => ?_⟩
  have hk4 := sb1kM_isKernel (d := d) D.s hs0 M
  have henv : ∀ z, ‖z‖ * ‖gradient (sb1kM d D.s M) z‖ ≤
      (Ae + 1) * (sb1kM d D.s M z + Real.log (1 + ‖z‖) + 1) := by
    intro z
    have h1 := hAe M z
    have h2 : 0 ≤ sb1kM d D.s M z + Real.log (1 + ‖z‖) + 1 := by
      have := hk4.lower z
      linarith
    nlinarith
  have hAM : ∀ j : Fin d, RgKer d D.s A (sb1_lv_dk (sb1kM d D.s M) j) := hA M
  have hw1 : ∀ x : Euc d, sb1w ((d : ℝ) + 3) x ≤ 1 := fun x => sb1w_le_one (by positivity) x
  have hη_ge : ∀ n : ℝ, 0 ≤ n → n ≤ Cε → n * sb1eta d D.s (1 / ((M : ℝ) + 1)) ≤ η M := fun n hn hnC =>
    mul_le_mul_of_nonneg_right hnC (sb1eta_nonneg _ _)
  refine hmain (1 / ((M : ℝ) + 1)) (sb1kM d D.s M) (η M) hk4 henv (hη0 M) (hb M) ?_ ?_ ?_ r hr Z
  · intro r hr x
    refine (sb1_lv_norm_le_sum _).trans ?_
    calc ∑ j, |sb1_lv_e D (sb1kM d D.s M) hT.le ρ r x j| ≤ ∑ _j : Fin d,
          K1 * sb1w ((d : ℝ) + 3) x * sb1eta d D.s (1 / ((M : ℝ) + 1)) := by
          refine Finset.sum_le_sum fun j _ => ?_
          refine (sb1_E0 H hT.le hs0 M hAM hr x j).trans (le_of_eq ?_)
          rw [hK1]; ring
      _ = d * K1 * sb1eta d D.s (1 / ((M : ℝ) + 1)) * sb1w ((d : ℝ) + 3) x := by simp; ring
      _ ≤ η M * sb1w ((d : ℝ) + 3) x := by
          refine mul_le_mul_of_nonneg_right ?_ (sb1w_pos _ _).le
          refine hη_ge _ (by positivity) ?_
          rw [hCε]; nlinarith [mul_nonneg (mul_nonneg hd0 hd0) hK10]
  · intro r hr x
    refine (sb1_E1 H M hAM hr x).trans ?_
    calc (d : ℝ) * ((A + σ) * ((4 * 2 ^ ((d : ℝ) + 3)) * C3 * sb1w ((d : ℝ) + 3) x) *
          sb1eta d D.s (1 / ((M : ℝ) + 1))) = d * K1 * sb1w ((d : ℝ) + 3) x * sb1eta d D.s (1 / ((M : ℝ) + 1)) := by
          rw [hK1]; ring
      _ ≤ d * K1 * 1 * sb1eta d D.s (1 / ((M : ℝ) + 1)) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hw1 x) (by positivity)) (sb1eta_nonneg _ _)
      _ ≤ η M := by
          rw [mul_one]
          refine hη_ge _ (by positivity) ?_
          rw [hCε]; nlinarith [mul_nonneg (mul_nonneg hd0 hd0) hK10]
  · intro r hr x y
    refine (sb1_E2 H hT.le M hA0 hAM hr x y).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc (d : ℝ) * (d * ((A + σ) * ((4 * 2 ^ ((d : ℝ) + 3)) * C3) * sb1eta d D.s (1 / ((M : ℝ) + 1))))
        = d * d * K1 * sb1eta d D.s (1 / ((M : ℝ) + 1)) := by rw [hK1]; ring
      _ ≤ η M := by
          refine hη_ge _ (by positivity) ?_
          rw [hCε]; nlinarith [mul_nonneg hd0 hK10]

end HRS.MS.MfeConf
