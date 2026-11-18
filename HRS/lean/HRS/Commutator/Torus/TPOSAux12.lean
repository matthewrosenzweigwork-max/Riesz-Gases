import HRS.Commutator.Torus.TPOSAux11

/-!
# T-POS helpers, part 12: continuity of lattice sums `y ↦ ∑_{m∉T} h(y+m)`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma tpos_exists_rho (y0 : Euc d) (T : Finset (Lattice d))
    (hy0 : ∀ m : Lattice d, m ∉ T → y0 + Lattice.toEuc m ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ m : Lattice d, m ∉ T → 2 * ρ ≤ ‖y0 + Lattice.toEuc m‖ := by
  classical
  set F : Finset (Lattice d) := (tpos_finite_norm_le (d := d) (‖y0‖ + 1)).toFinset.filter (· ∉ T)
    with hF
  have hfar : ∀ m : Lattice d, m ∉ T → m ∉ F → 1 ≤ ‖y0 + Lattice.toEuc m‖ := by
    intro m hmT hmF
    have : ¬ ‖Lattice.toEuc m‖ ≤ ‖y0‖ + 1 := by
      intro h
      apply hmF
      simp only [hF, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact ⟨h, hmT⟩
    push Not at this
    have h2 := norm_sub_norm_le (Lattice.toEuc m) (-y0)
    rw [sub_neg_eq_add, add_comm, norm_neg] at h2
    linarith
  by_cases hne : F.Nonempty
  · obtain ⟨m₀, hm₀, hmin⟩ := F.exists_min_image (fun m => ‖y0 + Lattice.toEuc m‖) hne
    have hm₀T : m₀ ∉ T := (Finset.mem_filter.1 hm₀).2
    have hpos : 0 < ‖y0 + Lattice.toEuc m₀‖ := norm_pos_iff.2 (hy0 m₀ hm₀T)
    refine ⟨min (1 / 2) (‖y0 + Lattice.toEuc m₀‖ / 2), lt_min (by norm_num) (by positivity),
      fun m hmT => ?_⟩
    by_cases hmF : m ∈ F
    · have := hmin m hmF
      have h2 : 2 * min (1 / 2) (‖y0 + Lattice.toEuc m₀‖ / 2) ≤ ‖y0 + Lattice.toEuc m₀‖ := by
        have := min_le_right (1 / 2 : ℝ) (‖y0 + Lattice.toEuc m₀‖ / 2); linarith
      linarith
    · have := hfar m hmT hmF
      have h2 : 2 * min (1 / 2 : ℝ) (‖y0 + Lattice.toEuc m₀‖ / 2) ≤ 1 := by
        have := min_le_left (1 / 2 : ℝ) (‖y0 + Lattice.toEuc m₀‖ / 2); linarith
      linarith
  · refine ⟨1 / 2, by norm_num, fun m hmT => ?_⟩
    have hmF : m ∉ F := fun h => hne ⟨m, h⟩
    have := hfar m hmT hmF
    linarith

lemma tpos_continuousAt_latsum {h : Euc d → ℝ} {C r : ℝ} (hC : 0 ≤ C) (hr : (d : ℝ) < r)
    (hb : ∀ z, z ≠ 0 → |h z| ≤ C * ‖z‖ ^ (-r)) (hcont : ContinuousOn h {z | z ≠ 0})
    (T : Finset (Lattice d)) (y0 : Euc d)
    (hy0 : ∀ m : Lattice d, m ∉ T → y0 + Lattice.toEuc m ≠ 0) :
    ContinuousAt (fun y : Euc d => ∑' m : Lattice d,
      if m ∈ T then 0 else h (y + Lattice.toEuc m)) y0 := by
  classical
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  obtain ⟨ρ, hρ, hρm⟩ := tpos_exists_rho y0 T hy0
  set R : ℝ := 2 * (‖y0‖ + ρ) with hR
  set u : Lattice d → ℝ := fun m => C * 2 ^ r * ‖Lattice.toEuc m‖ ^ (-r) +
    (if ‖Lattice.toEuc m‖ ≤ R then C * ρ ^ (-r) else 0) with hu
  have hu_sum : Summable u := by
    refine ((tpos_summable_rpow (d := d) hr).mul_left (C * 2 ^ r)).add ?_
    refine summable_of_finite_support ?_
    refine (tpos_finite_norm_le (d := d) R).subset ?_
    intro m hm
    simp only [Function.mem_support, ne_eq] at hm
    by_contra hcon
    simp only [Set.mem_setOf_eq] at hcon
    exact hm (by simp [hcon])
  have hlow : ∀ y ∈ Metric.ball y0 ρ, ∀ m : Lattice d, m ∉ T → ρ ≤ ‖y + Lattice.toEuc m‖ := by
    intro y hy m hmT
    have h1 := hρm m hmT
    have h2 : ‖y - y0‖ < ρ := by rwa [← dist_eq_norm, ← Metric.mem_ball]
    have h3 := norm_sub_norm_le (y0 + Lattice.toEuc m) (y0 - y)
    have : y0 + Lattice.toEuc m - (y0 - y) = y + Lattice.toEuc m := by abel
    rw [this, norm_sub_rev] at h3
    linarith
  have hcm : ∀ m : Lattice d, ContinuousOn (fun y : Euc d => if m ∈ T then (0 : ℝ) else h (y + Lattice.toEuc m))
      (Metric.ball y0 ρ) := by
    intro m
    by_cases hm : m ∈ T
    · simp only [hm, if_true]; exact continuousOn_const
    · simp only [hm, if_false]
      refine hcont.comp (continuous_id.add continuous_const).continuousOn (fun y hy => ?_)
      have := hlow y hy m hm
      exact norm_pos_iff.1 (lt_of_lt_of_le hρ this)
  have hbound : ∀ m : Lattice d, ∀ y ∈ Metric.ball y0 ρ,
      ‖(if m ∈ T then (0 : ℝ) else h (y + Lattice.toEuc m))‖ ≤ u m := by
    intro m y hy
    have hu0 : 0 ≤ u m := by
      simp only [hu]
      have h1 : 0 ≤ C * 2 ^ r * ‖Lattice.toEuc m‖ ^ (-r) := by positivity
      have h2 : 0 ≤ (if ‖Lattice.toEuc m‖ ≤ R then C * ρ ^ (-r) else 0) := by
        split_ifs
        · positivity
        · exact le_refl _
      linarith
    by_cases hm : m ∈ T
    · simp only [hm, if_true, norm_zero]; exact hu0
    · simp only [hm, if_false]
      have hy' := hlow y hy m hm
      have hz : y + Lattice.toEuc m ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hρ hy')
      have hb' := hb _ hz
      rw [Real.norm_eq_abs]
      have hnn : 0 ≤ C * 2 ^ r * ‖Lattice.toEuc m‖ ^ (-r) := by positivity
      by_cases hmR : ‖Lattice.toEuc m‖ ≤ R
      · have h2 : ‖y + Lattice.toEuc m‖ ^ (-r) ≤ ρ ^ (-r) :=
          Real.rpow_le_rpow_of_nonpos hρ hy' (by linarith)
        have : |h (y + Lattice.toEuc m)| ≤ C * ρ ^ (-r) :=
          hb'.trans (mul_le_mul_of_nonneg_left h2 hC)
        simp only [hu, hmR, if_true]
        linarith
      · push Not at hmR
        have hmpos : 0 < ‖Lattice.toEuc m‖ := by
          have : 0 ≤ ‖y0‖ + ρ := by positivity
          linarith
        have hy2 : ‖y‖ ≤ ‖y0‖ + ρ := by
          have h2 : ‖y - y0‖ < ρ := by rwa [← dist_eq_norm, ← Metric.mem_ball]
          have := norm_le_norm_add_norm_sub' y y0
          have := norm_sub_norm_le y y0
          linarith
        have hlow2 : ‖Lattice.toEuc m‖ / 2 ≤ ‖y + Lattice.toEuc m‖ := by
          have := norm_sub_norm_le (Lattice.toEuc m) (-y)
          rw [sub_neg_eq_add, add_comm, norm_neg] at this
          linarith
        have h2 : ‖y + Lattice.toEuc m‖ ^ (-r) ≤ (‖Lattice.toEuc m‖ / 2) ^ (-r) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hlow2 (by linarith)
        have h3 : (‖Lattice.toEuc m‖ / 2) ^ (-r) = 2 ^ r * ‖Lattice.toEuc m‖ ^ (-r) := by
          rw [Real.div_rpow hmpos.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) r,
            div_inv_eq_mul, mul_comm]
        have : |h (y + Lattice.toEuc m)| ≤ C * 2 ^ r * ‖Lattice.toEuc m‖ ^ (-r) := by
          calc |h (y + Lattice.toEuc m)| ≤ C * ‖y + Lattice.toEuc m‖ ^ (-r) := hb'
            _ ≤ C * (2 ^ r * ‖Lattice.toEuc m‖ ^ (-r)) := by
                rw [← h3]; exact mul_le_mul_of_nonneg_left h2 hC
            _ = _ := by ring
        have hmR' : ¬ ‖Lattice.toEuc m‖ ≤ R := not_le.2 hmR
        simp only [hu, hmR', if_false]
        linarith
  have hon := continuousOn_tsum hcm hu_sum hbound
  exact hon.continuousAt (Metric.ball_mem_nhds y0 hρ)

end HRS.Commutator.TorusNote
