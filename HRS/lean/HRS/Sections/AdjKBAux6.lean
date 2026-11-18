import HRS.Sections.AdjKBAux5

/-!
# ADJKB Aux6: assembled Kolmogorov-Chentsov tightness (KOLM)
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjK

theorem adjkb_kolmogorov_equicont {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] (T : ℝ) (hT : 0 < T) (p q : ℝ) (hq : 1 < q)
    (M : ℝ≥0) {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] (P : ∀ i, Measure (Ω i))
    [∀ i, IsProbabilityMeasure (P i)] (Y : ∀ i, Set.Icc (0 : ℝ) T → Ω i → E)
    (hY : ∀ i, IsKolmogorovProcess (Y i) (P i) p q M)
    (hcont : ∀ i, ∀ᵐ ω ∂P i, Continuous fun t => Y i t ω) :
    ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ i,
      P i {ω | ∃ s t : Set.Icc (0 : ℝ) T, |(s : ℝ) - t| ≤ δ ∧ η < ‖Y i s ω - Y i t ω‖} ≤
        ENNReal.ofReal ε := by
  intro ε η hε hη
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · exact ⟨1, one_pos, fun i => (hι.false i).elim⟩
  have hp : 0 < p := (hY i₀).p_pos
  obtain ⟨r, hr0, hr1, hΘ1⟩ := adjkb_consts p q hp hq
  set Θ : ℝ := 2 / ((2 : ℝ) ^ q * r ^ p) with hΘ
  have hΘ0 : 0 < Θ := by
    rw [hΘ]; have := Real.rpow_pos_of_pos hr0 p; positivity
  set C : ℝ := M * T ^ q with hC
  have hC0 : 0 ≤ C := by rw [hC]; have := Real.rpow_pos_of_pos hT q; positivity
  have h1r : 0 < 1 - r := by linarith
  have h1Θ : 0 < 1 - Θ := by linarith
  have ev1 : ∀ᶠ N : ℕ in atTop, C * Θ ^ N / (1 - Θ) ≤ ε := by
    have : Tendsto (fun N : ℕ => C * Θ ^ N / (1 - Θ)) atTop (𝓝 (C * 0 / (1 - Θ))) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hΘ0.le hΘ1).const_mul C).div_const _
    rw [mul_zero, zero_div] at this
    exact this.eventually (eventually_le_nhds hε)
  have ev2 : ∀ᶠ N : ℕ in atTop, r ^ N * (1 + r) / (1 - r) ≤ η := by
    have : Tendsto (fun N : ℕ => r ^ N * (1 + r) / (1 - r)) atTop (𝓝 (0 * (1 + r) / (1 - r))) :=
      (((tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1)).mul_const _).div_const _
    rw [zero_mul, zero_div] at this
    exact this.eventually (eventually_le_nhds hη)
  obtain ⟨N, hN1, hN2⟩ := (ev1.and ev2).exists
  refine ⟨T / 2 ^ N / 2, by positivity, fun i => ?_⟩
  have hYi := hY i
  set A : ℕ → Set (Ω i) := fun n => {ω | ∃ a : ℕ, a < 2 ^ n ∧
        r ^ n < ‖Y i (Set.projIcc 0 T hT.le (((a : ℝ) + 1) * (T / 2 ^ n))) ω -
          Y i (Set.projIcc 0 T hT.le ((a : ℝ) * (T / 2 ^ n))) ω‖} with hA
  set Nul : Set (Ω i) := {ω | ¬ Continuous fun t => Y i t ω} with hNul
  have hsub : {ω | ∃ s t : Set.Icc (0 : ℝ) T, |(s : ℝ) - t| ≤ T / 2 ^ N / 2 ∧
        η < ‖Y i s ω - Y i t ω‖} ⊆ Nul ∪ ⋃ n, A (N + n) := by
    intro ω ⟨s, t, hst, hlt⟩
    by_contra hcon
    simp only [mem_union, mem_iUnion, not_or, not_exists] at hcon
    obtain ⟨hcn, hAn⟩ := hcon
    have hcn' : Continuous fun u => Y i u ω := by
      by_contra h; exact hcn h
    set f : ℝ → E := fun x => Y i (Set.projIcc 0 T hT.le x) ω with hf
    have hfc : Continuous f := hcn'.comp continuous_projIcc
    have hinc : ∀ n : ℕ, N ≤ n → ∀ a : ℕ,
        ‖f (((a : ℝ) + 1) * (T / 2 ^ n)) - f ((a : ℝ) * (T / 2 ^ n))‖ ≤ r ^ n := by
      intro n hn a
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
      by_cases ha : a < 2 ^ (N + k)
      · have := hAn k
        simp only [hA, mem_setOf_eq, not_exists, not_and, not_lt] at this
        exact this a ha
      · push_neg at ha
        have hτ : 0 < T / 2 ^ (N + k) := by positivity
        have hge : T ≤ (a : ℝ) * (T / 2 ^ (N + k)) := by
          have : (2 : ℝ) ^ (N + k) ≤ a := by exact_mod_cast ha
          calc T = 2 ^ (N + k) * (T / 2 ^ (N + k)) := by field_simp
            _ ≤ a * (T / 2 ^ (N + k)) := mul_le_mul_of_nonneg_right this hτ.le
        have hge' : T ≤ ((a : ℝ) + 1) * (T / 2 ^ (N + k)) := by nlinarith
        simp only [hf]
        rw [Set.projIcc_of_right_le _ hge, Set.projIcc_of_right_le _ hge', sub_self, norm_zero]
        positivity
    have hmod := adjkb_modulus f hfc T hT r hr0 hr1 N hinc s t s.2.1 t.2.1
      (by have : (0 : ℝ) < T / 2 ^ N := by positivity
          linarith)
    have e1 : f (s : ℝ) = Y i s ω := by simp only [hf, Set.projIcc_val]
    have e2 : f (t : ℝ) = Y i t ω := by simp only [hf, Set.projIcc_val]
    rw [e1, e2] at hmod
    linarith
  have hnull : P i Nul = 0 := ae_iff.1 (hcont i)
  have hterm : ∀ n : ℕ, P i (A (N + n)) ≤ ENNReal.ofReal (C * Θ ^ N * Θ ^ n) := by
    intro n
    have := adjkb_level_bound hT hYi (N + n) (r ^ (N + n)) (by positivity)
    refine this.trans (le_of_eq ?_)
    rw [adjkb_level_identity hT (M : ℝ) r p q hr0 (N + n), pow_add]
    congr 1; rw [hC]; ring
  have hsum : Summable fun n : ℕ => C * Θ ^ N * Θ ^ n :=
    (summable_geometric_of_lt_one hΘ0.le hΘ1).mul_left _
  have hsumv : ∑' n : ℕ, C * Θ ^ N * Θ ^ n = C * Θ ^ N / (1 - Θ) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hΘ0.le hΘ1]; field_simp
  calc P i {ω | ∃ s t : Set.Icc (0 : ℝ) T, |(s : ℝ) - t| ≤ T / 2 ^ N / 2 ∧
        η < ‖Y i s ω - Y i t ω‖}
      ≤ P i (Nul ∪ ⋃ n, A (N + n)) := measure_mono hsub
    _ ≤ P i Nul + P i (⋃ n, A (N + n)) := measure_union_le _ _
    _ ≤ 0 + ∑' n, P i (A (N + n)) := by
        rw [hnull]; exact add_le_add le_rfl (measure_iUnion_le _)
    _ ≤ 0 + ∑' n : ℕ, ENNReal.ofReal (C * Θ ^ N * Θ ^ n) := by
        exact add_le_add le_rfl (ENNReal.tsum_le_tsum hterm)
    _ = ENNReal.ofReal (C * Θ ^ N / (1 - Θ)) := by
        rw [zero_add, ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum, hsumv]
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hN1

end HRS.AdjK
