import HRS.MS.R2InterpAux119

/-!
# S10.2 (worker S10S), part 126 (packet M3a): joint continuity from continuous slices on a dense set of times and a uniform Lipschitz bound

`F(u,t)` on the triangle `0 ≤ u ≤ t ≤ T`: if `F(·,q)` is continuous on `[0,q]` for all `q` in a set `Q ∋ T` accumulating at every `t < T` from above,
and `‖F(u,t) - F(u,t')‖ ≤ K (t - t')` for `u ≤ t' ≤ t`, then `F` is jointly continuous on the triangle.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

theorem s102_joint_cont {E : Type*} [NormedAddCommGroup E] {T K : ℝ} (hK : 0 ≤ K) (F : ℝ → ℝ → E) (Q : Set ℝ)
    (hQT : T ∈ Q)
    (hQd : ∀ t : ℝ, 0 ≤ t → t < T → ∀ δ > 0, ∃ q ∈ Q, t < q ∧ q < t + δ ∧ q ≤ T)
    (hlip : ∀ u t t' : ℝ, 0 ≤ u → u ≤ t' → t' ≤ t → t ≤ T → ‖F u t - F u t'‖ ≤ K * (t - t'))
    (hslice : ∀ q ∈ Q, ContinuousOn (fun u => F u q) (Icc 0 q)) :
    ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ T} := by
  rw [Metric.continuousOn_iff]
  rintro ⟨u0, t0⟩ ⟨h0u, hut, htT⟩ ε hε
  simp only at h0u hut htT
  have hK1 : 0 < K + 1 := by linarith
  set η : ℝ := ε / (4 * (K + 1)) with hη
  have hη0 : 0 < η := by positivity
  have hKη : K * η < ε / 4 := by
    rw [hη, mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  -- the auxiliary time `q`
  obtain ⟨q, hq, hqt0, hqT, hqcase, hKq⟩ : ∃ q ∈ Q, t0 ≤ q ∧ q ≤ T ∧ (q = T ∨ t0 < q) ∧ K * (q - t0) < ε / 4 := by
    by_cases ht : t0 < T
    · obtain ⟨q, hq, h1, h2, h3⟩ := hQd t0 (h0u.trans hut) ht η hη0
      refine ⟨q, hq, h1.le, h3, Or.inr h1, ?_⟩
      calc K * (q - t0) ≤ K * η := mul_le_mul_of_nonneg_left (by linarith) hK
        _ < ε / 4 := hKη
    · have h : t0 = T := le_antisymm htT (not_lt.1 ht)
      refine ⟨T, hQT, h.le, le_rfl, Or.inl rfl, ?_⟩
      rw [h, sub_self, mul_zero]; positivity
  obtain ⟨δ1, hδ1, hc⟩ := Metric.continuousOn_iff.1 (hslice q hq) u0 ⟨h0u, hut.trans hqt0⟩ (ε / 4) (by positivity)
  set δ3 : ℝ := if t0 < q then q - t0 else 1 with hδ3
  have hδ30 : 0 < δ3 := by
    by_cases h : t0 < q
    · simp only [hδ3, if_pos h]; linarith
    · simp only [hδ3, if_neg h]; norm_num
  refine ⟨min (min δ1 η) δ3, lt_min (lt_min hδ1 hη0) hδ30, ?_⟩
  rintro ⟨u, t⟩ ⟨h0u', hut', htT'⟩ hd
  simp only at h0u' hut' htT'
  rw [Prod.dist_eq] at hd
  have hd1 : dist u u0 < min (min δ1 η) δ3 := (le_max_left _ _).trans_lt hd
  have hd2 : dist t t0 < min (min δ1 η) δ3 := (le_max_right _ _).trans_lt hd
  have hu1 : dist u u0 < δ1 := hd1.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have ht1 : dist t t0 < η := hd2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have ht2 : dist t t0 < δ3 := hd2.trans_le (min_le_right _ _)
  have htq : t ≤ q := by
    rcases hqcase with h | h
    · rw [h]; exact htT'
    · have : δ3 = q - t0 := by simp only [hδ3, if_pos h]
      rw [this] at ht2
      have := (abs_lt.1 (by rwa [Real.dist_eq] at ht2)).2
      linarith
  have huq : u ≤ q := hut'.trans htq
  have hS : dist (F u q) (F u0 q) < ε / 4 := hc u ⟨h0u', huq⟩ hu1
  rw [Real.dist_eq] at ht1
  have ht1' := abs_lt.1 ht1
  have e1 : ‖F u q - F u t‖ ≤ K * (q - t) := hlip u q t h0u' hut' htq hqT
  have e3 : ‖F u0 q - F u0 t0‖ ≤ K * (q - t0) := hlip u0 q t0 h0u hut hqt0 hqT
  have e1' : K * (q - t) ≤ K * (q - t0) + K * η := by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left (by linarith) hK
  show dist (F u t) (F u0 t0) < ε
  have d1 : dist (F u t) (F u q) ≤ K * (q - t0) + K * η := by
    rw [dist_comm, dist_eq_norm]; exact e1.trans e1'
  have d3 : dist (F u0 q) (F u0 t0) ≤ K * (q - t0) := by
    rw [dist_eq_norm]; exact e3
  have d0 := dist_triangle (F u t) (F u q) (F u0 t0)
  have d00 := dist_triangle (F u q) (F u0 q) (F u0 t0)
  linarith

end HRS.MS.R2Interp

end
