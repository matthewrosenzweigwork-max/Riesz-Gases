import HRS.MC.S7PIDKPoly
import HRS.MC.S7PIDKSemi

/-!
# Packet PI-D, sub-packet K (part 4): pointwise (in `u`) limit of the polygonal path at a fixed time

For `u ∈ (c,c']`, `u ≠ t_a ∈ [0,T]`, the value at time `t_a` of the polygonal path of the kernel nodes
`p₀ 1_{u ≤ t_i} V^{t_i,u} e_k` converges, as the dyadic level `n → ∞`, to `p₀ 1_{u ≤ t_a} V^{t_a,u} e_k`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDK

open HRS HRS.Sec7 HRS.MC.Sec7.PID HRS.MC.Sec7.PIE

variable {d : ℕ}

/-- continuity in `s` of the causal kernel at a time `t > u`, within `[c,c']` -/
theorem S7PIDK_causal_cont_lt (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    {c c' : ℝ} (hc' : c' ≤ T) {u : ℝ} (hu : 0 < u) (e : NegSobolev d m) (p₀ : ℝ) {t : ℝ}
    (hut : u < t) (htc : t ∈ Set.Icc c c') :
    ContinuousWithinAt (fun s => p₀ • causalVec R.D R.ρ m s u e) (Set.Icc c c') t := by
  obtain ⟨J, n₀, H, hn₀, hJ, hm0, hm1⟩ := S7PIDP.S7PIDP_pie R m hm T hT
  have hV := S7PIDP.S7PIDP_V_within H hn₀ hJ hm0 hm1 hu e t ⟨hut.le, htc.2.trans hc'⟩
  have hmono : ContinuousWithinAt (fun s => Vprop R.D R.ρ m s u e) (Set.Icc c c') t := by
    refine hV.mono_of_mem_nhdsWithin ?_
    exact mem_nhdsWithin.2 ⟨Set.Ioi u, isOpen_Ioi, hut, fun s hs => ⟨hs.1.le, hs.2.2.trans hc'⟩⟩
  refine (hmono.const_smul p₀).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [mem_nhdsWithin.2 ⟨Set.Ioi u, isOpen_Ioi, hut, fun s hs => hs.1⟩] with s hs
    unfold causalVec
    rw [if_pos (le_of_lt hs)]
    rfl
  · unfold causalVec
    rw [if_pos hut.le]
    rfl

/-- continuity in `s` of the causal kernel at a time `t < u` (where it vanishes nearby) -/
theorem S7PIDK_causal_cont_gt (R : Regime d) (m : ℝ) (e : NegSobolev d m) (p₀ : ℝ) {c c' u t : ℝ}
    (hut : t < u) :
    ContinuousWithinAt (fun s => p₀ • causalVec R.D R.ρ m s u e) (Set.Icc c c') t := by
  refine (continuousWithinAt_const (b := (0 : NegSobolev d m))).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hut)] with s hs
    unfold causalVec
    rw [if_neg (not_le.2 hs), smul_zero]
  · unfold causalVec
    rw [if_neg (not_le.2 hut), smul_zero]

theorem S7PIDK_pathAt_tendsto (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    {c c' : ℝ} (hc : 0 ≤ c) (hcc : c < c') (hc' : c' ≤ T) (p₀ : ℝ) (k : NonzeroLattice d)
    {u ta : ℝ} (hu : u ∈ Set.Ioc c c') (hta : ta ∈ Set.Icc (0 : ℝ) T) (hne : u ≠ ta) :
    Tendsto (fun n : ℕ => pathAt (polyPath R.D R.ρ m T c c' n
        (fun i => p₀ • causalVec R.D R.ρ m (gridPt c c' n i) u (modeVec m k))) ta) atTop
      (𝓝 (p₀ • causalVec R.D R.ρ m ta u (modeVec m k))) := by
  obtain ⟨C₁, hC₁, hC⟩ := S7PIDP.s7_PID_poly_proof R m hm T hT
  have hu0 : 0 < u := lt_of_le_of_lt hc hu.1
  have hpa : ∀ n, pathAt (polyPath R.D R.ρ m T c c' n
        (fun i => p₀ • causalVec R.D R.ρ m (gridPt c c' n i) u (modeVec m k))) ta =
      if ta ≤ c' then polyAt c c' n (fun i => p₀ • causalVec R.D R.ρ m (gridPt c c' n i) u (modeVec m k)) ta
      else Vprop R.D R.ρ m ta c' (p₀ • causalVec R.D R.ρ m (gridPt c c' n (2 ^ n)) u (modeVec m k)) :=
    fun n => (hC c c' hc hcc.le hc' n _).1 hcc ta hta
  simp_rw [hpa]
  by_cases hac : ta ≤ c'
  · simp_rw [if_pos hac]
    by_cases hlow : ta < c
    · -- `t_a < c`: the polygonal value is the value at `c`, which vanishes
      have hcl : ∀ n : ℕ, polyAt c c' n (fun i => p₀ • causalVec R.D R.ρ m (gridPt c c' n i) u (modeVec m k)) ta =
          polyAt c c' n (fun i => p₀ • causalVec R.D R.ρ m (gridPt c c' n i) u (modeVec m k)) c := by
        intro n
        unfold polyAt
        have h1 : max c (min ta c') = c := max_eq_left (by rw [min_eq_left hac]; exact hlow.le)
        have h2 : max c (min c c') = c := by rw [min_eq_left hcc.le, max_self]
        rw [h1, h2]
      simp_rw [hcl]
      have hcont := S7PIDK_causal_cont_gt R m (modeVec m k) p₀ (c := c) (c' := c') (u := u) (t := c) hu.1
      have := S7PIDK_polyAt_tendsto c c' hc hcc
        (fun s => p₀ • causalVec R.D R.ρ m s u (modeVec m k)) c ⟨le_rfl, hcc.le⟩ hcont
      have e0 : causalVec R.D R.ρ m c u (modeVec m k) = 0 := by
        unfold causalVec; rw [if_neg (not_le.2 hu.1)]
      have e1 : causalVec R.D R.ρ m ta u (modeVec m k) = 0 := by
        unfold causalVec; rw [if_neg (not_le.2 (hlow.trans hu.1))]
      rw [e1, smul_zero]
      simpa [e0] using this
    · have htc : ta ∈ Set.Icc c c' := ⟨not_lt.1 hlow, hac⟩
      have hcont : ContinuousWithinAt (fun s => p₀ • causalVec R.D R.ρ m s u (modeVec m k)) (Set.Icc c c') ta := by
        rcases lt_or_gt_of_ne hne with h | h
        · exact S7PIDK_causal_cont_lt R m hm T hT hc' hu0 (modeVec m k) p₀ h htc
        · exact S7PIDK_causal_cont_gt R m (modeVec m k) p₀ h
      exact S7PIDK_polyAt_tendsto c c' hc hcc
        (fun s => p₀ • causalVec R.D R.ρ m s u (modeVec m k)) ta htc hcont
  · -- `t_a > c'`: constant sequence, by the semigroup law for `V`
    simp_rw [if_neg hac]
    have hct : c' < ta := not_le.1 hac
    have hgrid : ∀ n : ℕ, gridPt c c' n (2 ^ n) = c' := by
      intro n
      unfold gridPt
      have h2 : (0 : ℝ) < 2 ^ n := by positivity
      push_cast
      field_simp
      ring
    have e1 : causalVec R.D R.ρ m c' u (modeVec m k) = Vprop R.D R.ρ m c' u (modeVec m k) := by
      unfold causalVec; rw [if_pos hu.2]
    have e2 : causalVec R.D R.ρ m ta u (modeVec m k) = Vprop R.D R.ρ m ta u (modeVec m k) := by
      unfold causalVec; rw [if_pos (hu.2.trans hct.le)]
    simp_rw [hgrid, e1, e2]
    simp_rw [S7PIDK_V_semigroup R m hm T hT hu0 hu.2 hct hta.2 p₀ k]
    exact tendsto_const_nhds

end HRS.MC.Sec7.S7PIDK

end
