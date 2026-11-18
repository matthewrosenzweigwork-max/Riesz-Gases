import HRS.Whole.AppendixA
import HRS.PDE.ToolboxRd.Fourier

/-!
# M1 of `UniqPlan.md`, part 1: from `ulocNormE` to uniform local `L²` mass

* `sobolevNormE_zero_eq` / `sobolevNormE_zero_lt_top_iff`: for the Fourier-defined norm,
  `sobolevNormE 0 w = eLpNorm w 2` for `w ∈ L²` and `sobolevNormE 0 w < ⊤ ↔ MemLp w 2`;
  `sobolevNormE_zero_le` : `sobolevNormE 0 ≤ sobolevNormE r` for `r ≥ 0`.
* `LocMass B u`: `u` is a.e.-strongly measurable and `∫_{ball c 1} u² ≤ B²` for every centre `c`.
* `locMass_of_ulocNormE`: `ulocNormE m χ u ≤ ofReal B` (any `m : ℕ`, in particular `m = 0, 1`) gives `LocMass B u`.
* `LocMass.ball_sq` (mass on balls of radius `r`) and `LocMass.ball_l1` (the `L¹` mass on balls of radius `r`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqM1

open HRS HRS.Whole HRS.Whole.AppendixA HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

/-! ### The Fourier-defined `sobolevNormE` at order `0` -/

theorem memSobolev_zero_iff {u : Euc d → ℝ} : HRS.PDE.ToolboxRd.MemSobolev 0 u ↔ MemLp u 2 volume := by
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  simpa using integrable_norm_sq_fourierL2 h

theorem sobolevNormE_zero_eq {u : Euc d → ℝ} (hu : MemLp u 2 volume) :
    sobolevNormE 0 u = eLpNorm u 2 volume := by
  have h : HRS.PDE.ToolboxRd.MemSobolev (0 : ℝ) u := memSobolev_zero_iff.2 hu
  have h1 : sobolevNormSq (0 : ℝ) u = ∫ x, u x ^ 2 := by
    rw [sobolevNormSq_eq]
    simp only [Real.rpow_zero, one_mul]
    exact integral_norm_sq_fourierL2 hu
  unfold sobolevNormE
  rw [if_pos h, h1, hu.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  congr 1
  rw [Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat, one_div, Real.norm_eq_abs]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [sq_abs]

/-- The bridge: `sobolevNormE 0 w` is finite iff `w ∈ L²`. -/
theorem sobolevNormE_zero_lt_top_iff {w : Euc d → ℝ} : sobolevNormE 0 w < ⊤ ↔ MemLp w 2 volume := by
  constructor
  · intro h
    by_contra hw
    have : ¬ HRS.PDE.ToolboxRd.MemSobolev (0 : ℝ) w := fun h' => hw (memSobolev_zero_iff.1 h')
    unfold sobolevNormE at h
    rw [if_neg this] at h
    exact lt_irrefl _ h
  · intro hw
    rw [sobolevNormE_zero_eq hw]
    exact hw.eLpNorm_lt_top

/-- A finite `H^r` norm (`r` any real) implies `L²`. -/
theorem memLp_of_sobolevNormE_lt_top {r : ℝ} {w : Euc d → ℝ} (h : sobolevNormE r w < ⊤) :
    MemLp w 2 volume := by
  by_contra hw
  have : ¬ HRS.PDE.ToolboxRd.MemSobolev r w := fun h' => hw h'.1
  unfold sobolevNormE at h
  rw [if_neg this] at h
  exact lt_irrefl _ h

theorem sobolevNormE_zero_le {r : ℝ} (hr : 0 ≤ r) (w : Euc d → ℝ) :
    sobolevNormE 0 w ≤ sobolevNormE r w := by
  by_cases h : sobolevNormE r w < ⊤
  · have hs : HRS.PDE.ToolboxRd.MemSobolev r w := by
      by_contra hs
      unfold sobolevNormE at h
      rw [if_neg hs] at h
      exact lt_irrefl _ h
    have hs0 : HRS.PDE.ToolboxRd.MemSobolev (0 : ℝ) w := memSobolev_mono hr hs
    unfold sobolevNormE
    rw [if_pos hs, if_pos hs0]
    refine ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_)
    refine integral_mono hs0.2 hs.2 fun ξ => ?_
    have h1 : (1 : ℝ) ≤ 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := one_le_wt ξ
    have h2 : (1 : ℝ) ≤ (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ r := Real.one_le_rpow h1 hr
    simp only [Real.rpow_zero, one_mul]
    calc ‖fourierL2 w ξ‖ ^ 2 = 1 * ‖fourierL2 w ξ‖ ^ 2 := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  · rw [not_lt, top_le_iff] at h
    rw [h]; exact le_top

/-! ### Uniform local `L²` mass -/

/-- `u` is a.e.-strongly measurable with `∫_{ball c 1} u² ≤ B²` for every centre `c`. -/
def LocMass (B : ℝ) (u : Euc d → ℝ) : Prop :=
  AEStronglyMeasurable u volume ∧
    ∀ c : Euc d, ∫⁻ y in ball c 1, ‖u y‖ₑ ^ 2 ≤ ENNReal.ofReal (B ^ 2)

theorem sq_eLpNorm_two {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, one_div]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  simp
  exact hf

theorem locMass_of_ulocNormE {m : ℕ} {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) {u : Euc d → ℝ}
    {B : ℝ} (hB : 0 ≤ B) (hu : ulocNormE m χ u ≤ ENNReal.ofReal B) : LocMass B u := by
  have h0 : ∀ c : Euc d, sobolevNormE 0 (fun x => χ (x - c) * u x) ≤ ENNReal.ofReal B := fun c =>
    (sobolevNormE_zero_le (Nat.cast_nonneg m) _).trans
      ((le_iSup (fun z : Euc d => sobolevNormE (m : ℝ) fun x => χ (x - z) * u x) c).trans hu)
  have hmem : ∀ c : Euc d, MemLp (fun x => χ (x - c) * u x) 2 volume := fun c =>
    sobolevNormE_zero_lt_top_iff.1 ((h0 c).trans_lt ENNReal.ofReal_lt_top)
  have hcut : ∀ c : Euc d, ∀ y ∈ ball c 1, χ (y - c) = 1 := fun c y hy =>
    hχ.2.2.2.2 _ (by simpa [dist_eq_norm] using (mem_ball.1 hy).le)
  refine ⟨?_, fun c => ?_⟩
  · have hcov : ∀ c : Euc d, AEStronglyMeasurable u (volume.restrict (ball c 1)) := by
      intro c
      have := (hmem c).aestronglyMeasurable.restrict (s := ball c 1)
      refine this.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      simp [hcut c y hy]
    have hunion : (⋃ n, ball (TopologicalSpace.denseSeq (Euc d) n) 1) = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq (Euc d)).exists_dist_lt x one_pos
      exact Set.mem_iUnion.2 ⟨n, by rw [mem_ball]; exact hn⟩
    have : AEStronglyMeasurable u (volume.restrict (⋃ n, ball (TopologicalSpace.denseSeq (Euc d) n) 1)) :=
      aestronglyMeasurable_iUnion_iff.2 fun n => hcov _
    rwa [hunion, Measure.restrict_univ] at this
  · have h1 : ∫⁻ y in ball c 1, ‖u y‖ₑ ^ 2 ≤ eLpNorm (fun x => χ (x - c) * u x) 2 volume ^ 2 := by
      rw [sq_eLpNorm_two (hmem c).aestronglyMeasurable]
      calc ∫⁻ y in ball c 1, ‖u y‖ₑ ^ 2 = ∫⁻ y in ball c 1, ‖χ (y - c) * u y‖ₑ ^ 2 := by
            refine setLIntegral_congr_fun measurableSet_ball fun y hy => ?_
            simp [hcut c y hy]
        _ ≤ _ := setLIntegral_le_lintegral _ _
    refine h1.trans ?_
    have h2 : eLpNorm (fun x => χ (x - c) * u x) 2 volume ≤ ENNReal.ofReal B := by
      have := h0 c
      rwa [sobolevNormE_zero_eq (hmem c)] at this
    calc _ ≤ ENNReal.ofReal B ^ 2 := by gcongr
      _ = _ := by rw [ENNReal.ofReal_pow hB]

theorem LocMass.mono_B {B B' : ℝ} {u : Euc d → ℝ} (h : LocMass B u) (hB : |B| ≤ |B'|) : LocMass B' u :=
  ⟨h.1, fun c => (h.2 c).trans (ENNReal.ofReal_le_ofReal (by
    simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg B) hB 2))⟩

/-- Covering number: a ball of radius `r` is covered by `N` unit balls with centres `c + x_k`. -/
theorem exists_unit_cover (d : ℕ) (r : ℝ) :
    ∃ s : Finset (Euc d), ∀ c : Euc d, ball c r ⊆ ⋃ x ∈ s, ball (c + x) 1 := by
  obtain ⟨t, -, ht, hcov⟩ := finite_cover_balls_of_compact (isCompact_closedBall (0 : Euc d) r) one_pos
  refine ⟨ht.toFinset, fun c y hy => ?_⟩
  have : y - c ∈ closedBall (0 : Euc d) r := by
    simpa [dist_eq_norm] using (mem_ball.1 hy).le
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (hcov this)
  refine Set.mem_iUnion₂.2 ⟨x, by simpa using hx, ?_⟩
  rw [mem_ball] at hyx ⊢
  simpa [dist_eq_norm, add_comm, sub_sub] using hyx

/-- Mass on balls of radius `r`: `∫_{ball c r} u² ≤ N(d,r) B²`. -/
theorem exists_ball_sq_bound (d : ℕ) (r : ℝ) :
    ∃ N : ℕ, ∀ (B : ℝ) (u : Euc d → ℝ), LocMass B u → ∀ c : Euc d,
      ∫⁻ y in ball c r, ‖u y‖ₑ ^ 2 ≤ (N : ℝ≥0∞) * ENNReal.ofReal (B ^ 2) := by
  obtain ⟨s, hs⟩ := exists_unit_cover d r
  refine ⟨s.card, fun B u hu c => ?_⟩
  calc ∫⁻ y in ball c r, ‖u y‖ₑ ^ 2 ≤ ∫⁻ y in ⋃ x ∈ s, ball (c + x) 1, ‖u y‖ₑ ^ 2 :=
        lintegral_mono_set (hs c)
    _ ≤ ∑ x ∈ s, ∫⁻ y in ball (c + x) 1, ‖u y‖ₑ ^ 2 := by
        rw [show (⋃ x ∈ s, ball (c + x) 1) = ⋃ x : s, ball (c + (x : Euc d)) 1 by
          ext; simp]
        refine (lintegral_iUnion_le _ _).trans ?_
        rw [tsum_fintype]
        exact (Finset.sum_coe_sort s fun x => ∫⁻ y in ball (c + x) 1, ‖u y‖ₑ ^ 2).le
    _ ≤ ∑ x ∈ s, ENNReal.ofReal (B ^ 2) := Finset.sum_le_sum fun x _ => hu.2 _
    _ = _ := by simp

/-- `L¹` mass on balls of radius `r`: `∫_{ball c r} |u| ≤ K(d,r) B`. -/
theorem exists_ball_l1_bound (d : ℕ) (r : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (B : ℝ) (u : Euc d → ℝ), 0 ≤ B → LocMass B u → ∀ c : Euc d,
      ∫⁻ y in ball c r, ‖u y‖ₑ ≤ ENNReal.ofReal (K * B) := by
  obtain ⟨N, hN⟩ := exists_ball_sq_bound d r
  set V : ℝ≥0∞ := volume (ball (0 : Euc d) r) with hV
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  refine ⟨Real.sqrt N * V.toReal ^ (1 / 2 : ℝ), by positivity, fun B u hB hu c => ?_⟩
  set μ : Measure (Euc d) := volume.restrict (ball c r) with hμ
  have hμu : μ Set.univ = V := by
    simp [hμ, Measure.restrict_apply, Measure.addHaar_ball_center, hV]
  have h2 : eLpNorm u 2 μ ≤ ENNReal.ofReal (Real.sqrt N * B) := by
    have hsq : eLpNorm u 2 μ ^ 2 ≤ ENNReal.ofReal (Real.sqrt N * B) ^ 2 := by
      rw [sq_eLpNorm_two (hu.1.restrict), ← ENNReal.ofReal_pow (by positivity)]
      refine (hN B u hu c).trans ?_
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N), ENNReal.ofReal_mul (Nat.cast_nonneg N),
        ENNReal.ofReal_natCast]
    by_contra hlt
    exact absurd hsq (not_le.2 (ENNReal.pow_lt_pow_left two_ne_zero (not_le.1 hlt)))
  have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ) (p := 1) (q := 2) (by norm_num) hu.1.restrict
  rw [eLpNorm_one_eq_lintegral_enorm, hμu] at h1
  refine h1.trans ?_
  have : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by norm_num
  have hVr : V ^ (1 / 2 : ℝ) = ENNReal.ofReal (V.toReal ^ (1 / 2 : ℝ)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num), ENNReal.ofReal_toReal hVt]
  rw [this, hVr]
  calc eLpNorm u 2 μ * ENNReal.ofReal (V.toReal ^ (1 / 2 : ℝ))
      ≤ ENNReal.ofReal (Real.sqrt N * B) * ENNReal.ofReal (V.toReal ^ (1 / 2 : ℝ)) := by gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  exact hu.1.restrict

end HRS.MS.UniqM1
