import HRS.MS.MovAdjAux2

/-!
# S6.7 (packet P1, part 2): the weighted class `RgW` for Schwartz data, integration by parts in that class

Namespace `HRS.MS.MovAdj`, helpers `s67_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.

* `s67_rgW_schwartz`: a Schwartz function is in `RgW (1+|x|)^{-(d+1)} 1 c`.
* `s67_rgW_one_schwartz`: a Schwartz function is in `RgW 1 1 c` (bounded with bounded derivative).
* `s67_ibp_div_rgW`: `∫ div Y ψ = -∫ ⟨Y,∇ψ⟩` for `Y` with components in `RgW W 1 c` and `ψ ∈ C¹` bounded with bounded gradient.
* `s67_mul_rgW`: `RgW W 1` times a bounded `C¹` function with bounded derivative.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdj

open HRS HRS.Whole HRS.MH.DualityRd HRS.MS.Mov63

variable {d : ℕ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-- the decay weight -/
abbrev s67W (d : ℕ) : Euc d → ℝ := fun y => (1 + ‖y‖) ^ (-((d : ℝ) + 1))

theorem s67_W_pos (x : Euc d) : 0 < s67W d x := Real.rpow_pos_of_pos (by positivity) _

theorem s67_W_le_one (x : Euc d) : s67W d x ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x])
    (by have := Nat.cast_nonneg (α := ℝ) d; linarith)

theorem s67_rgW_schwartz (S : 𝓢R) :
    ∃ c : ℝ, 0 ≤ c ∧ HRS.MP.RdGen.RgW (s67W d) 1 c ⇑S := by
  set M0 : ℝ := (Finset.Iic (d + 1, 0)).sup (schwartzSeminormFamily ℝ (Euc d) ℝ) S with hM0
  set M1 : ℝ := (Finset.Iic (d + 1, 1)).sup (schwartzSeminormFamily ℝ (Euc d) ℝ) S with hM1
  have hM0n : 0 ≤ M0 := by positivity
  have hM1n : 0 ≤ M1 := by positivity
  refine ⟨2 ^ (d + 1) * (M0 + M1), by positivity, S.smooth 1, fun n hn x => ?_⟩
  have key : ∀ k : ℕ, ∀ M : ℝ, (1 + ‖x‖) ^ (d + 1) * ‖iteratedFDeriv ℝ k S x‖ ≤ 2 ^ (d + 1) * M →
      ‖iteratedFDeriv ℝ k S x‖ ≤ 2 ^ (d + 1) * M * s67W d x := by
    intro k M h
    have hpos : 0 < (1 + ‖x‖) ^ (d + 1) := by positivity
    have e : s67W d x = ((1 + ‖x‖) ^ (d + 1))⁻¹ := by
      unfold s67W
      rw [Real.rpow_neg (by positivity)]
      congr 1
      rw [← Real.rpow_natCast]
      push_cast
      rfl
    rw [e, ← div_eq_mul_inv, le_div_iff₀ hpos]
    linarith
  have b0 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (d + 1, 0)) (k := d + 1) (n := 0)
    (le_refl _) (le_refl _) S x
  have b1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (d + 1, 1)) (k := d + 1) (n := 1)
    (le_refl _) (le_refl _) S x
  interval_cases n
  · refine (key 0 M0 b0).trans ?_
    have : 2 ^ (d + 1) * M0 ≤ 2 ^ (d + 1) * (M0 + M1) := by nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) (d + 1)]
    exact mul_le_mul_of_nonneg_right this (s67_W_pos x).le
  · refine (key 1 M1 b1).trans ?_
    have : 2 ^ (d + 1) * M1 ≤ 2 ^ (d + 1) * (M0 + M1) := by nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) (d + 1)]
    exact mul_le_mul_of_nonneg_right this (s67_W_pos x).le

theorem s67_rgW_one_schwartz (S : 𝓢R) :
    ∃ c : ℝ, 0 ≤ c ∧ HRS.MP.RdGen.RgW (fun _ : Euc d => (1 : ℝ)) 1 c ⇑S := by
  obtain ⟨c, hc0, hc⟩ := s67_rgW_schwartz S
  refine ⟨c, hc0, hc.1, fun n hn x => ?_⟩
  have := hc.2 n hn x
  have h1 := s67_W_le_one x
  calc ‖iteratedFDeriv ℝ n S x‖ ≤ c * s67W d x := this
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left h1 hc0
    _ = c * 1 := rfl

/-- `RgW` gives integrability of the function and of its first derivative in a given direction. -/
theorem s67_rgW_int (hd : 1 ≤ d) {u : Euc d → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hu : HRS.MP.RdGen.RgW (s67W d) 1 c u) : Integrable u :=
  dc1b_rgW_int hd hc hu

theorem s67_rgW_int_deriv (hd : 1 ≤ d) {u : Euc d → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hu : HRS.MP.RdGen.RgW (s67W d) 1 c u) (v : Euc d) (hv : ‖v‖ ≤ 1) :
    Integrable (fun x => fderiv ℝ u x v) := by
  have hcont : Continuous fun x => fderiv ℝ u x v :=
    (hu.1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  refine Integrable.mono' ((HRS.MP.RdGen.rg_W_integrable hd).const_mul c) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have h2 := hu.2 1 le_rfl x
  have h3 : ‖fderiv ℝ u x‖ ≤ c * s67W d x := by
    have := h2
    rw [norm_iteratedFDeriv_one] at this
    exact this
  calc ‖fderiv ℝ u x v‖ ≤ ‖fderiv ℝ u x‖ * ‖v‖ := (fderiv ℝ u x).le_opNorm v
    _ ≤ (c * s67W d x) * 1 := mul_le_mul h3 hv (norm_nonneg _) ((mul_nonneg hc (s67_W_pos x).le))
    _ = c * s67W d x := mul_one _

/-- **Integration by parts in the weighted class.** -/
theorem s67_ibp_div_rgW (hd : 1 ≤ d) {Y : Euc d → Euc d} {ψ : Euc d → ℝ} {c B B' : ℝ} (hc : 0 ≤ c)
    (hY : ∀ i : Fin d, HRS.MP.RdGen.RgW (s67W d) 1 c (fun y => Y y i)) (hψ : ContDiff ℝ 1 ψ)
    (hψb : ∀ x, |ψ x| ≤ B) (hψd : ∀ x, ‖fderiv ℝ ψ x‖ ≤ B') :
    ∫ x, movDiv Y x * ψ x = -∫ x, inner ℝ (Y x) (gradient ψ x) := by
  have hYc : ContDiff ℝ 1 Y := contDiff_euclidean.2 fun i => (hY i).1
  refine s67_ibp_div hYc hψ hψb hψd (fun i => s67_rgW_int hd hc (hY i)) (fun i => ?_)
  have h1 : ∀ x, (fderiv ℝ Y x (EuclideanSpace.single i 1)) i =
      fderiv ℝ (fun y => Y y i) x (EuclideanSpace.single i 1) :=
    fun x => mnc_comp_fderiv_apply Y (hYc.differentiable one_ne_zero) x _ i
  simp_rw [h1]
  exact s67_rgW_int_deriv hd hc (hY i) _ (by simp)

/-- `RgW W 1` times a bounded `C¹` function with bounded derivative. -/
theorem s67_mul_rgW {u g : Euc d → ℝ} {C c : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c)
    (hu : HRS.MP.RdGen.RgW (s67W d) 1 C u) (hg : HRS.MP.RdGen.RgW (fun _ : Euc d => (1 : ℝ)) 1 c g) :
    HRS.MP.RdGen.RgW (s67W d) 1 (2 ^ 1 * C * c) (fun y => u y * g y) :=
  dc1a_mul_rgW hC hc hu hg


/-- Integration by parts with per-coordinate constants. -/
theorem s67_ibp_div_rgW' (hd : 1 ≤ d) {Y : Euc d → Euc d} {ψ : Euc d → ℝ} {B B' : ℝ}
    (hY : ∀ i : Fin d, ∃ c : ℝ, 0 ≤ c ∧ HRS.MP.RdGen.RgW (s67W d) 1 c (fun y => Y y i))
    (hψ : ContDiff ℝ 1 ψ) (hψb : ∀ x, |ψ x| ≤ B) (hψd : ∀ x, ‖fderiv ℝ ψ x‖ ≤ B') :
    ∫ x, movDiv Y x * ψ x = -∫ x, inner ℝ (Y x) (gradient ψ x) := by
  choose c hc0 hcW using hY
  refine s67_ibp_div_rgW hd (c := ∑ i, c i) (Finset.sum_nonneg fun i _ => hc0 i) (fun i => ?_) hψ hψb hψd
  exact HRS.MP.RdGen.RgW.mono (fun x => (s67_W_pos x).le) (hcW i)
    (Finset.single_le_sum (f := c) (fun i _ => hc0 i) (Finset.mem_univ i))

/-- A Schwartz function is bounded with bounded derivative. -/
theorem s67_schwartz_bounds (S : 𝓢R) : ∃ B : ℝ, 0 ≤ B ∧ (∀ x, |S x| ≤ B) ∧ (∀ x, ‖fderiv ℝ S x‖ ≤ B) := by
  obtain ⟨c, hc0, hc⟩ := s67_rgW_one_schwartz S
  refine ⟨c, hc0, fun x => ?_, fun x => ?_⟩
  · have := hc.2 0 (Nat.zero_le _) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    simpa using this
  · have := hc.2 1 le_rfl x
    rw [norm_iteratedFDeriv_one] at this
    simpa using this

/-- Bounds of a `C_b²` function. -/
theorem s67_memCb_bounds {u : Euc d → ℝ} (hu : MemCb 2 u) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ x, |u x| ≤ B) ∧ (∀ x, ‖fderiv ℝ u x‖ ≤ B) ∧
      (∀ x, ‖iteratedFDeriv ℝ 2 u x‖ ≤ B) := by
  obtain ⟨B0, hB0⟩ := hu.2 0 (Nat.zero_le _)
  obtain ⟨B1, hB1⟩ := hu.2 1 (by norm_num)
  obtain ⟨B2, hB2⟩ := hu.2 2 le_rfl
  have h0 : B0 ≤ max 0 (max B0 (max B1 B2)) := (le_max_left B0 _).trans (le_max_right 0 _)
  have h1 : B1 ≤ max 0 (max B0 (max B1 B2)) :=
    ((le_max_left B1 B2).trans (le_max_right B0 _)).trans (le_max_right 0 _)
  have h2 : B2 ≤ max 0 (max B0 (max B1 B2)) :=
    ((le_max_right B1 B2).trans (le_max_right B0 _)).trans (le_max_right 0 _)
  refine ⟨max 0 (max B0 (max B1 B2)), le_max_left _ _, fun x => ?_, fun x => ?_, fun x => ?_⟩
  · have := hB0 ⟨x, rfl⟩
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact this.trans h0
  · have := hB1 ⟨x, rfl⟩
    simp only [norm_iteratedFDeriv_one] at this
    exact this.trans h1
  · exact (hB2 ⟨x, rfl⟩).trans h2

end HRS.MS.MovAdj
