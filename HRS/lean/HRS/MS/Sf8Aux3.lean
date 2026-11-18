import HRS.MS.Sf8Aux2

/-!
# MS-SF8II, abstract core (route: `Sf8Plan.md`)

`core`: the symmetrized pairing with a weight `ς ∈ [0,1]` supported in a ball `B(c,R₀)`, for `w` with local
`L²`/`L¹` bounds (no global `L²` assumption), is absolutely convergent, is the limit of its truncations
and obeys an explicit bound.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Sf8

open HRS.Whole HRS.MS.SameFunction

variable {d : ℕ}

theorem lip_nonneg (hd : 1 ≤ d) {f : Euc d → ℝ} {L : ℝ} (h : ∀ x y, |f x - f y| ≤ L * ‖x - y‖) :
    0 ≤ L := by
  obtain ⟨z₀, hz₀⟩ := msf_exists_ne (d := d) hd
  have h1 := h 0 z₀
  rw [zero_sub, norm_neg] at h1
  have hpos : 0 < ‖z₀‖ := norm_pos_iff.2 hz₀
  by_contra hneg
  push_neg at hneg
  linarith [abs_nonneg (f 0 - f z₀), mul_neg_of_neg_of_pos hneg hpos]

theorem nonneg_facts (hd : 1 ≤ d) {s : ℝ} {κ : Euc d → ℝ} {K₀ La Λ : ℝ}
    (hbd : ∀ z : Euc d, z ≠ 0 → |κ z| ≤ K₀ * ‖z‖ ^ (-s - 1)) {a : Euc d → ℝ}
    (ha : HRS.PDE.ToolboxRd.IsLipschitz La a)
    (hjb : ∀ x, jbracket x ^ ((d : ℝ) + 3) * |a x| ≤ Λ) : 0 ≤ K₀ ∧ 0 ≤ La ∧ 0 ≤ Λ := by
  obtain ⟨z₀, hz₀⟩ := msf_exists_ne (d := d) hd
  refine ⟨?_, lip_nonneg hd ha, (abs_nonneg (a 0)).trans (msf_abs_le hjb 0)⟩
  have h1 := hbd z₀ hz₀
  have h2 : 0 < ‖z₀‖ ^ (-s - 1) := Real.rpow_pos_of_pos (norm_pos_iff.2 hz₀) _
  by_contra hneg
  push_neg at hneg
  linarith [abs_nonneg (κ z₀), mul_neg_of_neg_of_pos hneg h2]

theorem near_mem {c x y : Euc d} {R₀ : ℝ} (hx : x ∈ Metric.ball c R₀) (hxy : ‖x - y‖ < 1) :
    y ∈ Metric.ball c (R₀ + 1) := by
  rw [Metric.mem_ball, dist_eq_norm] at hx ⊢
  have : y - c = (y - x) + (x - c) := by abel
  rw [this]
  refine (norm_add_le _ _).trans_lt ?_
  rw [norm_sub_rev]
  linarith

theorem ball_mono_one {c x : Euc d} {R₀ : ℝ} (hx : x ∈ Metric.ball c R₀) :
    x ∈ Metric.ball c (R₀ + 1) := by
  rw [Metric.mem_ball] at hx ⊢; linarith

/-- Pointwise majorant of the symmetrized integrand. -/
theorem pt_sym {κ : Euc d → ℝ} {s K₀ La Λ L' : ℝ} (hK : 0 ≤ K₀) (hL : 0 ≤ La) (hΛ : 0 ≤ Λ)
    (hL' : 0 ≤ L') (hκ0 : κ 0 = 0) (hκ : ∀ z : Euc d, z ≠ 0 → |κ z| ≤ K₀ * ‖z‖ ^ (-s - 1))
    {a ς : Euc d → ℝ} (ha : HRS.PDE.ToolboxRd.IsLipschitz La a) (haΛ : ∀ x, |a x| ≤ Λ)
    (hς0 : ∀ x, 0 ≤ ς x) (hς1 : ∀ x, ς x ≤ 1) (hςL : ∀ x y, |ς x - ς y| ≤ L' * ‖x - y‖)
    {c : Euc d} {R₀ : ℝ} (hsupp : ∀ x, ς x ≠ 0 → x ∈ Metric.ball c R₀) (w : Euc d → ℝ)
    (x y : Euc d) :
    |κ (x - y) * w x * w y * (a y * ς x - a x * ς y)| ≤
      K₀ * (La + Λ) * (1 + L') * (msf_I1 s (x - y) *
        (|(Metric.ball c (R₀ + 1)).indicator w x| * |(Metric.ball c (R₀ + 1)).indicator w y|)) +
      K₀ * Λ * (msf_I2 s (x - y) * (Metric.ball c R₀).indicator (fun x => |w x|) x * |w y| +
        msf_I2 s (x - y) * |w x| * (Metric.ball c R₀).indicator (fun x => |w x|) y) := by
  have hςh : ∀ x, ς x * |w x| ≤ (Metric.ball c R₀).indicator (fun x => |w x|) x := by
    intro x
    by_cases hx : ς x = 0
    · rw [hx, zero_mul]; exact Set.indicator_nonneg (fun _ _ => abs_nonneg _) x
    · rw [Set.indicator_of_mem (hsupp x hx)]
      calc ς x * |w x| ≤ 1 * |w x| := mul_le_mul_of_nonneg_right (hς1 x) (abs_nonneg _)
        _ = _ := one_mul _
  have hhnn : ∀ x, 0 ≤ (Metric.ball c R₀).indicator (fun x => |w x|) x := fun x =>
    Set.indicator_nonneg (fun _ _ => abs_nonneg _) x
  have hI1 := msf_I1_nonneg (d := d) s (x - y)
  have hI2 := msf_I2_nonneg (d := d) s (x - y)
  have hc1 : 0 ≤ K₀ * (La + Λ) * (1 + L') := by positivity
  have hA : 0 ≤ K₀ * (La + Λ) * (1 + L') * (msf_I1 s (x - y) *
        (|(Metric.ball c (R₀ + 1)).indicator w x| * |(Metric.ball c (R₀ + 1)).indicator w y|)) :=
    mul_nonneg hc1 (mul_nonneg hI1 (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
  have hB : 0 ≤ K₀ * Λ * (msf_I2 s (x - y) * (Metric.ball c R₀).indicator (fun x => |w x|) x *
        |w y| + msf_I2 s (x - y) * |w x| * (Metric.ball c R₀).indicator (fun x => |w x|) y) :=
    mul_nonneg (mul_nonneg hK hΛ) (add_nonneg
      (mul_nonneg (mul_nonneg hI2 (hhnn x)) (abs_nonneg _))
      (mul_nonneg (mul_nonneg hI2 (abs_nonneg _)) (hhnn y)))
  have habs : |κ (x - y) * w x * w y * (a y * ς x - a x * ς y)| =
      |κ (x - y)| * (|w x| * |w y|) * |a y * ς x - a x * ς y| := by
    simp only [abs_mul]; ring
  by_cases hxy : x = y
  · have h0 : |κ (x - y) * w x * w y * (a y * ς x - a x * ς y)| = 0 := by
      rw [hxy, sub_self, hκ0]; simp
    rw [h0]; linarith
  have hz : x - y ≠ 0 := sub_ne_zero.2 hxy
  have hn : 0 < ‖x - y‖ := norm_pos_iff.2 hz
  have hκz := hκ _ hz
  rcases lt_or_ge ‖x - y‖ 1 with h1 | h1
  · -- near region
    suffices hs : |κ (x - y) * w x * w y * (a y * ς x - a x * ς y)| ≤ K₀ * (La + Λ) * (1 + L') *
        (msf_I1 s (x - y) *
          (|(Metric.ball c (R₀ + 1)).indicator w x| * |(Metric.ball c (R₀ + 1)).indicator w y|)) by
      linarith
    by_cases hz0 : ς x = 0 ∧ ς y = 0
    · rw [habs, hz0.1, hz0.2]; simp only [mul_zero, sub_zero, abs_zero]; exact hA
    · have hmem : x ∈ Metric.ball c (R₀ + 1) ∧ y ∈ Metric.ball c (R₀ + 1) := by
        by_cases hx : ς x = 0
        · have hy : ς y ≠ 0 := fun hy => hz0 ⟨hx, hy⟩
          have hy' := hsupp y hy
          refine ⟨near_mem hy' ?_, ball_mono_one hy'⟩
          rwa [norm_sub_rev]
        · have hx' := hsupp x hx
          exact ⟨ball_mono_one hx', near_mem hx' h1⟩
      rw [Set.indicator_of_mem hmem.1, Set.indicator_of_mem hmem.2, habs, msf_I1_lt h1]
      have key1 : |a y * ς x - a x * ς y| ≤ (La + Λ) * (1 + L') * ‖x - y‖ := by
        have e : a y * ς x - a x * ς y = (a y - a x) * ς x + a x * (ς x - ς y) := by ring
        rw [e]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg (hς0 x)]
        have t1 : |a y - a x| ≤ La * ‖x - y‖ := by
          have := ha y x; rwa [norm_sub_rev] at this
        have t2 : |a y - a x| * ς x ≤ La * ‖x - y‖ := by
          calc |a y - a x| * ς x ≤ |a y - a x| * 1 :=
                mul_le_mul_of_nonneg_left (hς1 x) (abs_nonneg _)
            _ ≤ La * ‖x - y‖ := by rw [mul_one]; exact t1
        have t3 : |a x| * |ς x - ς y| ≤ Λ * (L' * ‖x - y‖) :=
          mul_le_mul (haΛ x) (hςL x y) (abs_nonneg _) hΛ
        nlinarith [mul_nonneg (add_nonneg hΛ (mul_nonneg hL hL')) hn.le]
      have e1 : ‖x - y‖ ^ (-s - 1) * ‖x - y‖ = ‖x - y‖ ^ (-s) := by
        rw [Real.rpow_sub_one hn.ne', div_mul_cancel₀ _ hn.ne']
      have hww : 0 ≤ |w x| * |w y| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
      calc |κ (x - y)| * (|w x| * |w y|) * |a y * ς x - a x * ς y|
          ≤ (K₀ * ‖x - y‖ ^ (-s - 1)) * (|w x| * |w y|) * ((La + Λ) * (1 + L') * ‖x - y‖) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hκz hww) key1 (abs_nonneg _)
              (mul_nonneg (mul_nonneg hK (Real.rpow_nonneg hn.le _)) hww)
        _ = K₀ * (La + Λ) * (1 + L') * (‖x - y‖ ^ (-s) * (|w x| * |w y|)) := by
            rw [← e1]; ring
  · -- far region
    suffices hs : |κ (x - y) * w x * w y * (a y * ς x - a x * ς y)| ≤ K₀ * Λ *
        (msf_I2 s (x - y) * (Metric.ball c R₀).indicator (fun x => |w x|) x * |w y| +
        msf_I2 s (x - y) * |w x| * (Metric.ball c R₀).indicator (fun x => |w x|) y) by
      linarith
    rw [habs, msf_I2_ge h1] at *
    have hκ2 : |κ (x - y)| ≤ K₀ * ‖x - y‖ ^ (-s - 1) := hκz
    have key2 : |a y * ς x - a x * ς y| ≤ Λ * ς x + Λ * ς y := by
      have e : |a y * ς x - a x * ς y| ≤ |a y * ς x| + |a x * ς y| := by
        rw [sub_eq_add_neg, ← abs_neg (a x * ς y)]; exact abs_add_le _ _
      rw [abs_mul, abs_mul, abs_of_nonneg (hς0 x), abs_of_nonneg (hς0 y)] at e
      have t1 : |a y| * ς x ≤ Λ * ς x := mul_le_mul_of_nonneg_right (haΛ y) (hς0 x)
      have t2 : |a x| * ς y ≤ Λ * ς y := mul_le_mul_of_nonneg_right (haΛ x) (hς0 y)
      linarith
    have hww : 0 ≤ |w x| * |w y| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hP : 0 ≤ ‖x - y‖ ^ (-s - 1) := Real.rpow_nonneg hn.le _
    have hςh1 := hςh x
    have hςh2 := hςh y
    calc |κ (x - y)| * (|w x| * |w y|) * |a y * ς x - a x * ς y|
        ≤ (K₀ * ‖x - y‖ ^ (-s - 1)) * (|w x| * |w y|) * (Λ * ς x + Λ * ς y) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hκ2 hww) key2 (abs_nonneg _)
            (mul_nonneg (mul_nonneg hK hP) hww)
      _ = K₀ * Λ * ‖x - y‖ ^ (-s - 1) * ((ς x * |w x|) * |w y| + |w x| * (ς y * |w y|)) := by ring
      _ ≤ K₀ * Λ * ‖x - y‖ ^ (-s - 1) *
          ((Metric.ball c R₀).indicator (fun x => |w x|) x * |w y| +
            |w x| * (Metric.ball c R₀).indicator (fun x => |w x|) y) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (mul_nonneg hK hΛ) hP)
          exact add_le_add (mul_le_mul_of_nonneg_right hςh1 (abs_nonneg _))
            (mul_le_mul_of_nonneg_left hςh2 (abs_nonneg _))
      _ = _ := by ring

/-- Pointwise majorant of the truncated integrand. -/
theorem pt_trunc {κ : Euc d → ℝ} {s K₀ Λ : ℝ} (hK : 0 ≤ K₀) (hΛ : 0 ≤ Λ)
    (hκ : ∀ z : Euc d, z ≠ 0 → |κ z| ≤ K₀ * ‖z‖ ^ (-s - 1))
    {a ς : Euc d → ℝ} (haΛ : ∀ x, |a x| ≤ Λ) (hς0 : ∀ x, 0 ≤ ς x) (hς1 : ∀ x, ς x ≤ 1)
    {c : Euc d} {R₀ : ℝ} (hsupp : ∀ x, ς x ≠ 0 → x ∈ Metric.ball c R₀) (w : Euc d → ℝ)
    {ε : ℝ} (hε : 0 < ε) (x y : Euc d) :
    |if ε < ‖x - y‖ then κ (x - y) * a y * w y * ς x * w x else 0| ≤
      K₀ * Λ * ε⁻¹ * (msf_I1 s (x - y) *
        (|(Metric.ball c (R₀ + 1)).indicator w x| * |(Metric.ball c (R₀ + 1)).indicator w y|)) +
      K₀ * Λ * (msf_I2 s (x - y) * (Metric.ball c R₀).indicator (fun x => |w x|) x * |w y|) := by
  have hhnn : ∀ x, 0 ≤ (Metric.ball c R₀).indicator (fun x => |w x|) x := fun x =>
    Set.indicator_nonneg (fun _ _ => abs_nonneg _) x
  have hI1 := msf_I1_nonneg (d := d) s (x - y)
  have hI2 := msf_I2_nonneg (d := d) s (x - y)
  have hεi : 0 ≤ ε⁻¹ := inv_nonneg.2 hε.le
  have hA : 0 ≤ K₀ * Λ * ε⁻¹ * (msf_I1 s (x - y) *
        (|(Metric.ball c (R₀ + 1)).indicator w x| * |(Metric.ball c (R₀ + 1)).indicator w y|)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hK hΛ) hεi)
      (mul_nonneg hI1 (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
  have hB : 0 ≤ K₀ * Λ * (msf_I2 s (x - y) * (Metric.ball c R₀).indicator (fun x => |w x|) x *
        |w y|) := mul_nonneg (mul_nonneg hK hΛ) (mul_nonneg (mul_nonneg hI2 (hhnn x)) (abs_nonneg _))
  by_cases hlt : ε < ‖x - y‖
  · rw [if_pos hlt]
    have hn : 0 < ‖x - y‖ := hε.trans hlt
    have hz : x - y ≠ 0 := norm_pos_iff.1 hn
    have hκz : |κ (x - y)| ≤ K₀ * (ε⁻¹ * msf_I1 s (x - y) + msf_I2 s (x - y)) :=
      (hκ _ hz).trans (mul_le_mul_of_nonneg_left (msf_trunc_majorant hε hlt) hK)
    have e : |κ (x - y) * a y * w y * ς x * w x| =
        |κ (x - y)| * |a y| * (|w y| * (ς x * |w x|)) := by
      simp only [abs_mul, abs_of_nonneg (hς0 x)]; ring
    rw [e]
    have hςw : ς x * |w x| ≤ (Metric.ball c R₀).indicator (fun x => |w x|) x := by
      by_cases hx : ς x = 0
      · rw [hx, zero_mul]; exact hhnn x
      · rw [Set.indicator_of_mem (hsupp x hx)]
        calc ς x * |w x| ≤ 1 * |w x| := mul_le_mul_of_nonneg_right (hς1 x) (abs_nonneg _)
          _ = _ := one_mul _
    have hςw0 : 0 ≤ ς x * |w x| := mul_nonneg (hς0 x) (abs_nonneg _)
    -- near part
    have hnear : msf_I1 s (x - y) * (|w y| * (ς x * |w x|)) ≤ msf_I1 s (x - y) *
        (|(Metric.ball c (R₀ + 1)).indicator w x| * |(Metric.ball c (R₀ + 1)).indicator w y|) := by
      by_cases h1 : ‖x - y‖ < 1
      · refine mul_le_mul_of_nonneg_left ?_ hI1
        by_cases hx : ς x = 0
        · rw [hx, zero_mul, mul_zero]; exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
        · have hx' := hsupp x hx
          rw [Set.indicator_of_mem (ball_mono_one hx'), Set.indicator_of_mem (near_mem hx' h1)]
          calc |w y| * (ς x * |w x|) ≤ |w y| * (1 * |w x|) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hς1 x) (abs_nonneg _))
                  (abs_nonneg _)
            _ = |w x| * |w y| := by ring
      · rw [msf_I1_ge (not_lt.1 h1), zero_mul, zero_mul]
    have hfar : msf_I2 s (x - y) * (|w y| * (ς x * |w x|)) ≤
        msf_I2 s (x - y) * (Metric.ball c R₀).indicator (fun x => |w x|) x * |w y| := by
      calc msf_I2 s (x - y) * (|w y| * (ς x * |w x|))
          ≤ msf_I2 s (x - y) * (|w y| * (Metric.ball c R₀).indicator (fun x => |w x|) x) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hςw (abs_nonneg _)) hI2
        _ = _ := by ring
    have hQ : 0 ≤ |w y| * (ς x * |w x|) := mul_nonneg (abs_nonneg _) hςw0
    have hKI : 0 ≤ K₀ * (ε⁻¹ * msf_I1 s (x - y) + msf_I2 s (x - y)) :=
      mul_nonneg hK (add_nonneg (mul_nonneg hεi hI1) hI2)
    calc |κ (x - y)| * |a y| * (|w y| * (ς x * |w x|))
        ≤ (K₀ * (ε⁻¹ * msf_I1 s (x - y) + msf_I2 s (x - y))) * Λ * (|w y| * (ς x * |w x|)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hκz (haΛ y) (abs_nonneg _) hKI) hQ
      _ = K₀ * Λ * ε⁻¹ * (msf_I1 s (x - y) * (|w y| * (ς x * |w x|))) +
          K₀ * Λ * (msf_I2 s (x - y) * (|w y| * (ς x * |w x|))) := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hnear (mul_nonneg (mul_nonneg hK hΛ) hεi))
          (mul_le_mul_of_nonneg_left hfar (mul_nonneg hK hΛ))
  · rw [if_neg hlt, abs_zero]; linarith

end HRS.MS.Sf8
