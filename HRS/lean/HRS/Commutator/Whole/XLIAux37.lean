import HRS.Commutator.Whole.XLIAux36

/-!
# X-LI part 37: the Fefferman–Stein weak type inequality for the dyadic maximal function
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma vol_closedBall_mul10 (x : 𝔼) {r : ℝ} (hr : 0 ≤ r) :
    ENNReal.ofReal ((2 * (5 * r)) ^ d) * volume (closedBall (0 : 𝔼) 1) =
      10 ^ d * volume (closedBall x r) := by
  rw [show 2 * (5 * r) = 10 * r by ring, cmxHLS_vol_closedBall x hr, ← mul_assoc, mul_pow,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
  simp

/-- **Fefferman–Stein weak type `(1,1)`**: `l · ∫_{M f > l} v ≲ ∫ f · M v` -/
lemma FS_weak (hd : 1 ≤ d) {f v : 𝔼 → ℝ≥0∞} (hf : Measurable f) (hv : Measurable v) (hfi : ∫⁻ y, f y ≠ ⊤)
    {l : ℝ≥0∞} (hl0 : l ≠ 0) (hlt : l ≠ ⊤) :
    l * ∫⁻ x in {x | l < cmxHLS_Md f x}, v x ≤ 10 ^ d * ∫⁻ x, f x * cmxHLS_Md v x := by
  obtain ⟨u, r, hucount, hrpos, hdisj, hsel, hnot, hcov⟩ := exists_balls hd hf hfi hl0 hlt
  have hcu : Countable u := hucount.to_subtype
  set S : Set 𝔼 := {x | l < cmxHLS_Md f x} with hS
  have hvm : ∀ (b : u), (volume (closedBall (b : 𝔼) (r b))) ≠ 0 := fun b =>
    cmxHLS_vol_closedBall_ne_zero _ (hrpos b b.2)
  have hvt : ∀ (b : u), (volume (closedBall (b : 𝔼) (r b))) ≠ ⊤ := fun b =>
    cmxHLS_vol_closedBall_ne_top _ _
  -- the estimate for a single ball
  have hone : ∀ b : u, l * ∫⁻ x in closedBall (b : 𝔼) (4 * r b), v x ≤
      10 ^ d * ∫⁻ x in closedBall (b : 𝔼) (r b), f x * cmxHLS_Md v x := by
    intro b
    set B : Set 𝔼 := closedBall (b : 𝔼) (r b) with hB
    set V : ℝ≥0∞ := ∫⁻ x in closedBall (b : 𝔼) (4 * r b), v x with hV
    have hrb := hrpos b b.2
    have hpt : ∀ x ∈ B, V ≤ 10 ^ d * volume B * cmxHLS_Md v x := by
      intro x hx
      have hsub : closedBall (b : 𝔼) (4 * r b) ⊆ closedBall x (5 * r b) := by
        intro y hy
        rw [mem_closedBall] at hy hx ⊢
        have := dist_triangle y (b : 𝔼) x
        have h2 := dist_comm (b : 𝔼) x
        linarith
      calc V ≤ ∫⁻ y in closedBall x (5 * r b), v y := lintegral_mono_set hsub
        _ ≤ ENNReal.ofReal ((2 * (5 * r b)) ^ d) * volume (closedBall (0 : 𝔼) 1) * cmxHLS_Md v x :=
            lintegral_ball_le v x (by positivity)
        _ = 10 ^ d * volume B * cmxHLS_Md v x := by
            rw [vol_closedBall_mul10 x hrb.le]
            have : volume (closedBall x (r b)) = volume B := by
              rw [hB, cmxHLS_vol_closedBall x hrb.le, cmxHLS_vol_closedBall _ hrb.le]
            rw [this]
    have hMv : Measurable (cmxHLS_Md v) := cmxHLS_Md_measurable hv
    have h1 : V * ∫⁻ x in B, f x ≤ (10 ^ d * volume B) * ∫⁻ x in B, f x * cmxHLS_Md v x := by
      calc V * ∫⁻ x in B, f x = ∫⁻ x in B, f x * V := by
            rw [lintegral_mul_const'' _ hf.aemeasurable, mul_comm]
        _ ≤ ∫⁻ x in B, f x * (10 ^ d * volume B * cmxHLS_Md v x) :=
            setLIntegral_mono' measurableSet_closedBall fun x hx => mul_le_mul_right (hpt x hx) _
        _ = (10 ^ d * volume B) * ∫⁻ x in B, f x * cmxHLS_Md v x := by
            have hm : Measurable (fun x => f x * cmxHLS_Md v x) := hf.mul hMv
            rw [← lintegral_const_mul _ hm]
            refine lintegral_congr fun x => ?_
            ring
    have h2 : (volume B) * (l * V) ≤ (volume B) * (10 ^ d * ∫⁻ x in B, f x * cmxHLS_Md v x) := by
      calc volume B * (l * V) = V * (l * volume B) := by ring
        _ ≤ V * ∫⁻ x in B, f x := mul_le_mul_right (hsel b b.2) _
        _ ≤ (10 ^ d * volume B) * ∫⁻ x in B, f x * cmxHLS_Md v x := h1
        _ = _ := by ring
    exact (ENNReal.mul_le_mul_iff_right (hvm b) (hvt b)).1 h2
  have hBdisj : Pairwise (Function.onFun Disjoint fun i : u => closedBall (i : 𝔼) (r i)) :=
    fun i j hij => hdisj i.2 j.2 (fun h => hij (Subtype.ext h))
  have hcov' : S ⊆ ⋃ b : u, closedBall (b : 𝔼) (4 * r b) := by
    intro x hx
    obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.1 (hcov hx)
    exact mem_iUnion.2 ⟨⟨b, hb⟩, hxb⟩
  calc l * ∫⁻ x in S, v x
      ≤ l * ∫⁻ x in ⋃ b : u, closedBall (b : 𝔼) (4 * r b), v x :=
        mul_le_mul_right (lintegral_mono_set hcov') _
    _ ≤ l * ∑' b : u, ∫⁻ x in closedBall (b : 𝔼) (4 * r b), v x :=
        mul_le_mul_right (lintegral_iUnion_le _ _) _
    _ = ∑' b : u, l * ∫⁻ x in closedBall (b : 𝔼) (4 * r b), v x := ENNReal.tsum_mul_left.symm
    _ ≤ ∑' b : u, 10 ^ d * ∫⁻ x in closedBall (b : 𝔼) (r b), f x * cmxHLS_Md v x :=
        ENNReal.tsum_le_tsum hone
    _ = 10 ^ d * ∫⁻ x in ⋃ b : u, closedBall (b : 𝔼) (r b), f x * cmxHLS_Md v x := by
        rw [lintegral_iUnion (fun i => measurableSet_closedBall) hBdisj, ENNReal.tsum_mul_left]
    _ ≤ 10 ^ d * ∫⁻ x, f x * cmxHLS_Md v x := mul_le_mul_right (setLIntegral_le_lintegral _ _) _

/-- **Fefferman–Stein for indicators**: `∫ (M 1_E)² v ≲ ∫_E M v` -/
lemma FS_sq (hd : 1 ≤ d) {E : Set 𝔼} (hE : MeasurableSet E) (hEfin : volume E ≠ ⊤)
    {v : 𝔼 → ℝ≥0∞} (hv : Measurable v) :
    ∫⁻ x, cmxHLS_Md (E.indicator (fun _ => (1 : ℝ≥0∞))) x ^ 2 * v x ≤
      2 * 10 ^ d * ∫⁻ x in E, cmxHLS_Md v x := by
  set f : 𝔼 → ℝ≥0∞ := E.indicator (fun _ => (1 : ℝ≥0∞)) with hf
  have hfm : Measurable f := measurable_const.indicator hE
  have hfi : ∫⁻ y, f y ≠ ⊤ := by
    rw [hf, lintegral_indicator_const hE, one_mul]; exact hEfin
  have hMf : Measurable (cmxHLS_Md f) := cmxHLS_Md_measurable hfm
  have hMfle : ∀ x, cmxHLS_Md f x ≤ 1 := fun x =>
    Md_le_of_le (fun y => by
      by_cases hy : y ∈ E
      · simp [hf, hy]
      · simp [hf, hy]) x
  set X : ℝ≥0∞ := ∫⁻ x in E, cmxHLS_Md v x with hX
  by_cases hXt : X = ⊤
  · rw [hXt, ENNReal.mul_top (by simp)]; exact le_top
  have hFS : ∀ t : ℝ, 0 < t → t < 1 → ∫⁻ x in {x | ENNReal.ofReal t < cmxHLS_Md f x ^ 2}, v x ≤
      10 ^ d * X * ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) := by
    intro t ht0 ht1
    set s : ℝ := Real.sqrt t with hs
    have hs0 : 0 < s := Real.sqrt_pos.2 ht0
    have hst : s ^ 2 = t := Real.sq_sqrt ht0.le
    have hsub : {x | ENNReal.ofReal t < cmxHLS_Md f x ^ 2} ⊆ {x | ENNReal.ofReal s < cmxHLS_Md f x} := by
      intro x hx
      have hx' : ENNReal.ofReal t < cmxHLS_Md f x ^ 2 := hx
      show ENNReal.ofReal s < _
      by_contra hcon
      have h1 := not_lt.1 hcon
      have h2 : cmxHLS_Md f x ^ 2 ≤ ENNReal.ofReal s ^ 2 := by gcongr
      rw [← ENNReal.ofReal_pow hs0.le, hst] at h2
      exact absurd hx' (not_lt.2 h2)
    have hl0 : ENNReal.ofReal s ≠ 0 := (ENNReal.ofReal_pos.2 hs0).ne'
    have hw := FS_weak hd hfm hv hfi hl0 ENNReal.ofReal_ne_top
    have hfM : ∫⁻ x, f x * cmxHLS_Md v x = X := by
      rw [hf, hX, ← lintegral_indicator hE]
      refine lintegral_congr fun x => ?_
      by_cases hx : x ∈ E <;> simp [hx]
    rw [hfM] at hw
    have hmain : ENNReal.ofReal s * ∫⁻ x in {x | ENNReal.ofReal t < cmxHLS_Md f x ^ 2}, v x ≤
        10 ^ d * X :=
      (mul_le_mul_right (lintegral_mono_set hsub) _).trans hw
    have hinv : ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) * ENNReal.ofReal s = 1 := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht0.le _)]
      have : t ^ (-(1 / 2 : ℝ)) * s = 1 := by
        rw [hs, Real.sqrt_eq_rpow, ← Real.rpow_add ht0]
        norm_num
      rw [this]; simp
    calc ∫⁻ x in {x | ENNReal.ofReal t < cmxHLS_Md f x ^ 2}, v x
        = (ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) * ENNReal.ofReal s) *
            ∫⁻ x in {x | ENNReal.ofReal t < cmxHLS_Md f x ^ 2}, v x := by rw [hinv, one_mul]
      _ = ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) * (ENNReal.ofReal s *
            ∫⁻ x in {x | ENNReal.ofReal t < cmxHLS_Md f x ^ 2}, v x) := by ring
      _ ≤ ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) * (10 ^ d * X) := mul_le_mul_right hmain _
      _ = _ := by ring
  have hlayer := lintegral_mul_layer (f := v) (G := fun x => cmxHLS_Md f x ^ 2) hv
    (hMf.pow_const 2)
  calc ∫⁻ x, cmxHLS_Md f x ^ 2 * v x = ∫⁻ x, v x * cmxHLS_Md f x ^ 2 :=
        lintegral_congr fun x => mul_comm _ _
    _ = ∫⁻ t in Set.Ioi (0 : ℝ), ∫⁻ x in {x | ENNReal.ofReal t < cmxHLS_Md f x ^ 2}, v x := hlayer
    _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ), (Set.Iio (1 : ℝ)).indicator
          (fun t => 10 ^ d * X * ENNReal.ofReal (t ^ (-(1 / 2 : ℝ)))) t := by
        refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
        have ht0 : 0 < t := ht
        by_cases ht1 : t < 1
        · rw [Set.indicator_of_mem (show t ∈ Set.Iio (1 : ℝ) from ht1)]
          exact hFS t ht0 ht1
        · rw [Set.indicator_of_notMem (show t ∉ Set.Iio (1 : ℝ) from ht1)]
          have h1 : {x | ENNReal.ofReal t < cmxHLS_Md f x ^ 2} = ∅ := by
            ext x
            simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
            calc cmxHLS_Md f x ^ 2 ≤ 1 ^ 2 := by gcongr; exact hMfle x
              _ = 1 := by norm_num
              _ ≤ ENNReal.ofReal t := by
                  rw [← ENNReal.ofReal_one]
                  exact ENNReal.ofReal_le_ofReal (not_lt.1 ht1)
          rw [h1]; simp
    _ = 10 ^ d * X * ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) := by
        rw [setLIntegral_indicator measurableSet_Iio, Set.Iio_inter_Ioi,
          lintegral_const_mul' _ _ (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) hXt)]
    _ = 2 * 10 ^ d * X := by
        rw [cmxHLS_int_rpow (by norm_num) (by norm_num)]
        have : (1 : ℝ) ^ (-(1 / 2 : ℝ) + 1) / (-(1 / 2 : ℝ) + 1) = 2 := by norm_num
        rw [this]
        simp only [ENNReal.ofReal_ofNat]
        ring

end HRS.Commutator.Whole.XLI
