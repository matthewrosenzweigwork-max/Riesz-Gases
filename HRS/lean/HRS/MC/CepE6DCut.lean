import Mathlib

/-!
# Packet CEPE6D, part 1: the cutoff functional `g_ε` and its calculus

`ζ(y) = 1 - smoothTransition(4y-1)` (`ζ = 1` on `(-∞,1/4]`, `ζ = 0` on `[1/2,∞)`, `0 ≤ ζ ≤ 1`, smooth, `|ζ'| ≤ Cz`),
`h_ε(x) = ∫_0^x ζ(y/ε) dy`, `χ_ε(d) = h_ε(d) + h_ε(1-d)`, `g_ε(z) = ∑_{k<l} χ_ε(z_l - z_k)` on all of `ℝ^N`.
-/

open Set Filter Topology
open scoped RealInnerProductSpace ContDiff

noncomputable section

namespace HRS.MC.CepE6D

/-- Chamber coordinates `ℝ^N` (definitionally the `Ch N` of the Cépa spec). -/
abbrev Ch6D (N : ℕ) := EuclideanSpace ℝ (Fin N)

/-- The cutoff profile `ζ`. -/
def zeta (y : ℝ) : ℝ := 1 - Real.smoothTransition (4 * y - 1)

theorem zeta_contDiff : ContDiff ℝ ∞ zeta := by
  unfold zeta
  exact contDiff_const.sub ((Real.smoothTransition.contDiff (n := ⊤)).comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const))

theorem zeta_eq_one {y : ℝ} (h : y ≤ 1 / 4) : zeta y = 1 := by
  unfold zeta
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]; ring

theorem zeta_eq_zero {y : ℝ} (h : 1 / 2 ≤ y) : zeta y = 0 := by
  unfold zeta
  rw [Real.smoothTransition.one_of_one_le (by linarith)]; ring

theorem zeta_nonneg (y : ℝ) : 0 ≤ zeta y := by
  unfold zeta; linarith [Real.smoothTransition.le_one (4 * y - 1)]

theorem zeta_le_one (y : ℝ) : zeta y ≤ 1 := by
  unfold zeta; linarith [Real.smoothTransition.nonneg (4 * y - 1)]

theorem zeta_hasDerivAt (y : ℝ) : HasDerivAt zeta (deriv zeta y) y :=
  ((zeta_contDiff.differentiable (by simp)) y).hasDerivAt

theorem deriv_zeta_contDiff : ContDiff ℝ ∞ (deriv zeta) :=
  (contDiff_infty_iff_deriv.1 zeta_contDiff).2

theorem deriv_zeta_eq_zero_of_le {y : ℝ} (h : y < 1 / 4) : deriv zeta y = 0 := by
  have : zeta =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
    filter_upwards [Iio_mem_nhds h] with x hx using zeta_eq_one (le_of_lt hx)
  rw [this.deriv_eq]; simp

theorem deriv_zeta_eq_zero_of_ge {y : ℝ} (h : 1 / 2 < y) : deriv zeta y = 0 := by
  have : zeta =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds h] with x hx using zeta_eq_zero (le_of_lt hx)
  rw [this.deriv_eq]; simp

theorem exists_deriv_zeta_bound : ∃ C : ℝ, 1 ≤ C ∧ ∀ y, |deriv zeta y| ≤ C := by
  have hc : Continuous (deriv zeta) := deriv_zeta_contDiff.continuous
  have hcs : HasCompactSupport (deriv zeta) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (1 / 4 : ℝ)) (b := 1 / 2)) ?_
    intro y hy
    simp only [mem_Icc, not_and_or, not_le] at hy
    rcases hy with hy | hy
    · exact deriv_zeta_eq_zero_of_le hy
    · exact deriv_zeta_eq_zero_of_ge hy
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
  refine ⟨max 1 C, le_max_left _ _, fun y => ?_⟩
  exact (by simpa using hC y : |deriv zeta y| ≤ C).trans (le_max_right _ _)

/-- The Lipschitz constant of `ζ` (`|ζ'| ≤ Cz`, `1 ≤ Cz`); the sup norm of `ζ'` is `8`, we do not need its value. -/
def Cz : ℝ := Classical.choose exists_deriv_zeta_bound

theorem one_le_Cz : 1 ≤ Cz := (Classical.choose_spec exists_deriv_zeta_bound).1

theorem abs_deriv_zeta_le (y : ℝ) : |deriv zeta y| ≤ Cz :=
  (Classical.choose_spec exists_deriv_zeta_bound).2 y


theorem deriv_zeta_eq_zero_of_le' {y : ℝ} (h : y ≤ 1 / 4) : deriv zeta y = 0 := by
  have hc : Continuous (deriv zeta) := deriv_zeta_contDiff.continuous
  have hsub : Iic (1 / 4 : ℝ) ⊆ closure (Iio (1 / 4 : ℝ)) := by rw [closure_Iio]
  exact closure_minimal (fun y hy => deriv_zeta_eq_zero_of_le hy) (isClosed_eq hc continuous_const)
    (hsub h)

theorem deriv_zeta_eq_zero_of_ge' {y : ℝ} (h : 1 / 2 ≤ y) : deriv zeta y = 0 := by
  have hc : Continuous (deriv zeta) := deriv_zeta_contDiff.continuous
  have hsub : Ici (1 / 2 : ℝ) ⊆ closure (Ioi (1 / 2 : ℝ)) := by rw [closure_Ioi]
  exact closure_minimal (fun y hy => deriv_zeta_eq_zero_of_ge hy) (isClosed_eq hc continuous_const)
    (hsub h)

/-! ### The scalar profile `h_ε`, `χ_ε`, `χ_ε'`, `χ_ε''` -/

/-- `h_ε(x) = ∫_0^x ζ(y/ε) dy`. -/
def hh (ε x : ℝ) : ℝ := ∫ y in (0 : ℝ)..x, zeta (y / ε)
/-- `χ_ε(d) = h_ε(d) + h_ε(1-d)`. -/
def chi (ε d : ℝ) : ℝ := hh ε d + hh ε (1 - d)
/-- `χ_ε'(d) = ζ(d/ε) - ζ((1-d)/ε)`. -/
def chi1 (ε d : ℝ) : ℝ := zeta (d / ε) - zeta ((1 - d) / ε)
/-- `χ_ε''(d) = ε⁻¹ (ζ'(d/ε) + ζ'((1-d)/ε))`. -/
def chi2 (ε d : ℝ) : ℝ := ε⁻¹ * (deriv zeta (d / ε) + deriv zeta ((1 - d) / ε))

theorem hh_hasDerivAt (ε x : ℝ) : HasDerivAt (hh ε) (zeta (x / ε)) x :=
  ((zeta_contDiff.continuous.comp (continuous_id.div_const ε)).integral_hasStrictDerivAt 0 x).hasDerivAt

theorem chi_hasDerivAt (ε d : ℝ) : HasDerivAt (chi ε) (chi1 ε d) d := by
  have h1 := hh_hasDerivAt ε d
  have h2 := (hh_hasDerivAt ε (1 - d)).comp d ((hasDerivAt_id d).const_sub 1)
  have h3 := h1.add h2
  refine HasDerivAt.congr_deriv (f := chi ε) h3 ?_
  simp [chi1]; ring

theorem chi1_hasDerivAt (ε d : ℝ) : HasDerivAt (chi1 ε) (chi2 ε d) d := by
  have h1 := (zeta_hasDerivAt (d / ε)).comp d ((hasDerivAt_id d).div_const ε)
  have h2 := (zeta_hasDerivAt ((1 - d) / ε)).comp d (((hasDerivAt_id d).const_sub 1).div_const ε)
  have h3 := h1.sub h2
  refine HasDerivAt.congr_deriv (f := chi1 ε) h3 ?_
  simp only [chi2]; ring

theorem chi1_contDiff (ε : ℝ) : ContDiff ℝ ∞ (chi1 ε) := by
  unfold chi1
  exact (zeta_contDiff.comp (contDiff_id.div_const ε)).sub
    (zeta_contDiff.comp ((contDiff_const.sub contDiff_id).div_const ε))

theorem chi_contDiff (ε : ℝ) : ContDiff ℝ ∞ (chi ε) := by
  refine contDiff_infty_iff_deriv.2 ⟨fun d => (chi_hasDerivAt ε d).differentiableAt, ?_⟩
  have : deriv (chi ε) = chi1 ε := funext fun d => (chi_hasDerivAt ε d).deriv
  rw [this]; exact chi1_contDiff ε

theorem chi2_contDiff (ε : ℝ) : ContDiff ℝ ∞ (chi2 ε) := by
  unfold chi2
  exact contDiff_const.mul ((deriv_zeta_contDiff.comp (contDiff_id.div_const ε)).add
    (deriv_zeta_contDiff.comp ((contDiff_const.sub contDiff_id).div_const ε)))

theorem abs_chi1_le (ε d : ℝ) : |chi1 ε d| ≤ 1 := by
  unfold chi1
  rw [abs_le]; constructor <;> linarith [zeta_nonneg (d / ε), zeta_le_one (d / ε),
    zeta_nonneg ((1 - d) / ε), zeta_le_one ((1 - d) / ε)]

theorem chi1_eq_zero {ε d : ℝ} (hε : 0 < ε) (h1 : ε / 2 ≤ d) (h2 : ε / 2 ≤ 1 - d) : chi1 ε d = 0 := by
  unfold chi1
  rw [zeta_eq_zero (by rw [le_div_iff₀ hε]; linarith), zeta_eq_zero (by rw [le_div_iff₀ hε]; linarith)]
  ring

theorem chi1_eq_one {ε d : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 8) (hd : d ≤ ε / 4) : chi1 ε d = 1 := by
  unfold chi1
  rw [zeta_eq_one (by rw [div_le_iff₀ hε]; linarith), zeta_eq_zero (by rw [le_div_iff₀ hε]; linarith)]
  ring

theorem chi1_one_sub (ε d : ℝ) : chi1 ε (1 - d) = - chi1 ε d := by
  unfold chi1; simp only [sub_sub_cancel]; ring

theorem chi1_eq_neg_one {ε d : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 8) (hd : 1 - ε / 4 ≤ d) :
    chi1 ε d = -1 := by
  have := chi1_eq_one hε hε1 (d := 1 - d) (by linarith)
  rw [chi1_one_sub] at this; linarith

theorem chi2_eq_zero {ε d : ℝ} (hε : 0 < ε) (h1 : ε / 2 ≤ d) (h2 : ε / 2 ≤ 1 - d) : chi2 ε d = 0 := by
  unfold chi2
  rw [deriv_zeta_eq_zero_of_ge' (by rw [le_div_iff₀ hε]; linarith),
    deriv_zeta_eq_zero_of_ge' (by rw [le_div_iff₀ hε]; linarith)]
  simp

theorem abs_chi2_le {ε d : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 8) : |chi2 ε d| ≤ Cz / ε := by
  have hz : ∀ y : ℝ, 0 ≤ |deriv zeta y| := fun y => abs_nonneg _
  unfold chi2
  rw [abs_mul, abs_of_pos (inv_pos.2 hε), inv_mul_eq_div]
  refine div_le_div_of_nonneg_right ?_ hε.le
  by_cases h : d / ε ≤ 1 / 4
  · -- then (1-d)/ε ≥ 1/2
    have : 1 / 2 ≤ (1 - d) / ε := by
      rw [le_div_iff₀ hε]; rw [div_le_iff₀ hε] at h; linarith
    rw [deriv_zeta_eq_zero_of_ge' this, add_zero]; exact abs_deriv_zeta_le _
  · replace h := not_le.1 h
    by_cases h' : d / ε ≤ 1 / 2
    · have : 1 / 2 ≤ (1 - d) / ε := by
        rw [le_div_iff₀ hε]; rw [div_le_iff₀ hε] at h'; linarith
      rw [deriv_zeta_eq_zero_of_ge' this, add_zero]; exact abs_deriv_zeta_le _
    · replace h' := not_le.1 h'
      rw [deriv_zeta_eq_zero_of_ge' h'.le, zero_add]; exact abs_deriv_zeta_le _


/-- Combined form of the support/size bound: `|χ_ε''(d)| ≤ (Cz/ε) 1_{min(d,1-d) < ε/2}`. -/
theorem abs_chi2_le_indicator {ε : ℝ} (d : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 8) :
    |chi2 ε d| ≤ if min d (1 - d) < ε / 2 then Cz / ε else 0 := by
  split_ifs with h
  · exact abs_chi2_le hε hε1
  · rw [not_lt, le_min_iff] at h
    rw [chi2_eq_zero hε h.1 h.2]; simp

theorem abs_chi1_le_indicator {ε : ℝ} (d : ℝ) (hε : 0 < ε) :
    |chi1 ε d| ≤ if min d (1 - d) < ε / 2 then 1 else 0 := by
  split_ifs with h
  · exact abs_chi1_le ε d
  · rw [not_lt, le_min_iff] at h
    rw [chi1_eq_zero hε h.1 h.2]; simp


theorem hh_nonneg {ε x : ℝ} (hx : 0 ≤ x) : 0 ≤ hh ε x :=
  intervalIntegral.integral_nonneg hx fun y _ => zeta_nonneg _

theorem hh_le {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : 0 ≤ x) : hh ε x ≤ ε / 2 := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun y => zeta (y / ε)) MeasureTheory.volume a b :=
    fun a b => (zeta_contDiff.continuous.comp (continuous_id.div_const ε)).intervalIntegrable a b
  by_cases hxe : x ≤ ε / 2
  · calc hh ε x = ∫ y in (0 : ℝ)..x, zeta (y / ε) := rfl
      _ ≤ ∫ y in (0 : ℝ)..x, (1 : ℝ) :=
        intervalIntegral.integral_mono_on hx (hint 0 x) intervalIntegrable_const
          fun y _ => zeta_le_one _
      _ = x := by simp
      _ ≤ ε / 2 := hxe
  · replace hxe := not_le.1 hxe
    have h1 : hh ε x = hh ε (ε / 2) + ∫ y in (ε / 2)..x, zeta (y / ε) := by
      unfold hh
      rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
    have h2 : ∫ y in (ε / 2)..x, zeta (y / ε) = 0 := by
      have : ∫ y in (ε / 2)..x, zeta (y / ε) = ∫ y in (ε / 2)..x, (0 : ℝ) := by
        refine intervalIntegral.integral_congr fun y hy => ?_
        rw [uIcc_of_le hxe.le] at hy
        exact zeta_eq_zero (by rw [le_div_iff₀ hε]; linarith [hy.1])
      rw [this]; simp
    rw [h1, h2, add_zero]
    calc hh ε (ε / 2) = ∫ y in (0 : ℝ)..(ε / 2), zeta (y / ε) := rfl
      _ ≤ ∫ y in (0 : ℝ)..(ε / 2), (1 : ℝ) :=
        intervalIntegral.integral_mono_on (by linarith) (hint 0 _) intervalIntegrable_const
          fun y _ => zeta_le_one _
      _ = ε / 2 := by simp

theorem chi_nonneg {ε d : ℝ} (h0 : 0 ≤ d) (h1 : d ≤ 1) : 0 ≤ chi ε d :=
  add_nonneg (hh_nonneg h0) (hh_nonneg (by linarith))

theorem chi_le {ε d : ℝ} (hε : 0 < ε) (h0 : 0 ≤ d) (h1 : d ≤ 1) : chi ε d ≤ ε := by
  have := hh_le hε h0
  have := hh_le hε (show 0 ≤ 1 - d by linarith)
  unfold chi; linarith

end HRS.MC.CepE6D
