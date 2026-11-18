import HRS.Whole.Q34Aux2
import HRS.Energy.WeakReference

/-!
# HRS.MS.WrRowAux1 -- Euclidean level-set integrals of `W_s = 1 + rieszWeight s` (WR-3, part 1)

Packet WR-3 of `docs/SUPP_FOUND_PACKETS.md` (Track D).  Whole-space port of the torus level-set
estimates `lev1`, `lev2_base`, `lev2a/b/c`, `kernel_levels_real` of `HRS/Energy/WeakReference.lean`
(lines 2345-3000, 3322-3500, 4803-4840).  The torus file is not edited.

Adaptations (all forced by `ℝ^d` having infinite volume, none changes the mathematical content):
* the torus integrals `∫_{𝕋^d}` become `∫_{ℝ^d}` for the first level-set integral
  `∫ (W_s - L)_+ ≤ C L^{1 - d/σ}` (finite only for `L` above `1`; we state it for `L ≥ 2`), and
  `∫_{B(0,1)}` for the second one `∫_{B(0,1)} min(W_s, L)² ≤ C ψ₂(L)` (`L ≥ 1`); the far zone `|z| ≥ 1`
  is handled in `WrRowAux2` by the pointwise bound `W_s ≤ 1 + B₀` there;
* the sup-norm polar coordinates of the torus box are replaced by Euclidean polar coordinates
  (`Q34.lintegral_radial_set`, `Q34.lintegral_ball_rpow`, `Q34.volume_ball_eq`);
* the torus constant `cstar` is `0` (the weight is `W_s = 1 + rieszWeight s`, `rieszWeight ≥ 0`);
* `σ = sigmaOf d s` (`σ = s` for `s > 0`, `σ = d/4` for `s = 0`) and `ψ₂ = psi2 d s` are the torus
  definitions of `HRS.WeakRef` (imported, not redefined).

No lower bound on a density is used anywhere.  Helper lemmas carry the prefix `wr3_`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Set Metric
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

variable {d : ℕ}

/-! ### The weight `rieszWeight` and its power envelope -/

theorem wr3_rieszWeight_nonneg (s : ℝ) (z : Euc d) : 0 ≤ HRS.Whole.rieszWeight s z := by
  unfold HRS.Whole.rieszWeight
  split_ifs
  · exact le_max_right _ _
  · exact Real.rpow_nonneg (norm_nonneg _) _

theorem wr3_rieszWeight_zero (s : ℝ) : HRS.Whole.rieszWeight s (0 : Euc d) = 0 := by
  unfold HRS.Whole.rieszWeight
  split_ifs with h
  · simp
  · simp only [norm_zero]
    exact Real.zero_rpow (neg_ne_zero.2 h)

/-- Power envelope of the weight: `rieszWeight s z ≤ (1 + 4/d) |z|^{-σ}`, `σ = sigmaOf d s`
(`σ = s` for `s > 0`, `σ = d/4` for `s = 0`, where `-log t ≤ t^{-σ}/σ`). -/
theorem wr3_rieszWeight_le (hd : 1 ≤ d) {s : ℝ} (z : Euc d) :
    HRS.Whole.rieszWeight s z ≤ (1 + 4 / (d : ℝ)) * ‖z‖ ^ (-(HRS.WeakRef.sigmaOf d s)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hB0 : (1 : ℝ) ≤ 1 + 4 / (d : ℝ) := by
    have : 0 ≤ 4 / (d : ℝ) := by positivity
    linarith
  have hRnn : 0 ≤ (1 + 4 / (d : ℝ)) * ‖z‖ ^ (-(HRS.WeakRef.sigmaOf d s)) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)
  by_cases hz : z = 0
  · subst hz
    rw [wr3_rieszWeight_zero]
    simpa using hRnn
  · have ht : 0 < ‖z‖ := norm_pos_iff.2 hz
    by_cases hs : s = 0
    · subst hs
      have hσ : HRS.WeakRef.sigmaOf d 0 = (d : ℝ) / 4 := by simp [HRS.WeakRef.sigmaOf]
      rw [hσ]
      unfold HRS.Whole.rieszWeight
      rw [if_pos rfl]
      refine max_le ?_ (by rw [hσ] at hRnn; exact hRnn)
      have h2 : -Real.log ‖z‖ ≤ ‖z‖ ^ (-((d : ℝ) / 4)) / ((d : ℝ) / 4) := by
        have := Real.log_le_rpow_div (inv_nonneg.2 ht.le) (show 0 < (d : ℝ) / 4 by positivity)
        rw [Real.log_inv, Real.inv_rpow ht.le] at this
        rwa [← Real.rpow_neg ht.le] at this
      have h3 : ‖z‖ ^ (-((d : ℝ) / 4)) / ((d : ℝ) / 4) = 4 / d * ‖z‖ ^ (-((d : ℝ) / 4)) := by
        field_simp
      have h5 : 0 ≤ ‖z‖ ^ (-((d : ℝ) / 4)) := Real.rpow_nonneg ht.le _
      have h6 : 0 ≤ 4 / (d : ℝ) * ‖z‖ ^ (-((d : ℝ) / 4)) := by positivity
      rw [h3] at h2
      nlinarith
    · have hσ : HRS.WeakRef.sigmaOf d s = s := by simp [HRS.WeakRef.sigmaOf, hs]
      rw [hσ]
      unfold HRS.Whole.rieszWeight
      rw [if_neg hs]
      exact le_mul_of_one_le_left (Real.rpow_nonneg ht.le _) hB0

/-! ### Radial integrals -/

/-- Annulus integral of a power of the radius. -/
theorem wr3_lintegral_annulus (hd : 1 ≤ d) {a r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    ∫⁻ z in {z : Euc d | ‖z‖ ∈ Ico r R}, ENNReal.ofReal (‖z‖ ^ (-a)) =
      ENNReal.ofReal (sphereArea d * ∫ t in r..R, t ^ ((d : ℝ) - 1 - a)) := by
  rw [HRS.Whole.Q34.lintegral_radial_set hd (Ico r R) measurableSet_Ico
    (fun t => ENNReal.ofReal (t ^ (-a))) (by fun_prop)]
  have h1 : Ioi (0 : ℝ) ∩ Ico r R = Ico r R := by
    ext t; simp only [mem_inter_iff, mem_Ioi, mem_Ico]
    exact ⟨fun h => h.2, fun h => ⟨hr.trans_le h.1, h⟩⟩
  rw [h1]
  have hsA := HRS.Whole.Q34.sphereArea_nonneg hd
  have hcont : ContinuousOn (fun t : ℝ => t ^ ((d : ℝ) - 1 - a)) (Icc r R) :=
    ContinuousOn.rpow_const continuousOn_id fun t ht => Or.inl (ne_of_gt (hr.trans_le ht.1))
  have hint : IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - 1 - a)) (Ioc r R) :=
    hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have h2 : ∫⁻ t in Ico r R, ENNReal.ofReal (t ^ (d - 1)) * ENNReal.ofReal (t ^ (-a)) =
      ∫⁻ t in Ioc r R, ENNReal.ofReal (t ^ ((d : ℝ) - 1 - a)) := by
    rw [← setLIntegral_congr Ico_ae_eq_Ioc]
    refine setLIntegral_congr_fun measurableSet_Ico fun t ht => ?_
    have ht0 : 0 < t := hr.trans_le ht.1
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub hd]; simp
    rw [← Real.rpow_natCast, this, ← Real.rpow_add ht0]
    congr 1
  rw [h2, ← ofReal_integral_eq_lintegral_ofReal hint, ENNReal.ofReal_mul hsA,
    intervalIntegral.integral_of_le hrR]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact Real.rpow_nonneg (hr.trans ht.1).le _

/-! ### First level-set integral -/

/-- Core of the first level-set integral: `∫_{ℝ^d} (B|z|^{-σ} - L)_+ ≤ B ω_d/(d-σ) (B/L)^{d/σ-1}`. -/
theorem wr3_lev1_base (hd : 1 ≤ d) {σ B L : ℝ} (hσ0 : 0 < σ) (hσd : σ < d) (hB : 0 < B)
    (hL : 0 < L) :
    ∫⁻ z : Euc d, ENNReal.ofReal (max (B * ‖z‖ ^ (-σ) - L) 0) ≤
      ENNReal.ofReal (B * (sphereArea d / ((d : ℝ) - σ)) * (B / L) ^ ((d : ℝ) / σ - 1)) := by
  have hdσ : 0 < (d : ℝ) - σ := by linarith
  have hBL : 0 < B / L := div_pos hB hL
  set r : ℝ := (B / L) ^ (1 / σ) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hBL _
  have hrσ : r ^ (-σ) = L / B := by
    rw [hr, ← Real.rpow_mul hBL.le]
    have : 1 / σ * (-σ) = -1 := by field_simp
    rw [this, Real.rpow_neg_one, inv_div]
  have hpt : ∀ z : Euc d, ENNReal.ofReal (max (B * ‖z‖ ^ (-σ) - L) 0) ≤
      (ball (0 : Euc d) r).indicator
        (fun z => ENNReal.ofReal B * ENNReal.ofReal (‖z‖ ^ (-σ))) z := by
    intro z
    by_cases hz : z ∈ ball (0 : Euc d) r
    · rw [indicator_of_mem hz, ← ENNReal.ofReal_mul hB.le]
      refine ENNReal.ofReal_le_ofReal (max_le ?_
        (mul_nonneg hB.le (Real.rpow_nonneg (norm_nonneg _) _)))
      linarith
    · rw [indicator_of_notMem hz]
      have hz' : r ≤ ‖z‖ := by
        have : ¬ ‖z‖ < r := by simpa [mem_ball_zero_iff] using hz
        exact not_lt.1 this
      have h1 : ‖z‖ ^ (-σ) ≤ r ^ (-σ) := Real.rpow_le_rpow_of_nonpos hr0 hz' (by linarith)
      rw [hrσ] at h1
      have h2 : B * ‖z‖ ^ (-σ) ≤ L := by
        calc B * ‖z‖ ^ (-σ) ≤ B * (L / B) := mul_le_mul_of_nonneg_left h1 hB.le
          _ = L := by field_simp
      exact le_of_eq (ENNReal.ofReal_eq_zero.2 (max_le (by linarith) le_rfl))
  calc ∫⁻ z : Euc d, ENNReal.ofReal (max (B * ‖z‖ ^ (-σ) - L) 0)
      ≤ ∫⁻ z : Euc d, (ball (0 : Euc d) r).indicator
          (fun z => ENNReal.ofReal B * ENNReal.ofReal (‖z‖ ^ (-σ))) z := lintegral_mono hpt
    _ = ∫⁻ z in ball (0 : Euc d) r, ENNReal.ofReal B * ENNReal.ofReal (‖z‖ ^ (-σ)) :=
        lintegral_indicator measurableSet_ball _
    _ = ENNReal.ofReal B * ∫⁻ z in ball (0 : Euc d) r, ENNReal.ofReal (‖z‖ ^ (-σ)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (B * (sphereArea d * (r ^ ((d : ℝ) - σ) / ((d : ℝ) - σ)))) := by
        rw [HRS.Whole.Q34.lintegral_ball_rpow hd hr0 hσd, ← ENNReal.ofReal_mul hB.le]
    _ = _ := by
        congr 1
        have hrp : r ^ ((d : ℝ) - σ) = (B / L) ^ ((d : ℝ) / σ - 1) := by
          rw [hr, ← Real.rpow_mul hBL.le]
          congr 1
          field_simp
        rw [hrp]; ring

/-- First level-set integral `∫_{ℝ^d} (w - L)_+ ≤ C L^{1-d/σ}` for `L ≥ 2`, for every `w` below the
envelope `1 + B|z|^{-σ}`; the constant depends only on `d, σ, B`. -/
theorem wr3_lev1 (hd : 1 ≤ d) {σ B : ℝ} (hσ0 : 0 < σ) (hσd : σ < d) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : Euc d → ℝ, (∀ z, w z ≤ 1 + B * ‖z‖ ^ (-σ)) →
      ∀ L : ℝ, 2 ≤ L →
        ∫⁻ z : Euc d, ENNReal.ofReal (max (w z - L) 0)
          ≤ ENNReal.ofReal (C * L ^ (1 - (d : ℝ) / σ)) := by
  have hB0 : 0 < B := by linarith
  have hdσ : 0 < (d : ℝ) - σ := by linarith
  have hsA := HRS.Whole.Q34.sphereArea_nonneg hd
  refine ⟨B * (sphereArea d / ((d : ℝ) - σ)) * (2 * B) ^ ((d : ℝ) / σ - 1), by positivity,
    fun w hw L hL => ?_⟩
  have hL0 : 0 < L := by linarith
  have hpt : ∀ z : Euc d, ENNReal.ofReal (max (w z - L) 0) ≤
      ENNReal.ofReal (max (B * ‖z‖ ^ (-σ) - L / 2) 0) := by
    intro z
    refine ENNReal.ofReal_le_ofReal (max_le ?_ (le_max_right _ _))
    have := hw z
    refine le_trans ?_ (le_max_left _ _)
    linarith
  refine (lintegral_mono hpt).trans ((wr3_lev1_base hd hσ0 hσd hB0 (by linarith)).trans
    (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
  have h1 : B / (L / 2) = 2 * B / L := by field_simp
  have h2 : (2 * B / L) ^ ((d : ℝ) / σ - 1) = (2 * B) ^ ((d : ℝ) / σ - 1) * L ^ (1 - (d : ℝ) / σ) := by
    rw [Real.div_rpow (by positivity) hL0.le, div_eq_mul_inv, ← Real.rpow_neg hL0.le]
    congr 2; ring
  rw [h1, h2]; ring

/-! ### Second level-set integral on the unit ball -/

theorem wr3_ball_term {σ L : ℝ} (hL : 0 < L) :
    L ^ 2 * (L ^ (-(1 / σ))) ^ d = L ^ (2 - (d : ℝ) / σ) := by
  have h1 : (L ^ (-(1 / σ))) ^ d = L ^ (-((d : ℝ) / σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]; congr 1; ring
  rw [h1]
  have h2 : L ^ 2 = L ^ ((2 : ℝ)) := (Real.rpow_two L).symm
  rw [h2, ← Real.rpow_add hL, ← sub_eq_add_neg]

theorem wr3_annulus_power {σ L : ℝ} (hσ0 : 0 < σ) (hL : 0 < L) :
    (L ^ (-(1 / σ))) ^ ((d : ℝ) - 2 * σ) = L ^ (2 - (d : ℝ) / σ) := by
  rw [← Real.rpow_mul hL.le]; congr 1; field_simp; ring

/-- Second level-set integral, reduced to an annulus integral:
`∫_{B(0,1)} min(w,L)² ≤ ω_d [ (L^{2-d/σ} + 2B²)/d + 2B² ∫_r^1 t^{d-1-2σ} dt ]`, `r = L^{-1/σ}`. -/
theorem wr3_lev2_base (hd : 1 ≤ d) {σ B : ℝ} (hσ0 : 0 < σ) (hσd : σ < d) (hB : 1 ≤ B)
    {w : Euc d → ℝ} (hw : ∀ z, w z ≤ B * (1 + ‖z‖ ^ (-σ))) (hw0 : ∀ z, 0 ≤ w z) {L : ℝ}
    (hL : 1 ≤ L) :
    ∫⁻ z in ball (0 : Euc d) 1, ENNReal.ofReal ((min (w z) L) ^ 2) ≤
      ENNReal.ofReal (sphereArea d * ((L ^ (2 - (d : ℝ) / σ) + 2 * B ^ 2) * (d : ℝ)⁻¹
        + 2 * B ^ 2 * ∫ t in (L ^ (-(1 / σ)))..1, t ^ ((d : ℝ) - 1 - 2 * σ))) := by
  have hB0 : 0 < B := by linarith
  have hL0 : 0 < L := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hsA := HRS.Whole.Q34.sphereArea_nonneg hd
  set r : ℝ := L ^ (-(1 / σ)) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hL0 _
  have hr1 : r ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL
    (by have : 0 < 1 / σ := by positivity
        linarith)
  set S₂ : Set (Euc d) := {z : Euc d | ‖z‖ ∈ Ico r 1} with hS₂
  have hS₂m : MeasurableSet S₂ := measurable_norm measurableSet_Ico
  have hunion : ball (0 : Euc d) 1 = ball (0 : Euc d) r ∪ S₂ := by
    ext z
    simp only [mem_ball_zero_iff, mem_union, hS₂, mem_setOf_eq, mem_Ico]
    constructor
    · intro h
      by_cases h' : ‖z‖ < r
      · exact Or.inl h'
      · exact Or.inr ⟨not_lt.1 h', h⟩
    · rintro (h | h)
      · exact h.trans_le hr1
      · exact h.2
  have hdisj : Disjoint (ball (0 : Euc d) r) S₂ := by
    refine Set.disjoint_left.2 fun z h1 h2 => ?_
    have h1' : ‖z‖ < r := by simpa [mem_ball_zero_iff] using h1
    have h2' : r ≤ ‖z‖ := h2.1
    exact absurd h1' (not_lt.2 h2')
  have hS₂sub : S₂ ⊆ ball (0 : Euc d) 1 := by
    intro z hz
    rw [mem_ball_zero_iff]; exact hz.2
  rw [hunion, lintegral_union hS₂m hdisj]
  -- near zone
  have hT1 : ∫⁻ z in ball (0 : Euc d) r, ENNReal.ofReal ((min (w z) L) ^ 2) ≤
      ENNReal.ofReal (L ^ 2) * ENNReal.ofReal (sphereArea d * (r ^ d / d)) := by
    calc ∫⁻ z in ball (0 : Euc d) r, ENNReal.ofReal ((min (w z) L) ^ 2)
        ≤ ∫⁻ _z in ball (0 : Euc d) r, ENNReal.ofReal (L ^ 2) := by
          refine setLIntegral_mono' measurableSet_ball fun z _ => ?_
          refine ENNReal.ofReal_le_ofReal ?_
          have h0 : 0 ≤ min (w z) L := le_min (hw0 z) hL0.le
          nlinarith [min_le_right (w z) L]
      _ = ENNReal.ofReal (L ^ 2) * volume (ball (0 : Euc d) r) := setLIntegral_const _ _
      _ = _ := by rw [HRS.Whole.Q34.volume_ball_eq hd hr0]
  -- annulus
  have hpt : ∀ z ∈ S₂, ENNReal.ofReal ((min (w z) L) ^ 2) ≤
      ENNReal.ofReal (2 * B ^ 2) + ENNReal.ofReal (2 * B ^ 2) * ENNReal.ofReal (‖z‖ ^ (-(2 * σ))) := by
    intro z hz
    have ht : 0 < ‖z‖ := hr0.trans_le hz.1
    have h0 : 0 ≤ min (w z) L := le_min (hw0 z) hL0.le
    have h2 : (min (w z) L) ^ 2 ≤ (w z) ^ 2 := by nlinarith [min_le_left (w z) L]
    have hφ : 0 ≤ ‖z‖ ^ (-σ) := Real.rpow_nonneg ht.le _
    have h3 : (w z) ^ 2 ≤ (B * (1 + ‖z‖ ^ (-σ))) ^ 2 := by
      have := hw z
      have := hw0 z
      nlinarith
    have hpow : ‖z‖ ^ (-(2 * σ)) = (‖z‖ ^ (-σ)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; congr 1; push_cast; ring
    have h4 : (B * (1 + ‖z‖ ^ (-σ))) ^ 2 ≤ 2 * B ^ 2 + 2 * B ^ 2 * ‖z‖ ^ (-(2 * σ)) := by
      rw [hpow]
      nlinarith [sq_nonneg (B * (1 - ‖z‖ ^ (-σ)))]
    have hnn : 0 ≤ 2 * B ^ 2 * ‖z‖ ^ (-(2 * σ)) :=
      mul_nonneg (by positivity) (Real.rpow_nonneg ht.le _)
    calc ENNReal.ofReal ((min (w z) L) ^ 2)
        ≤ ENNReal.ofReal (2 * B ^ 2 + 2 * B ^ 2 * ‖z‖ ^ (-(2 * σ))) :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ = _ := by
          rw [ENNReal.ofReal_add (by positivity) hnn,
            ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * B ^ 2 by positivity)]
  have hJ : 0 ≤ ∫ t in r..1, t ^ ((d : ℝ) - 1 - 2 * σ) :=
    intervalIntegral.integral_nonneg hr1 fun t ht => Real.rpow_nonneg (hr0.le.trans ht.1) _
  have hT2 : ∫⁻ z in S₂, ENNReal.ofReal ((min (w z) L) ^ 2) ≤
      ENNReal.ofReal (2 * B ^ 2) * ENNReal.ofReal (sphereArea d * ((1 : ℝ) ^ d / d)) +
        ENNReal.ofReal (2 * B ^ 2) *
          ENNReal.ofReal (sphereArea d * ∫ t in r..1, t ^ ((d : ℝ) - 1 - 2 * σ)) := by
    calc ∫⁻ z in S₂, ENNReal.ofReal ((min (w z) L) ^ 2)
        ≤ ∫⁻ z in S₂, (ENNReal.ofReal (2 * B ^ 2)
            + ENNReal.ofReal (2 * B ^ 2) * ENNReal.ofReal (‖z‖ ^ (-(2 * σ)))) :=
          setLIntegral_mono' hS₂m hpt
      _ = ENNReal.ofReal (2 * B ^ 2) * volume S₂ +
            ENNReal.ofReal (2 * B ^ 2) * ∫⁻ z in S₂, ENNReal.ofReal (‖z‖ ^ (-(2 * σ))) := by
          rw [lintegral_add_left measurable_const, setLIntegral_const,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ _ := by
          rw [hS₂, wr3_lintegral_annulus hd hr0 hr1]
          gcongr
          calc volume {z : Euc d | ‖z‖ ∈ Ico r 1} ≤ volume (ball (0 : Euc d) 1) :=
                measure_mono hS₂sub
            _ = _ := HRS.Whole.Q34.volume_ball_eq hd one_pos
  refine (add_le_add hT1 hT2).trans (le_of_eq ?_)
  have hr_d : r ^ d / d = r ^ d * (d : ℝ)⁻¹ := div_eq_mul_inv _ _
  have h1d : (1 : ℝ) ^ d / d = (d : ℝ)⁻¹ := by simp [div_eq_mul_inv]
  have hq1 : 0 ≤ sphereArea d * (r ^ d / d) := by
    have := pow_nonneg hr0.le d; positivity
  have hq2 : 0 ≤ sphereArea d * ((1 : ℝ) ^ d / d) := by positivity
  have hq3 : 0 ≤ sphereArea d * ∫ t in r..1, t ^ ((d : ℝ) - 1 - 2 * σ) := mul_nonneg hsA hJ
  have h2B : (0 : ℝ) ≤ 2 * B ^ 2 := by positivity
  have hbt : L ^ (2 - (d : ℝ) / σ) = L ^ 2 * r ^ d := (wr3_ball_term (σ := σ) hL0).symm
  rw [← ENNReal.ofReal_mul (sq_nonneg L), ← ENNReal.ofReal_mul h2B, ← ENNReal.ofReal_mul h2B,
    ← ENNReal.ofReal_add (mul_nonneg h2B hq2) (mul_nonneg h2B hq3),
    ← ENNReal.ofReal_add (mul_nonneg (sq_nonneg L) hq1)
      (add_nonneg (mul_nonneg h2B hq2) (mul_nonneg h2B hq3))]
  congr 1
  rw [h1d, hbt]
  ring

/-- `2σ < d`: the second level-set integral on the unit ball is bounded. -/
theorem wr3_lev2a (hd : 1 ≤ d) {σ B : ℝ} (hσ0 : 0 < σ) (hσd : σ < d) (hB : 1 ≤ B)
    (h2 : 2 * σ < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : Euc d → ℝ, (∀ z, w z ≤ B * (1 + ‖z‖ ^ (-σ))) → (∀ z, 0 ≤ w z) →
      ∀ L : ℝ, 1 ≤ L →
        ∫⁻ z in ball (0 : Euc d) 1, ENNReal.ofReal ((min (w z) L) ^ 2) ≤ ENNReal.ofReal C := by
  have hB0 : 0 < B := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hsA := HRS.Whole.Q34.sphereArea_nonneg hd
  have he : (-1 : ℝ) < (d : ℝ) - 1 - 2 * σ := by linarith
  have hpos : 0 < (d : ℝ) - 2 * σ := by linarith
  have h2B : (0 : ℝ) ≤ 2 * B ^ 2 := by positivity
  refine ⟨sphereArea d * ((1 + 2 * B ^ 2) * (d : ℝ)⁻¹ + 2 * B ^ 2 * (1 / ((d : ℝ) - 2 * σ))),
    mul_nonneg hsA (add_nonneg (by positivity) (mul_nonneg h2B (one_div_nonneg.2 hpos.le))),
    fun w hw hw0 L hL => ?_⟩
  refine (wr3_lev2_base hd hσ0 hσd hB hw hw0 hL).trans (ENNReal.ofReal_le_ofReal ?_)
  have hL0 : 0 < L := by linarith
  set r : ℝ := L ^ (-(1 / σ)) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hL0 _
  have h1 : L ^ (2 - (d : ℝ) / σ) ≤ 1 := by
    refine Real.rpow_le_one_of_one_le_of_nonpos hL ?_
    have : 2 < (d : ℝ) / σ := by rw [lt_div_iff₀ hσ0]; linarith
    linarith
  have hJ : ∫ t in r..1, t ^ ((d : ℝ) - 1 - 2 * σ) ≤ 1 / ((d : ℝ) - 2 * σ) := by
    rw [integral_rpow (Or.inl he)]
    have h3 : (d : ℝ) - 1 - 2 * σ + 1 = (d : ℝ) - 2 * σ := by ring
    rw [h3, Real.one_rpow]
    have : 0 ≤ r ^ ((d : ℝ) - 2 * σ) := Real.rpow_nonneg hr0.le _
    exact div_le_div_of_nonneg_right (by linarith) hpos.le
  refine mul_le_mul_of_nonneg_left (add_le_add
    (mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hd0.le))
    (mul_le_mul_of_nonneg_left hJ h2B)) hsA

/-- `2σ = d`: logarithmic growth. -/
theorem wr3_lev2b (hd : 1 ≤ d) {σ B : ℝ} (hσ0 : 0 < σ) (hσd : σ < d) (hB : 1 ≤ B)
    (h2 : 2 * σ = d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : Euc d → ℝ, (∀ z, w z ≤ B * (1 + ‖z‖ ^ (-σ))) → (∀ z, 0 ≤ w z) →
      ∀ L : ℝ, 1 ≤ L →
        ∫⁻ z in ball (0 : Euc d) 1, ENNReal.ofReal ((min (w z) L) ^ 2)
          ≤ ENNReal.ofReal (C * Real.log (Real.exp 1 * L)) := by
  have hB0 : 0 < B := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hsA := HRS.Whole.Q34.sphereArea_nonneg hd
  have h2B : (0 : ℝ) ≤ 2 * B ^ 2 := by positivity
  have ha : 0 ≤ (1 + 2 * B ^ 2) * (d : ℝ)⁻¹ := by positivity
  have hb : 0 ≤ 2 * B ^ 2 / σ := by positivity
  refine ⟨sphereArea d * ((1 + 2 * B ^ 2) * (d : ℝ)⁻¹ + 2 * B ^ 2 / σ),
    mul_nonneg hsA (add_nonneg ha hb), fun w hw hw0 L hL => ?_⟩
  refine (wr3_lev2_base hd hσ0 hσd hB hw hw0 hL).trans (ENNReal.ofReal_le_ofReal ?_)
  have hL0 : 0 < L := by linarith
  set r : ℝ := L ^ (-(1 / σ)) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hL0 _
  have hexp : 2 - (d : ℝ) / σ = 0 := by
    have : (d : ℝ) = 2 * σ := h2.symm
    rw [this]; field_simp; ring
  rw [hexp, Real.rpow_zero]
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hJ : ∫ t in r..1, t ^ ((d : ℝ) - 1 - 2 * σ) = Real.log L / σ := by
    have : ∀ t : ℝ, t ^ ((d : ℝ) - 1 - 2 * σ) = t⁻¹ := by
      intro t
      have : (d : ℝ) - 1 - 2 * σ = -1 := by rw [← h2]; ring
      rw [this, Real.rpow_neg_one]
    simp_rw [this]
    rw [integral_inv_of_pos hr0 one_pos, one_div, Real.log_inv, hr, Real.log_rpow hL0]
    field_simp
  rw [hJ]
  have hlogeL : Real.log (Real.exp 1 * L) = 1 + Real.log L := by
    rw [Real.log_mul (Real.exp_pos 1).ne' hL0.ne', Real.log_exp]
  rw [hlogeL]
  have e1 : 2 * B ^ 2 * (Real.log L / σ) = 2 * B ^ 2 / σ * Real.log L := by ring
  have key : (1 + 2 * B ^ 2) * (d : ℝ)⁻¹ + 2 * B ^ 2 * (Real.log L / σ) ≤
      ((1 + 2 * B ^ 2) * (d : ℝ)⁻¹ + 2 * B ^ 2 / σ) * (1 + Real.log L) := by
    rw [e1]
    nlinarith [mul_nonneg ha hlog]
  have key' : ((1 : ℝ) + 2 * B ^ 2) * (d : ℝ)⁻¹ + 2 * B ^ 2 * (Real.log L / σ) =
      (1 + 2 * B ^ 2) * (d : ℝ)⁻¹ + 2 * B ^ 2 * (Real.log L / σ) := rfl
  calc sphereArea d * ((1 + 2 * B ^ 2) * (d : ℝ)⁻¹ + 2 * B ^ 2 * (Real.log L / σ))
      ≤ sphereArea d * (((1 + 2 * B ^ 2) * (d : ℝ)⁻¹ + 2 * B ^ 2 / σ) * (1 + Real.log L)) :=
        mul_le_mul_of_nonneg_left key hsA
    _ = _ := by ring

/-- `2σ > d`: polynomial growth `L^{2-d/σ}`. -/
theorem wr3_lev2c (hd : 1 ≤ d) {σ B : ℝ} (hσ0 : 0 < σ) (hσd : σ < d) (hB : 1 ≤ B)
    (h2 : (d : ℝ) < 2 * σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : Euc d → ℝ, (∀ z, w z ≤ B * (1 + ‖z‖ ^ (-σ))) → (∀ z, 0 ≤ w z) →
      ∀ L : ℝ, 1 ≤ L →
        ∫⁻ z in ball (0 : Euc d) 1, ENNReal.ofReal ((min (w z) L) ^ 2)
          ≤ ENNReal.ofReal (C * L ^ (2 - (d : ℝ) / σ)) := by
  have hB0 : 0 < B := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hsA := HRS.Whole.Q34.sphereArea_nonneg hd
  have hpos : 0 < 2 * σ - (d : ℝ) := by linarith
  have h2B : (0 : ℝ) ≤ 2 * B ^ 2 := by positivity
  have ha : 0 ≤ (1 + 2 * B ^ 2) * (d : ℝ)⁻¹ := by positivity
  have hb : 0 ≤ 2 * B ^ 2 / (2 * σ - (d : ℝ)) := div_nonneg h2B hpos.le
  refine ⟨sphereArea d * ((1 + 2 * B ^ 2) * (d : ℝ)⁻¹ + 2 * B ^ 2 / (2 * σ - (d : ℝ))),
    mul_nonneg hsA (add_nonneg ha hb), fun w hw hw0 L hL => ?_⟩
  refine (wr3_lev2_base hd hσ0 hσd hB hw hw0 hL).trans (ENNReal.ofReal_le_ofReal ?_)
  have hL0 : 0 < L := by linarith
  set r : ℝ := L ^ (-(1 / σ)) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hL0 _
  have hr1 : r ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL
    (by have : 0 < 1 / σ := by positivity
        linarith)
  have h1 : 1 ≤ L ^ (2 - (d : ℝ) / σ) := by
    refine Real.one_le_rpow hL ?_
    have : (d : ℝ) / σ < 2 := by rw [div_lt_iff₀ hσ0]; linarith
    linarith
  have hJ : ∫ t in r..1, t ^ ((d : ℝ) - 1 - 2 * σ) ≤ L ^ (2 - (d : ℝ) / σ) / (2 * σ - (d : ℝ)) := by
    have he : (d : ℝ) - 1 - 2 * σ ≠ -1 := by intro h; linarith
    rw [integral_rpow (Or.inr ⟨he, by
      rw [Set.mem_uIcc]; push Not; exact ⟨fun h => absurd h (not_le.2 hr0), fun h => absurd h (by norm_num)⟩⟩)]
    have h3 : (d : ℝ) - 1 - 2 * σ + 1 = (d : ℝ) - 2 * σ := by ring
    rw [h3, Real.one_rpow, hr, wr3_annulus_power hσ0 hL0]
    have : (1 - L ^ (2 - (d : ℝ) / σ)) / ((d : ℝ) - 2 * σ)
        = (L ^ (2 - (d : ℝ) / σ) - 1) / (2 * σ - (d : ℝ)) := by
      have : (d : ℝ) - 2 * σ ≠ 0 := by intro h; linarith
      field_simp; ring
    rw [this]
    exact div_le_div_of_nonneg_right (by linarith) hpos.le
  have hLp : 0 ≤ L ^ (2 - (d : ℝ) / σ) := by positivity
  have e2 : 2 * B ^ 2 * (L ^ (2 - (d : ℝ) / σ) / (2 * σ - (d : ℝ)))
      = 2 * B ^ 2 / (2 * σ - (d : ℝ)) * L ^ (2 - (d : ℝ) / σ) := by ring
  have key : (L ^ (2 - (d : ℝ) / σ) + 2 * B ^ 2) * (d : ℝ)⁻¹
      + 2 * B ^ 2 * ∫ t in r..1, t ^ ((d : ℝ) - 1 - 2 * σ) ≤
      ((1 + 2 * B ^ 2) * (d : ℝ)⁻¹ + 2 * B ^ 2 / (2 * σ - (d : ℝ))) * L ^ (2 - (d : ℝ) / σ) := by
    have t1 : (L ^ (2 - (d : ℝ) / σ) + 2 * B ^ 2) * (d : ℝ)⁻¹
        ≤ (1 + 2 * B ^ 2) * (d : ℝ)⁻¹ * L ^ (2 - (d : ℝ) / σ) := by
      have : L ^ (2 - (d : ℝ) / σ) + 2 * B ^ 2 ≤ (1 + 2 * B ^ 2) * L ^ (2 - (d : ℝ) / σ) := by
        nlinarith [mul_le_mul_of_nonneg_left h1 h2B]
      calc (L ^ (2 - (d : ℝ) / σ) + 2 * B ^ 2) * (d : ℝ)⁻¹
          ≤ ((1 + 2 * B ^ 2) * L ^ (2 - (d : ℝ) / σ)) * (d : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right this (inv_nonneg.2 hd0.le)
        _ = _ := by ring
    have t2 := mul_le_mul_of_nonneg_left hJ h2B
    nlinarith
  exact (mul_le_mul_of_nonneg_left key hsA).trans (le_of_eq (by ring))

/-- **Euclidean level-set integrals of `W_s = 1 + rieszWeight s`** (port of `kernel_levels` and
`kernel_levels_real`, `0 ≤ s < d`): with `σ = sigmaOf d s`,
`∫_{ℝ^d} (W_s - L)_+ ≤ C₁ L^{1-d/σ}` for `L ≥ 2`, and `∫_{B(0,1)} min(W_s, L)² ≤ C₂ ψ₂(L)` for
`L ≥ 1`.  The integrals are `ℝ≥0∞`-valued (no Bochner junk); the first one is over all of `ℝ^d`
(finite only because `W_s - L` has bounded support for `L ≥ 2`), the second over the unit ball
(over `ℝ^d` it is infinite since `W_s ≥ 1`); the far zone is handled in `WrRowAux2`. -/
theorem wr3_kernel_levels_real (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      (∀ L : ℝ, 2 ≤ L → ∫⁻ z : Euc d, ENNReal.ofReal (max (1 + HRS.Whole.rieszWeight s z - L) 0)
          ≤ ENNReal.ofReal (C₁ * L ^ (1 - (d : ℝ) / HRS.WeakRef.sigmaOf d s))) ∧
      (∀ L : ℝ, 1 ≤ L → ∫⁻ z in ball (0 : Euc d) 1,
          ENNReal.ofReal ((min (1 + HRS.Whole.rieszWeight s z) L) ^ 2)
          ≤ ENNReal.ofReal (C₂ * HRS.WeakRef.psi2 d s L)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hσ0 := HRS.WeakRef.sigmaOf_pos hd hs0
  have hσd := HRS.WeakRef.sigmaOf_lt hd hsd
  set σ := HRS.WeakRef.sigmaOf d s with hσ
  set B : ℝ := 1 + 4 / (d : ℝ) with hB
  have hB1 : 1 ≤ B := by
    have : 0 ≤ 4 / (d : ℝ) := by positivity
    rw [hB]; linarith
  have hwle : ∀ z : Euc d, 1 + HRS.Whole.rieszWeight s z ≤ 1 + B * ‖z‖ ^ (-σ) := fun z => by
    have := wr3_rieszWeight_le (s := s) hd z
    linarith
  have hwB : ∀ z : Euc d, 1 + HRS.Whole.rieszWeight s z ≤ B * (1 + ‖z‖ ^ (-σ)) := fun z => by
    have := hwle z
    have h5 : 0 ≤ ‖z‖ ^ (-σ) := Real.rpow_nonneg (norm_nonneg _) _
    nlinarith
  have hw0 : ∀ z : Euc d, 0 ≤ 1 + HRS.Whole.rieszWeight s z := fun z => by
    have := wr3_rieszWeight_nonneg (d := d) s z
    linarith
  obtain ⟨C₁, hC₁, hlev1⟩ := wr3_lev1 hd hσ0 hσd hB1
  have h2 : ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ L : ℝ, 1 ≤ L → ∫⁻ z in ball (0 : Euc d) 1,
      ENNReal.ofReal ((min (1 + HRS.Whole.rieszWeight s z) L) ^ 2)
        ≤ ENNReal.ofReal (C₂ * HRS.WeakRef.psi2 d s L) := by
    rcases lt_trichotomy s ((d : ℝ) / 2) with h | h | h
    · have h2σ : 2 * σ < d := (HRS.WeakRef.two_sigmaOf_lt_iff hd hs0).2 h
      obtain ⟨C, hC, hlev⟩ := wr3_lev2a hd hσ0 hσd hB1 h2σ
      refine ⟨C, hC, fun L hL => ?_⟩
      have : HRS.WeakRef.psi2 d s L = 1 := by unfold HRS.WeakRef.psi2; rw [if_pos h]
      rw [this, mul_one]
      exact hlev _ hwB hw0 L hL
    · have hσs : σ = s := HRS.WeakRef.sigmaOf_eq hd (by rw [h])
      have h2σ : 2 * σ = d := by rw [hσs, h]; ring
      obtain ⟨C, hC, hlev⟩ := wr3_lev2b hd hσ0 hσd hB1 h2σ
      refine ⟨C, hC, fun L hL => ?_⟩
      have : HRS.WeakRef.psi2 d s L = Real.log (Real.exp 1 * L) := by
        unfold HRS.WeakRef.psi2; rw [if_neg (not_lt.2 h.ge), if_pos h]
      rw [this]
      exact hlev _ hwB hw0 L hL
    · have hσs : σ = s := HRS.WeakRef.sigmaOf_eq hd h.le
      have h2σ : (d : ℝ) < 2 * σ := by rw [hσs]; linarith
      obtain ⟨C, hC, hlev⟩ := wr3_lev2c hd hσ0 hσd hB1 h2σ
      refine ⟨C, hC, fun L hL => ?_⟩
      have : HRS.WeakRef.psi2 d s L = L ^ (2 - (d : ℝ) / σ) := by
        unfold HRS.WeakRef.psi2; rw [if_neg (not_lt.2 h.le), if_neg h.ne', hσs]
      rw [this]
      exact hlev _ hwB hw0 L hL
  obtain ⟨C₂, hC₂, h2'⟩ := h2
  exact ⟨C₁, C₂, hC₁, hC₂, fun L hL => hlev1 _ hwle L hL, h2'⟩

end HRS.MS.Wr
