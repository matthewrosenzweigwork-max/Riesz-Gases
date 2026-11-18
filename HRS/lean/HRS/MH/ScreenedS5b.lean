import HRS.MH.ScreenedP1Aux1
import HRS.MH.ScreenedA7

/-!
# Packet S5b (`gag_product`, S.B.4): product estimate for the Gagliardo form.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}


/-- `(‖a‖ₑ)² = ofReal (a²)`. -/
lemma s5b_enorm_sq (a : ℝ) : ‖a‖ₑ ^ 2 = ENNReal.ofReal (a ^ 2) := by
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]

/-- The real product inequality: `(p0 U0 - p1 U1)² ≤ 2B²(U0-U1)² + 2M²U1²` when `|p0| ≤ B`, `|p0-p1| ≤ M`. -/
lemma s5b_real_pt {B M p0 p1 U0 U1 : ℝ} (hB : 0 ≤ B) (h0 : |p0| ≤ B) (hM : |p0 - p1| ≤ M) :
    (p0 * U0 - p1 * U1) ^ 2 ≤ 2 * B ^ 2 * (U0 - U1) ^ 2 + 2 * M ^ 2 * U1 ^ 2 := by
  have hp0 : p0 ^ 2 ≤ B ^ 2 := sq_le_sq' (abs_le.mp h0).1 (abs_le.mp h0).2
  have hpM : (p0 - p1) ^ 2 ≤ M ^ 2 := sq_le_sq' (abs_le.mp hM).1 (abs_le.mp hM).2
  have hPsq : (p0 * (U0 - U1)) ^ 2 ≤ B ^ 2 * (U0 - U1) ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right hp0 (sq_nonneg _)
  have hQsq : (U1 * (p0 - p1)) ^ 2 ≤ M ^ 2 * U1 ^ 2 := by
    rw [mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left hpM (sq_nonneg U1)]
  have hid : p0 * U0 - p1 * U1 = p0 * (U0 - U1) + U1 * (p0 - p1) := by ring
  rw [hid]
  nlinarith [sq_nonneg (p0 * (U0 - U1) - U1 * (p0 - p1))]

/-- The Lipschitz increment bound `|ϕ(x+h) - ϕ x| ≤ min(La‖h‖, 2B)`. -/
lemma s5b_diff_bound {La B : ℝ} {ϕ : Euc d → ℝ} (hL : ∀ x y, |ϕ x - ϕ y| ≤ La * ‖x - y‖)
    (hB : ∀ x, |ϕ x| ≤ B) (x h : Euc d) :
    |ϕ (x + h) - ϕ x| ≤ min (La * ‖h‖) (2 * B) := by
  apply le_min
  · have := hL (x + h) x
    simpa using this
  · calc |ϕ (x + h) - ϕ x| ≤ |ϕ (x + h)| + |ϕ x| := abs_sub _ _
      _ ≤ B + B := add_le_add (hB _) (hB _)
      _ = 2 * B := by ring

/-- Pointwise `L²` product bound for the Gagliardo increment of `ϕ u`. -/
lemma s5b_pt {La B : ℝ} {ϕ u : Euc d → ℝ} (hL : ∀ x y, |ϕ x - ϕ y| ≤ La * ‖x - y‖)
    (hB : ∀ x, |ϕ x| ≤ B) (hB0 : 0 ≤ B) (h x : Euc d) :
    ‖ϕ (x + h) * u (x + h) - ϕ x * u x‖ₑ ^ 2 ≤
      ENNReal.ofReal (2 * B ^ 2) * ‖u (x + h) - u x‖ₑ ^ 2 +
        ENNReal.ofReal (2 * (min (La * ‖h‖) (2 * B)) ^ 2) * ‖u x‖ₑ ^ 2 := by
  have hr := s5b_real_pt (U0 := u (x + h)) (U1 := u x) hB0 (hB (x + h))
    (s5b_diff_bound hL hB x h)
  simp only [s5b_enorm_sq]
  calc ENNReal.ofReal ((ϕ (x + h) * u (x + h) - ϕ x * u x) ^ 2)
      ≤ ENNReal.ofReal (2 * B ^ 2 * (u (x + h) - u x) ^ 2 +
          2 * (min (La * ‖h‖) (2 * B)) ^ 2 * (u x) ^ 2) := ENNReal.ofReal_le_ofReal hr
    _ = ENNReal.ofReal (2 * B ^ 2) * ENNReal.ofReal ((u (x + h) - u x) ^ 2) +
          ENNReal.ofReal (2 * (min (La * ‖h‖) (2 * B)) ^ 2) * ENNReal.ofReal ((u x) ^ 2) := by
        rw [ENNReal.ofReal_add (show (0:ℝ) ≤ 2 * B ^ 2 * (u (x + h) - u x) ^ 2 by positivity)
            (show (0:ℝ) ≤ 2 * (min (La * ‖h‖) (2 * B)) ^ 2 * (u x) ^ 2 by positivity),
          ENNReal.ofReal_mul (show (0:ℝ) ≤ 2 * B ^ 2 by positivity),
          ENNReal.ofReal_mul (show (0:ℝ) ≤ 2 * (min (La * ‖h‖) (2 * B)) ^ 2 by positivity)]

/-- Integrability of the far part of `|h|^{-d-2σ}` for `σ > 0`, used in the `J` bound. -/
lemma s5b_J_bound {σ : ℝ} (hd : 1 ≤ d) (h0 : 0 < σ) (h1 : σ < 1) :
    ∃ CK T' : ℝ, 0 ≤ CK ∧ 0 ≤ T' ∧ ∀ La B : ℝ, 0 ≤ La → 0 ≤ B →
      ∫⁻ h : Euc d, ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ))) *
          ENNReal.ofReal (2 * (min (La * ‖h‖) (2 * B)) ^ 2) ≤
        ENNReal.ofReal (2 * La ^ 2 * CK + 8 * B ^ 2 * T') := by
  obtain ⟨CK, hCK0, hCK⟩ := lintegral_ball_rpow_le_proof (t := (d : ℝ) + 2 * σ - 2) hd (by linarith)
  have hTfin : ∫⁻ h in (Metric.closedBall (0 : Euc d) 1)ᶜ, ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ)))
      < ⊤ := p1_tail_lintegral_lt_top (t := (d : ℝ) + 2 * σ) (by linarith)
  obtain ⟨T', hT0, hTeq⟩ : ∃ T' : ℝ, 0 ≤ T' ∧
      (∫⁻ h in (Metric.closedBall (0 : Euc d) 1)ᶜ, ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ)))) =
        ENNReal.ofReal T' :=
    ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hTfin.ne).symm⟩
  refine ⟨CK, T', hCK0, hT0, ?_⟩
  intro La B hLa hB0
  have hdpos : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hpt : ∀ h : Euc d,
      ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ))) * ENNReal.ofReal (2 * (min (La * ‖h‖) (2 * B)) ^ 2) ≤
        (Metric.closedBall (0 : Euc d) 1).indicator
          (fun h => ENNReal.ofReal (2 * La ^ 2) * ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ - 2)))) h +
        (Metric.closedBall (0 : Euc d) 1)ᶜ.indicator
          (fun h => ENNReal.ofReal (8 * B ^ 2) * ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ)))) h := by
    intro h
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)]
    by_cases hb : h ∈ Metric.closedBall (0 : Euc d) 1
    · rw [Set.indicator_of_mem hb,
        Set.indicator_of_notMem (show h ∉ (Metric.closedBall (0 : Euc d) 1)ᶜ from fun h' => h' hb),
        add_zero, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rcases eq_or_ne h 0 with rfl | hne
      · have hz : (0 : ℝ) ^ (-((d : ℝ) + 2 * σ)) = 0 :=
          Real.zero_rpow (ne_of_lt (by linarith))
        rw [norm_zero, hz, zero_mul]
        positivity
      · have hpos : 0 < ‖h‖ := norm_pos_iff.2 hne
        have hmin0 : 0 ≤ min (La * ‖h‖) (2 * B) := le_min (mul_nonneg hLa (norm_nonneg _)) (by linarith)
        have hM : (min (La * ‖h‖) (2 * B)) ^ 2 ≤ (La * ‖h‖) ^ 2 :=
          pow_le_pow_left₀ hmin0 (min_le_left _ _) 2
        have hrp : ‖h‖ ^ (-((d : ℝ) + 2 * σ - 2)) = ‖h‖ ^ (-((d : ℝ) + 2 * σ)) * ‖h‖ ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hpos]
          congr 1
          push_cast
          ring
        have hw : 0 ≤ ‖h‖ ^ (-((d : ℝ) + 2 * σ)) := Real.rpow_nonneg (norm_nonneg _) _
        rw [hrp]
        nlinarith [mul_le_mul_of_nonneg_left hM hw]
    · rw [Set.indicator_of_notMem hb,
        Set.indicator_of_mem (show h ∈ (Metric.closedBall (0 : Euc d) 1)ᶜ from hb),
        zero_add, ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hmin0 : 0 ≤ min (La * ‖h‖) (2 * B) := le_min (mul_nonneg hLa (norm_nonneg _)) (by linarith)
      have hM : min (La * ‖h‖) (2 * B) ≤ 2 * B := min_le_right _ _
      have hM2 : (min (La * ‖h‖) (2 * B)) ^ 2 ≤ (2 * B) ^ 2 := pow_le_pow_left₀ hmin0 hM 2
      have hw : 0 ≤ ‖h‖ ^ (-((d : ℝ) + 2 * σ)) := Real.rpow_nonneg (norm_nonneg _) _
      nlinarith [mul_le_mul_of_nonneg_left hM2 hw]
  have hmeas1 : Measurable (fun h : Euc d => ENNReal.ofReal (2 * La ^ 2) *
      ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ - 2)))) := by
    fun_prop
  have hball : ∫⁻ h in Metric.closedBall (0 : Euc d) 1,
      ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ - 2))) ≤ ENNReal.ofReal CK := by
    have h2 := hCK 1 one_pos
    simpa using h2
  calc ∫⁻ h : Euc d, ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ))) *
        ENNReal.ofReal (2 * (min (La * ‖h‖) (2 * B)) ^ 2)
      ≤ ∫⁻ h : Euc d, ((Metric.closedBall (0 : Euc d) 1).indicator
          (fun h => ENNReal.ofReal (2 * La ^ 2) * ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ - 2)))) h +
        (Metric.closedBall (0 : Euc d) 1)ᶜ.indicator
          (fun h => ENNReal.ofReal (8 * B ^ 2) * ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ)))) h) :=
        lintegral_mono hpt
    _ = (∫⁻ h : Euc d, (Metric.closedBall (0 : Euc d) 1).indicator
          (fun h => ENNReal.ofReal (2 * La ^ 2) * ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ - 2)))) h) +
        ∫⁻ h : Euc d, (Metric.closedBall (0 : Euc d) 1)ᶜ.indicator
          (fun h => ENNReal.ofReal (8 * B ^ 2) * ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ)))) h :=
        lintegral_add_left (hmeas1.indicator measurableSet_closedBall) _
    _ = (∫⁻ h in Metric.closedBall (0 : Euc d) 1,
          ENNReal.ofReal (2 * La ^ 2) * ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ - 2)))) +
        ∫⁻ h in (Metric.closedBall (0 : Euc d) 1)ᶜ,
          ENNReal.ofReal (8 * B ^ 2) * ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ))) := by
        rw [lintegral_indicator measurableSet_closedBall,
          lintegral_indicator measurableSet_closedBall.compl]
    _ = ENNReal.ofReal (2 * La ^ 2) * (∫⁻ h in Metric.closedBall (0 : Euc d) 1,
          ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ - 2)))) +
        ENNReal.ofReal (8 * B ^ 2) * (∫⁻ h in (Metric.closedBall (0 : Euc d) 1)ᶜ,
          ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ)))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (2 * La ^ 2) * ENNReal.ofReal CK +
        ENNReal.ofReal (8 * B ^ 2) * (∫⁻ h in (Metric.closedBall (0 : Euc d) 1)ᶜ,
          ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ)))) :=
        add_le_add (mul_le_mul_of_nonneg_left hball (by simp)) le_rfl
    _ = ENNReal.ofReal (2 * La ^ 2 * CK + 8 * B ^ 2 * T') := by
        rw [hTeq, ENNReal.ofReal_add (show (0:ℝ) ≤ 2 * La ^ 2 * CK by positivity)
            (show (0:ℝ) ≤ 8 * B ^ 2 * T' by positivity),
          ENNReal.ofReal_mul (show (0:ℝ) ≤ 2 * La ^ 2 by positivity),
          ENNReal.ofReal_mul (show (0:ℝ) ≤ 8 * B ^ 2 by positivity)]

/-- `La ≥ 0` for a Lipschitz function on `Euc d`, `d ≥ 1`. -/
lemma s5b_La_nonneg (hd : 1 ≤ d) {La : ℝ} {ϕ : Euc d → ℝ}
    (hL : HRS.PDE.ToolboxRd.IsLipschitz La ϕ) : 0 ≤ La := by
  have hd0 : 0 < d := by omega
  have h1 := hL (EuclideanSpace.single (⟨0, hd0⟩ : Fin d) (1 : ℝ)) 0
  rw [sub_zero, PiLp.norm_single, norm_one, mul_one] at h1
  exact le_trans (abs_nonneg _) h1

lemma s5b_sq_sqrt (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- `(eLpNorm u 2)² = ∫⁻ ‖u‖ₑ²` for a.e.-strongly-measurable `u`. -/
lemma s5b_eLpNorm_sq {u : Euc d → ℝ} (hu : AEStronglyMeasurable u volume) :
    (eLpNorm u 2 volume) ^ 2 = ∫⁻ x, ‖u x‖ₑ ^ 2 := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp) hu]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact s5b_sq_sqrt _

/-- Translated increments of an `L²` function are a.e.-measurable (in `x`, for fixed `h`). -/
lemma s5b_aemeas_incr {u : Euc d → ℝ} (hu : MemLp u 2 volume) (h : Euc d) :
    AEMeasurable (fun x => ‖u (x + h) - u x‖ₑ ^ 2) volume := by
  have hT : AEStronglyMeasurable (fun x => u (x + h)) volume :=
    hu.aestronglyMeasurable.comp_quasiMeasurePreserving
      (measurePreserving_add_right volume h).quasiMeasurePreserving
  exact ((hT.sub hu.aestronglyMeasurable).enorm).pow_const 2

/-- Fixed-`h` integral bound: `∫⁻ x ‖Δ_h(ϕu)‖² ≤ 2B² ∫⁻ ‖Δ_h u‖² + 2M_h² ∫⁻ ‖u‖²`. -/
lemma s5b_inner {La B : ℝ} {ϕ u : Euc d → ℝ} (hL : ∀ x y, |ϕ x - ϕ y| ≤ La * ‖x - y‖)
    (hB : ∀ x, |ϕ x| ≤ B) (hB0 : 0 ≤ B) (hu : MemLp u 2 volume) (h : Euc d) :
    ∫⁻ x, ‖ϕ (x + h) * u (x + h) - ϕ x * u x‖ₑ ^ 2 ≤
      ENNReal.ofReal (2 * B ^ 2) * (∫⁻ x, ‖u (x + h) - u x‖ₑ ^ 2) +
        ENNReal.ofReal (2 * (min (La * ‖h‖) (2 * B)) ^ 2) * (eLpNorm u 2 volume) ^ 2 := by
  rw [s5b_eLpNorm_sq hu.aestronglyMeasurable]
  calc ∫⁻ x, ‖ϕ (x + h) * u (x + h) - ϕ x * u x‖ₑ ^ 2
      ≤ ∫⁻ x, (ENNReal.ofReal (2 * B ^ 2) * ‖u (x + h) - u x‖ₑ ^ 2 +
          ENNReal.ofReal (2 * (min (La * ‖h‖) (2 * B)) ^ 2) * ‖u x‖ₑ ^ 2) :=
        lintegral_mono fun x => s5b_pt hL hB hB0 h x
    _ = ENNReal.ofReal (2 * B ^ 2) * (∫⁻ x, ‖u (x + h) - u x‖ₑ ^ 2) +
          ENNReal.ofReal (2 * (min (La * ‖h‖) (2 * B)) ^ 2) * (∫⁻ x, ‖u x‖ₑ ^ 2) := by
        rw [lintegral_add_left' ((s5b_aemeas_incr hu h).const_mul _),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Main assembly for `gag_product`. -/
theorem gag_product_proof (hd : 1 ≤ d) {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (La B : ℝ) (ϕ u : Euc d → ℝ), HRS.PDE.ToolboxRd.IsLipschitz La ϕ → (∀ x, |ϕ x| ≤ B) →
      MemLp u 2 volume →
      gagSq σ (fun x => ϕ x * u x) ≤
        ENNReal.ofReal (C * (La + B) ^ 2) * ((eLpNorm u 2 volume) ^ 2 + gagSq σ u) := by
  obtain ⟨CK, T', hCK0, hT0, hJ⟩ := s5b_J_bound (d := d) hd h0 h1
  refine ⟨2 + 2 * CK + 8 * T', by positivity, ?_⟩
  intro La B ϕ u hL hB hu
  have hLa : 0 ≤ La := s5b_La_nonneg hd hL
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hstep1 : gagSq σ (fun x => ϕ x * u x) ≤
      (∫⁻ h : Euc d, ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ))) *
          ENNReal.ofReal (2 * (min (La * ‖h‖) (2 * B)) ^ 2)) * (eLpNorm u 2 volume) ^ 2 +
        ENNReal.ofReal (2 * B ^ 2) * gagSq σ u := by
    have hmW : Measurable (fun h : Euc d => ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ))) *
        ENNReal.ofReal (2 * (min (La * ‖h‖) (2 * B)) ^ 2)) := by
      fun_prop
    have hpt : ∀ h : Euc d,
        ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ))) *
            ∫⁻ x, ‖ϕ (x + h) * u (x + h) - ϕ x * u x‖ₑ ^ 2 ≤
          ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ))) *
              ENNReal.ofReal (2 * (min (La * ‖h‖) (2 * B)) ^ 2) * (eLpNorm u 2 volume) ^ 2 +
            ENNReal.ofReal (2 * B ^ 2) *
              (ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ))) * (∫⁻ x, ‖u (x + h) - u x‖ₑ ^ 2)) := by
      intro h
      have hI := s5b_inner hL hB hB0 hu h
      calc ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ))) *
            ∫⁻ x, ‖ϕ (x + h) * u (x + h) - ϕ x * u x‖ₑ ^ 2
          ≤ ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ))) *
              (ENNReal.ofReal (2 * B ^ 2) * (∫⁻ x, ‖u (x + h) - u x‖ₑ ^ 2) +
                ENNReal.ofReal (2 * (min (La * ‖h‖) (2 * B)) ^ 2) * (eLpNorm u 2 volume) ^ 2) := by
            gcongr
        _ = ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ))) *
              ENNReal.ofReal (2 * (min (La * ‖h‖) (2 * B)) ^ 2) * (eLpNorm u 2 volume) ^ 2 +
            ENNReal.ofReal (2 * B ^ 2) *
              (ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ))) * (∫⁻ x, ‖u (x + h) - u x‖ₑ ^ 2)) := by
          ring
    unfold gagSq
    calc ∫⁻ h : Euc d, ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ))) *
            ∫⁻ x, ‖ϕ (x + h) * u (x + h) - ϕ x * u x‖ₑ ^ 2
        ≤ ∫⁻ h : Euc d, (ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ))) *
              ENNReal.ofReal (2 * (min (La * ‖h‖) (2 * B)) ^ 2) * (eLpNorm u 2 volume) ^ 2 +
            ENNReal.ofReal (2 * B ^ 2) *
              (ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ))) * (∫⁻ x, ‖u (x + h) - u x‖ₑ ^ 2))) :=
          lintegral_mono hpt
      _ = (∫⁻ h : Euc d, ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ))) *
              ENNReal.ofReal (2 * (min (La * ‖h‖) (2 * B)) ^ 2)) * (eLpNorm u 2 volume) ^ 2 +
          ENNReal.ofReal (2 * B ^ 2) * (∫⁻ h : Euc d,
            ENNReal.ofReal (‖h‖ ^ (-((d : ℝ) + 2 * σ))) * (∫⁻ x, ‖u (x + h) - u x‖ₑ ^ 2)) := by
          rw [lintegral_add_left' (hmW.mul_const ((eLpNorm u 2 volume) ^ 2)).aemeasurable,
            lintegral_mul_const _ hmW,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hJ' := hJ La B hLa hB0
  have hKM : 2 * La ^ 2 * CK + 8 * B ^ 2 * T' ≤ (2 + 2 * CK + 8 * T') * (La + B) ^ 2 := by
    have hA : La ^ 2 ≤ (La + B) ^ 2 := by nlinarith
    have hBB : B ^ 2 ≤ (La + B) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hA hCK0, mul_le_mul_of_nonneg_left hBB hT0,
      sq_nonneg (La + B)]
  have hBM : 2 * B ^ 2 ≤ (2 + 2 * CK + 8 * T') * (La + B) ^ 2 := by
    have hBB : B ^ 2 ≤ (La + B) ^ 2 := by nlinarith
    nlinarith [mul_nonneg hCK0 (sq_nonneg (La + B)), mul_nonneg hT0 (sq_nonneg (La + B))]
  have hc1 := hJ'.trans (ENNReal.ofReal_le_ofReal hKM)
  have hc2 : ENNReal.ofReal (2 * B ^ 2) ≤ ENNReal.ofReal ((2 + 2 * CK + 8 * T') * (La + B) ^ 2) :=
    ENNReal.ofReal_le_ofReal hBM
  calc gagSq σ (fun x => ϕ x * u x)
      ≤ _ := hstep1
    _ ≤ ENNReal.ofReal ((2 + 2 * CK + 8 * T') * (La + B) ^ 2) * (eLpNorm u 2 volume) ^ 2 +
          ENNReal.ofReal ((2 + 2 * CK + 8 * T') * (La + B) ^ 2) * gagSq σ u :=
        add_le_add (mul_le_mul_of_nonneg_right hc1 (by simp))
          (mul_le_mul_of_nonneg_right hc2 (by simp))
    _ = ENNReal.ofReal ((2 + 2 * CK + 8 * T') * (La + B) ^ 2) *
          ((eLpNorm u 2 volume) ^ 2 + gagSq σ u) := by rw [mul_add]
