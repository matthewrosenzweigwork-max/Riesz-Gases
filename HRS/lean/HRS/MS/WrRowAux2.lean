import HRS.MS.WrRowAux1

/-!
# HRS.MS.WrRowAux2 -- real-level row bounds of kernels dominated by `W_s`, `ρ ≤ M` (WR-3, part 2)

Port of `row_bounds_real` (`HRS/Energy/WeakReference.lean:4843`) from `Torus d` to `ℝ^d`
(`0 ≤ s < d`, `μ = ρ dx`, `ρ` a probability density with `ρ ≤ M` only; no lower bound and no
smoothness is used).  The torus convolution estimate `KernelAux2.lintegral_conv_le` is replaced by
`Q34.lintegral_conv_le`, and the infinite volume of `ℝ^d` is handled by splitting `ℝ^d` into the unit
ball (where the level-set integrals of `WrRowAux1` apply) and its complement (where `W_s ≤ 1 + B₀`,
`B₀ = 1 + 4/d`, so `min(W_s, L)² ≤ (1 + B₀)²`); for `L < 2 max(A,1)` the first bound is the trivial one
`∫ (q - L)_+ dμ ≤ ∫ q dμ ≤ c` together with `L^{1-d/σ} ≥ (2 max(A,1))^{1-d/σ}`.

The statements are `ℝ≥0∞`-valued, so no Bochner junk value can make them vacuous;
`WrRowAux3` derives the real-valued forms with integrability.  The kernel only has to be bounded
by `A W_s(x-y)` off the diagonal (as `IsBoundedPairKernel`); measurability of `q` is not needed here.
Helper lemmas carry the prefix `wr3_`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Set Metric
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

variable {d : ℕ}

theorem wr3_measurable_rieszWeight (s : ℝ) : Measurable (HRS.Whole.rieszWeight s : Euc d → ℝ) := by
  by_cases h : s = 0
  · have : (HRS.Whole.rieszWeight s : Euc d → ℝ) = fun z => max (-Real.log ‖z‖) 0 := by
      funext z; unfold HRS.Whole.rieszWeight; rw [if_pos h]
    rw [this]
    exact (Real.measurable_log.comp measurable_norm).neg.max measurable_const
  · have : (HRS.Whole.rieszWeight s : Euc d → ℝ) = fun z => ‖z‖ ^ (-s) := by
      funext z; unfold HRS.Whole.rieszWeight; rw [if_neg h]
    rw [this]
    exact measurable_norm.pow_const _

/-- A density `ρ dx` does not charge a point. -/
theorem wr3_ae_ne (hd : 1 ≤ d) (ρ : Euc d → ℝ) (x : Euc d) :
    ∀ᵐ y ∂(HRS.Whole.withDensityReal ρ), y ≠ x := by
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have h : ∀ᵐ y ∂(volume : Measure (Euc d)), y ≠ x := by
    rw [ae_iff]
    simpa using measure_singleton (μ := (volume : Measure (Euc d))) x
  exact (withDensity_absolutelyContinuous _ _).ae_le h

/-- `ψ₂(L) ≥ 1` for `L ≥ 1`. -/
theorem wr3_one_le_psi2 (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) {L : ℝ} (hL : 1 ≤ L) :
    1 ≤ HRS.WeakRef.psi2 d s L := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hL0 : 0 < L := by linarith
  unfold HRS.WeakRef.psi2
  split_ifs with h1 h2
  · exact le_rfl
  · have : 1 ≤ Real.exp 1 * L := by
      have := Real.add_one_le_exp (1 : ℝ); nlinarith [Real.exp_pos 1]
    have h3 : Real.log (Real.exp 1 * L) = 1 + Real.log L := by
      rw [Real.log_mul (Real.exp_pos 1).ne' hL0.ne', Real.log_exp]
    rw [h3]; linarith [Real.log_nonneg hL]
  · push Not at h1
    have hs : 0 < s := by
      have : 0 < (d : ℝ) / 2 := by positivity
      linarith
    refine Real.one_le_rpow hL ?_
    have : (d : ℝ) / s ≤ 2 := by rw [div_le_iff₀ hs]; linarith
    linarith

/-- Mass of the weight `W_s(x - ·)` against `ρ dx`, `ρ ≤ M`. -/
theorem wr3_lintegral_W_row (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) (x : Euc d) :
    ∫⁻ y, ENNReal.ofReal (1 + HRS.Whole.rieszWeight s (x - y)) ∂(HRS.Whole.withDensityReal ρ)
      ≤ ENNReal.ofReal (1 + (1 + 4 / (d : ℝ)) *
          (M * sphereArea d / ((d : ℝ) - HRS.WeakRef.sigmaOf d s) + 1)) := by
  have hσ0 := HRS.WeakRef.sigmaOf_pos hd hs0
  have hσd := HRS.WeakRef.sigmaOf_lt hd hsd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  set σ := HRS.WeakRef.sigmaOf d s with hσ
  set B : ℝ := 1 + 4 / (d : ℝ) with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hpt : ∀ y : Euc d, ENNReal.ofReal (1 + HRS.Whole.rieszWeight s (x - y)) ≤
      1 + ENNReal.ofReal B * ENNReal.ofReal (‖x - y‖ ^ (-σ)) := by
    intro y
    have h1 := wr3_rieszWeight_le (s := s) hd (x - y)
    have h2 : 0 ≤ ‖x - y‖ ^ (-σ) := Real.rpow_nonneg (norm_nonneg _) _
    calc ENNReal.ofReal (1 + HRS.Whole.rieszWeight s (x - y))
        ≤ ENNReal.ofReal (1 + B * ‖x - y‖ ^ (-σ)) := ENNReal.ofReal_le_ofReal (by linarith)
      _ = _ := by
          rw [ENNReal.ofReal_add zero_le_one (mul_nonneg hB0 h2), ENNReal.ofReal_mul hB0,
            ENNReal.ofReal_one]
  calc ∫⁻ y, ENNReal.ofReal (1 + HRS.Whole.rieszWeight s (x - y)) ∂(HRS.Whole.withDensityReal ρ)
      ≤ ∫⁻ y, (1 + ENNReal.ofReal B * ENNReal.ofReal (‖x - y‖ ^ (-σ)))
          ∂(HRS.Whole.withDensityReal ρ) := lintegral_mono hpt
    _ = 1 + ENNReal.ofReal B * ∫⁻ y, ENNReal.ofReal (‖x - y‖ ^ (-σ))
          ∂(HRS.Whole.withDensityReal ρ) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ 1 + ENNReal.ofReal B * ENNReal.ofReal (M * sphereArea d / ((d : ℝ) - σ) + 1) := by
        gcongr
        exact HRS.Whole.Q34.lintegral_kernel_le hd hσ0 hσd hρ hM x
    _ = _ := by
        have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
        have hsA := HRS.Whole.Q34.sphereArea_nonneg hd
        have hdσ : 0 < (d : ℝ) - σ := by linarith
        have hq : 0 ≤ M * sphereArea d / ((d : ℝ) - σ) + 1 := by positivity
        rw [← ENNReal.ofReal_mul hB0, ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add zero_le_one (mul_nonneg hB0 hq)]

/-- **Row bounds (`ℝ≥0∞`-valued), whole-space port of `row_bounds_real`**, `0 ≤ s < d`.
For `ρ` a probability density with `ρ ≤ M` and a nonnegative kernel `q` with
`q(x,y) ≤ A (1 + rieszWeight s (x-y))` off the diagonal, for every `x`:
`∫ (q(x,y) - L)_+ dμ(y) ≤ C_a L^{1-d/σ}` (`L > 0`) and `∫ min(q(x,y), L)² dμ(y) ≤ C_b ψ₂(L)`
(`L ≥ 1`), `μ = ρ dx`, `σ = sigmaOf d s`.  The constants depend only on `(d, s, A, M)`. -/
theorem wr3_row_bounds_real (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (A M : ℝ) :
    ∃ Ca Cb : ℝ, 0 ≤ Ca ∧ 0 ≤ Cb ∧
      ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ q : Euc d → Euc d → ℝ, (∀ x y, 0 ≤ q x y) →
      (∀ x y, x ≠ y → q x y ≤ A * (1 + HRS.Whole.rieszWeight s (x - y))) → ∀ x : Euc d,
        (∀ L : ℝ, 0 < L →
          ∫⁻ y, ENNReal.ofReal (max (q x y - L) 0) ∂(HRS.Whole.withDensityReal ρ)
            ≤ ENNReal.ofReal (Ca * L ^ (1 - (d : ℝ) / HRS.WeakRef.sigmaOf d s))) ∧
        (∀ L : ℝ, 1 ≤ L →
          ∫⁻ y, ENNReal.ofReal ((min (q x y) L) ^ 2) ∂(HRS.Whole.withDensityReal ρ)
            ≤ ENNReal.ofReal (Cb * HRS.WeakRef.psi2 d s L)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨C₁, C₂, hC₁, hC₂, hlev1, hlev2⟩ := wr3_kernel_levels_real hd hs0 hsd
  have hσ0 := HRS.WeakRef.sigmaOf_pos hd hs0
  have hσd := HRS.WeakRef.sigmaOf_lt hd hsd
  set σ := HRS.WeakRef.sigmaOf d s with hσ
  set e : ℝ := 1 - (d : ℝ) / σ with he
  have he0 : e < 0 := by
    have : 1 < (d : ℝ) / σ := by rw [lt_div_iff₀ hσ0]; linarith
    rw [he]; linarith
  set Ā : ℝ := max A 1 with hĀ
  have hĀ1 : 1 ≤ Ā := le_max_right _ _
  have hĀ0 : 0 < Ā := by linarith
  have hAĀ : A ≤ Ā := le_max_left _ _
  set M' : ℝ := max M 0 with hM'def
  have hM'0 : 0 ≤ M' := le_max_right _ _
  set B : ℝ := 1 + 4 / (d : ℝ) with hB
  have hB1 : 1 ≤ B := by
    have : 0 ≤ 4 / (d : ℝ) := by positivity
    rw [hB]; linarith
  have hsA := HRS.Whole.Q34.sphereArea_nonneg hd
  have hdσ : 0 < (d : ℝ) - σ := by linarith
  set cW : ℝ := 1 + B * (M' * sphereArea d / ((d : ℝ) - σ) + 1) with hcW
  have hcW0 : 0 ≤ cW := by rw [hcW]; positivity
  have hCa0 : 0 ≤ M' * Ā * C₁ * Ā ^ (-e) := by positivity
  have hCa0' : 0 ≤ Ā * cW * (2 * Ā) ^ (-e) := by positivity
  refine ⟨max (M' * Ā * C₁ * Ā ^ (-e)) (Ā * cW * (2 * Ā) ^ (-e)),
    Ā ^ 2 * (M' * C₂ + (1 + B) ^ 2), le_max_of_le_left hCa0, by positivity, ?_⟩
  intro ρ hρ hM q hq0 hqA x
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hM' : ∀ y, ρ y ≤ M' := fun y => (hM y).trans (le_max_left _ _)
  have hae := wr3_ae_ne hd ρ x
  have hW1 : ∀ z : Euc d, 1 ≤ 1 + HRS.Whole.rieszWeight s z := fun z => by
    linarith [wr3_rieszWeight_nonneg (d := d) s z]
  have hpt : ∀ y, y ≠ x → q x y ≤ Ā * (1 + HRS.Whole.rieszWeight s (x - y)) := by
    intro y hy
    have h1 := hqA x y (Ne.symm hy)
    exact h1.trans (mul_le_mul_of_nonneg_right hAĀ (by linarith [hW1 (x - y)]))
  have hWm : Measurable fun z : Euc d => 1 + HRS.Whole.rieszWeight s z :=
    measurable_const.add (wr3_measurable_rieszWeight s)
  constructor
  · intro L hL
    by_cases hbig : 2 * Ā ≤ L
    · have hLA : 2 ≤ L / Ā := by rw [le_div_iff₀ hĀ0]; linarith
      set H : Euc d → ℝ≥0∞ := fun z =>
        ENNReal.ofReal Ā * ENNReal.ofReal (max (1 + HRS.Whole.rieszWeight s z - L / Ā) 0) with hH
      have hHm : Measurable H :=
        measurable_const.mul (ENNReal.measurable_ofReal.comp
          ((hWm.sub_const _).max measurable_const))
      calc ∫⁻ y, ENNReal.ofReal (max (q x y - L) 0) ∂μ
          ≤ ∫⁻ y, H (x - y) ∂μ := by
            refine lintegral_mono_ae ?_
            filter_upwards [hae] with y hy
            have h1 := hpt y hy
            show ENNReal.ofReal (max (q x y - L) 0) ≤ ENNReal.ofReal Ā *
              ENNReal.ofReal (max (1 + HRS.Whole.rieszWeight s (x - y) - L / Ā) 0)
            rw [← ENNReal.ofReal_mul hĀ0.le]
            refine ENNReal.ofReal_le_ofReal (max_le ?_
              (mul_nonneg hĀ0.le (le_max_right _ _)))
            have h2 : Ā * (1 + HRS.Whole.rieszWeight s (x - y) - L / Ā)
                ≤ Ā * max (1 + HRS.Whole.rieszWeight s (x - y) - L / Ā) 0 :=
              mul_le_mul_of_nonneg_left (le_max_left _ _) hĀ0.le
            have e2 : Ā * (1 + HRS.Whole.rieszWeight s (x - y) - L / Ā)
                = Ā * (1 + HRS.Whole.rieszWeight s (x - y)) - L := by field_simp
            linarith
        _ ≤ ENNReal.ofReal M' * ∫⁻ z, H z :=
            HRS.Whole.Q34.lintegral_conv_le hρ hM' H hHm x
        _ = ENNReal.ofReal M' * (ENNReal.ofReal Ā *
              ∫⁻ z, ENNReal.ofReal (max (1 + HRS.Whole.rieszWeight s z - L / Ā) 0)) := by
            rw [hH, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal M' * (ENNReal.ofReal Ā * ENNReal.ofReal (C₁ * (L / Ā) ^ e)) := by
            gcongr
            exact hlev1 _ hLA
        _ = ENNReal.ofReal (M' * Ā * C₁ * (L / Ā) ^ e) := by
            rw [← ENNReal.ofReal_mul hĀ0.le, ← ENNReal.ofReal_mul hM'0]
            congr 1; ring
        _ ≤ _ := by
            refine ENNReal.ofReal_le_ofReal ?_
            have h1 : (L / Ā) ^ e = L ^ e * Ā ^ (-e) := by
              rw [Real.div_rpow hL.le hĀ0.le, Real.rpow_neg hĀ0.le, div_eq_mul_inv]
            rw [h1]
            have h2 : 0 ≤ L ^ e := Real.rpow_nonneg hL.le _
            calc M' * Ā * C₁ * (L ^ e * Ā ^ (-e)) = (M' * Ā * C₁ * Ā ^ (-e)) * L ^ e := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) h2
    · push Not at hbig
      calc ∫⁻ y, ENNReal.ofReal (max (q x y - L) 0) ∂μ
          ≤ ∫⁻ y, ENNReal.ofReal Ā *
              ENNReal.ofReal (1 + HRS.Whole.rieszWeight s (x - y)) ∂μ := by
            refine lintegral_mono_ae ?_
            filter_upwards [hae] with y hy
            rw [← ENNReal.ofReal_mul hĀ0.le]
            refine ENNReal.ofReal_le_ofReal (max_le ?_
              (mul_nonneg hĀ0.le (by linarith [hW1 (x - y)])))
            linarith [hpt y hy]
        _ = ENNReal.ofReal Ā *
              ∫⁻ y, ENNReal.ofReal (1 + HRS.Whole.rieszWeight s (x - y)) ∂μ :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal Ā * ENNReal.ofReal cW := by
            gcongr
            exact wr3_lintegral_W_row hd hs0 hsd hρ hM' x
        _ = ENNReal.ofReal (Ā * cW) := (ENNReal.ofReal_mul hĀ0.le).symm
        _ ≤ _ := by
            refine ENNReal.ofReal_le_ofReal ?_
            have hle : (2 * Ā) ^ e ≤ L ^ e :=
              Real.rpow_le_rpow_of_nonpos hL hbig.le he0.le
            calc Ā * cW = (Ā * cW * (2 * Ā) ^ (-e)) * (2 * Ā) ^ e := by
                  rw [mul_assoc, ← Real.rpow_add (by positivity)]; simp
              _ ≤ _ := mul_le_mul (le_max_right _ _) hle (Real.rpow_nonneg (by positivity) _)
                  (le_max_of_le_left hCa0)
  · intro L hL
    have hL0 : 0 < L := by linarith
    set G : Euc d → ℝ≥0∞ := fun z =>
      ENNReal.ofReal ((min (1 + HRS.Whole.rieszWeight s z) L) ^ 2) with hG
    have hGm : Measurable G :=
      ENNReal.measurable_ofReal.comp ((hWm.min measurable_const).pow_const 2)
    set G1 : Euc d → ℝ≥0∞ := (ball (0 : Euc d) 1).indicator G with hG1
    have hG1m : Measurable G1 := hGm.indicator measurableSet_ball
    have hfar : ∀ z, G z ≤ G1 z + ENNReal.ofReal ((1 + B) ^ 2) := by
      intro z
      by_cases hz : z ∈ ball (0 : Euc d) 1
      · rw [hG1, indicator_of_mem hz]; exact le_self_add
      · rw [hG1, indicator_of_notMem hz, zero_add]
        have hz1 : 1 ≤ ‖z‖ := by
          have : ¬ ‖z‖ < 1 := by simpa [mem_ball_zero_iff] using hz
          exact not_lt.1 this
        have h1 := wr3_rieszWeight_le hd (s := s) z
        have h2 : ‖z‖ ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hz1 (by linarith)
        have h3 : HRS.Whole.rieszWeight s z ≤ B := by
          refine h1.trans ?_
          have : B * ‖z‖ ^ (-σ) ≤ B * 1 := mul_le_mul_of_nonneg_left h2 (by linarith)
          linarith
        refine ENNReal.ofReal_le_ofReal ?_
        have h0 : 0 ≤ min (1 + HRS.Whole.rieszWeight s z) L :=
          le_min (by linarith [hW1 z]) hL0.le
        have h4 : min (1 + HRS.Whole.rieszWeight s z) L ≤ 1 + B :=
          (min_le_left _ _).trans (by linarith)
        nlinarith
    have hψ := wr3_one_le_psi2 hd hs0 hL
    calc ∫⁻ y, ENNReal.ofReal ((min (q x y) L) ^ 2) ∂μ
        ≤ ∫⁻ y, ENNReal.ofReal (Ā ^ 2) * G (x - y) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae] with y hy
          have h1 := hpt y hy
          show ENNReal.ofReal ((min (q x y) L) ^ 2) ≤ ENNReal.ofReal (Ā ^ 2) *
            ENNReal.ofReal ((min (1 + HRS.Whole.rieszWeight s (x - y)) L) ^ 2)
          rw [← ENNReal.ofReal_mul (sq_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h2 : min (q x y) L ≤ Ā * min (1 + HRS.Whole.rieszWeight s (x - y)) L := by
            rw [mul_min_of_nonneg _ _ hĀ0.le]
            exact le_min ((min_le_left _ _).trans h1)
              ((min_le_right _ _).trans (le_mul_of_one_le_left hL0.le hĀ1))
          have h3 : 0 ≤ min (q x y) L := le_min (hq0 x y) hL0.le
          calc (min (q x y) L) ^ 2 ≤ (Ā * min (1 + HRS.Whole.rieszWeight s (x - y)) L) ^ 2 :=
                pow_le_pow_left₀ h3 h2 2
            _ = Ā ^ 2 * (min (1 + HRS.Whole.rieszWeight s (x - y)) L) ^ 2 := by ring
      _ = ENNReal.ofReal (Ā ^ 2) * ∫⁻ y, G (x - y) ∂μ :=
          lintegral_const_mul _ (hGm.comp (measurable_const.sub measurable_id))
      _ ≤ ENNReal.ofReal (Ā ^ 2) *
            ∫⁻ y, (G1 (x - y) + ENNReal.ofReal ((1 + B) ^ 2)) ∂μ := by
          exact mul_le_mul' le_rfl (lintegral_mono fun y => hfar _)
      _ = ENNReal.ofReal (Ā ^ 2) *
            (∫⁻ y, G1 (x - y) ∂μ + ENNReal.ofReal ((1 + B) ^ 2)) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ ENNReal.ofReal (Ā ^ 2) *
            (ENNReal.ofReal M' * (∫⁻ z, G1 z) + ENNReal.ofReal ((1 + B) ^ 2)) := by
          exact mul_le_mul' le_rfl (add_le_add
            (HRS.Whole.Q34.lintegral_conv_le hρ hM' G1 hG1m x) le_rfl)
      _ ≤ ENNReal.ofReal (Ā ^ 2) * (ENNReal.ofReal M' *
            ENNReal.ofReal (C₂ * HRS.WeakRef.psi2 d s L) + ENNReal.ofReal ((1 + B) ^ 2)) := by
          have hI : ∫⁻ z, G1 z ≤ ENNReal.ofReal (C₂ * HRS.WeakRef.psi2 d s L) := by
            rw [hG1, lintegral_indicator measurableSet_ball]
            exact hlev2 L hL
          exact mul_le_mul' le_rfl (add_le_add (mul_le_mul' le_rfl hI) le_rfl)
      _ = ENNReal.ofReal (Ā ^ 2 * (M' * (C₂ * HRS.WeakRef.psi2 d s L) + (1 + B) ^ 2)) := by
          have hψ0 : 0 ≤ HRS.WeakRef.psi2 d s L := by linarith
          rw [← ENNReal.ofReal_mul hM'0, ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul (sq_nonneg _)]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : (1 + B) ^ 2 ≤ (1 + B) ^ 2 * HRS.WeakRef.psi2 d s L :=
            le_mul_of_one_le_right (sq_nonneg _) hψ
          have h2 : M' * (C₂ * HRS.WeakRef.psi2 d s L) + (1 + B) ^ 2
              ≤ (M' * C₂ + (1 + B) ^ 2) * HRS.WeakRef.psi2 d s L := by nlinarith
          calc Ā ^ 2 * (M' * (C₂ * HRS.WeakRef.psi2 d s L) + (1 + B) ^ 2)
              ≤ Ā ^ 2 * ((M' * C₂ + (1 + B) ^ 2) * HRS.WeakRef.psi2 d s L) :=
                mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
            _ = _ := by ring

end HRS.MS.Wr
