/-
# HRS.Equilibrium.MarginalKernel -- kernel estimates for Proposition 4.2 (EQ-02, full-law half)

Pure real-analysis estimates on the torus for the periodic Riesz kernel `g = periodicRiesz d s`
(`0 ≤ s < d`, `d ≥ 2`), used in `HRS.Equilibrium.MarginalDensity`:

* `tail_volume`: `|{g ≥ t}| ≤ K t^{-d/s}` for `s > 0`;
* the layer-cake integrals `I_λ = ∫ min(g₊², g₊/λ)` (`≲ N δ_N` at `λ = β/N`);
* the convolution estimate `A:eq:convolution` in the form needed (`‖|g| * |f|‖_{L²} ≤ C δ_N` for
  `|f| ≤ M`, `‖f‖₁ ≲ √(δ_N/N)`), by value truncation `g₊ = min(g₊,H) + (g₊ - H)₊`;
* uniform smallness of `g * f` for `‖f‖₁ → 0`, `|f| ≤ M`.
-/
import HRS.Equilibrium.PoleCavity
import HRS.Kernel.ResponseAux

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace MarginalAux

open PoleCavityAux KernelAux KernelAux2

variable {d : ℕ} {s : ℝ}

/-- Tail of the distribution of `g`: `|{g ≥ t}| ≤ K t^{-d/s}` for `0 < s < d`. -/
theorem tail_volume (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 < t →
      (volume : Measure (Torus d)) {z | t ≤ periodicRiesz d s z} ≤
        ENNReal.ofReal (K / t ^ ((d : ℝ) / s)) := by
  have hd0 : 0 < d := by omega
  obtain ⟨A, hA1, hA⟩ := gPlus_envelope hd hs0 hsd 0
  have hA0 : 0 < A := by linarith
  refine ⟨2 ^ d * A ^ ((d : ℝ) / s), by positivity, fun t ht => ?_⟩
  have hmeasS : MeasurableSet {z : Torus d | t ≤ periodicRiesz d s z} :=
    measurableSet_le measurable_const (measurable_periodicRiesz hd hs0.le hsd)
  set r : ℝ := (A / t) ^ (1 / s) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by positivity) _
  have hsub : ((fun y : Fin d → ℝ => boxPt y) ⁻¹' {z : Torus d | t ≤ periodicRiesz d s z}) ∩ Box d ⊆
      Metric.closedBall (0 : Fin d → ℝ) r := by
    rintro y ⟨hyS, hyB⟩
    rw [mem_closedBall_zero_iff]
    by_cases hy : y = 0
    · rw [hy, norm_zero]; exact hr0
    · have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy
      have h1 : t ≤ A * ‖y‖ ^ (-s) := by
        have := hA y hyB hy
        simp only [gPlus, add_zero] at this
        exact hyS.trans this
      have h2 : ‖y‖ ^ s ≤ A / t := by
        rw [Real.rpow_neg hypos.le] at h1
        have hp : 0 < ‖y‖ ^ s := Real.rpow_pos_of_pos hypos _
        rw [le_div_iff₀ ht]
        have := (le_div_iff₀ hp).1 (show t ≤ A / ‖y‖ ^ s by simpa [div_eq_mul_inv] using h1)
        linarith
      calc ‖y‖ = (‖y‖ ^ s) ^ (1 / s) := by
            rw [← Real.rpow_mul hypos.le, mul_one_div_cancel hs0.ne', Real.rpow_one]
        _ ≤ r := Real.rpow_le_rpow (Real.rpow_nonneg hypos.le _) h2 (by positivity)
  calc (volume : Measure (Torus d)) {z | t ≤ periodicRiesz d s z}
      = ∫⁻ z, ({z : Torus d | t ≤ periodicRiesz d s z}).indicator 1 z := by
        rw [lintegral_indicator_one hmeasS]
    _ = ∫⁻ y in Box d, ({z : Torus d | t ≤ periodicRiesz d s z}).indicator (1 : Torus d → ℝ≥0∞) (boxPt y) :=
        lintegral_torus_box _
    _ = (volume.restrict (Box d)) ((fun y : Fin d → ℝ => boxPt y) ⁻¹' {z : Torus d | t ≤ periodicRiesz d s z}) := by
        rw [← lintegral_indicator_one (hmeasS.preimage (continuous_boxPt d).measurable)]
        rfl
    _ = volume (((fun y : Fin d → ℝ => boxPt y) ⁻¹' {z : Torus d | t ≤ periodicRiesz d s z}) ∩ Box d) := by
        rw [Measure.restrict_apply' (measurableSet_Box d)]
    _ ≤ volume (Metric.closedBall (0 : Fin d → ℝ) r) := measure_mono hsub
    _ = ENNReal.ofReal ((2 * r) ^ d) := by rw [Real.volume_pi_closedBall _ hr0]; simp
    _ = ENNReal.ofReal (2 ^ d * A ^ ((d : ℝ) / s) / t ^ ((d : ℝ) / s)) := by
        congr 1
        have : r ^ d = (A / t) ^ ((d : ℝ) / s) := by
          rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          congr 1; field_simp
        rw [mul_pow, this, Real.div_rpow hA0.le ht.le]; field_simp

/-! ### Layer-cake integrals for a tail `min 1 (K / t^p)`, `1 < p < 2` -/

theorem int1_bound_p (K H p : ℝ) (hK : 0 < K) (hH : 0 < H) (hp1 : 1 < p) (hp2 : p < 2) :
    ∫⁻ t in Set.Ioi (0 : ℝ), min 1 (ENNReal.ofReal (K / t ^ p)) *
        ENNReal.ofReal (if t ≤ H then 2 * t else 0) ≤
      ENNReal.ofReal (2 * K / (2 - p) * H ^ (2 - p)) := by
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ), min 1 (ENNReal.ofReal (K / t ^ p)) *
        ENNReal.ofReal (if t ≤ H then 2 * t else 0) ≤
      (Set.Ioc (0 : ℝ) H).indicator (fun t => ENNReal.ofReal (2 * K * t ^ (1 - p))) t := by
    intro t ht
    have ht0 : 0 < t := ht
    by_cases h : t ≤ H
    · simp only [h, ↓reduceIte]
      rw [Set.indicator_of_mem (show t ∈ Set.Ioc (0 : ℝ) H from ⟨ht0, h⟩)]
      calc _ ≤ ENNReal.ofReal (K / t ^ p) * ENNReal.ofReal (2 * t) := by
            gcongr; exact min_le_right _ _
        _ = ENNReal.ofReal (K / t ^ p * (2 * t)) :=
            (ENNReal.ofReal_mul (by positivity)).symm
        _ = _ := by
            congr 1
            have : t ^ (1 - p) = t / t ^ p := by
              rw [Real.rpow_sub ht0, Real.rpow_one]
            rw [this]; field_simp
    · simp only [h, ↓reduceIte]; simp
  have hint : IntervalIntegrable (fun t : ℝ => 2 * K * t ^ (1 - p)) volume 0 H :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).const_mul _
  calc _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ), (Set.Ioc (0 : ℝ) H).indicator
          (fun t => ENNReal.ofReal (2 * K * t ^ (1 - p))) t := setLIntegral_mono' measurableSet_Ioi hpt
    _ = ∫⁻ t in Set.Ioc (0 : ℝ) H, ENNReal.ofReal (2 * K * t ^ (1 - p)) :=
        lintegral_Ioi_indicator_Ioc _ _ le_rfl _
    _ = ENNReal.ofReal (∫ t in (0 : ℝ)..H, 2 * K * t ^ (1 - p)) :=
        lintegral_Ioc_ofReal 0 H hH.le _ hint (fun t ht => by
          have := ht.1; positivity)
    _ = _ := by
        congr 1
        rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
        have h1 : 1 - p + 1 = 2 - p := by ring
        rw [h1, Real.zero_rpow (by linarith)]
        have : (2 - p) ≠ 0 := by linarith
        field_simp
        ring

theorem int2_bound_p (K H p : ℝ) (hK : 0 < K) (hH : 0 < H) (hp1 : 1 < p) :
    ∫⁻ t in Set.Ioi (0 : ℝ), min 1 (ENNReal.ofReal (K / t ^ p)) *
        ENNReal.ofReal (if H ≤ t then 1 else 0) ≤ ENNReal.ofReal (K / (p - 1) * H ^ (1 - p)) := by
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ), min 1 (ENNReal.ofReal (K / t ^ p)) *
        ENNReal.ofReal (if H ≤ t then 1 else 0) ≤
      (Set.Ici H).indicator (fun t => ENNReal.ofReal (K * t ^ (-p))) t := by
    intro t ht
    have ht0 : 0 < t := ht
    by_cases h : H ≤ t
    · simp only [h, ↓reduceIte]
      rw [Set.indicator_of_mem (show t ∈ Set.Ici H from h)]
      calc _ ≤ ENNReal.ofReal (K / t ^ p) * ENNReal.ofReal 1 := by gcongr; exact min_le_right _ _
        _ = ENNReal.ofReal (K * t ^ (-p)) := by
          rw [ENNReal.ofReal_one, mul_one, Real.rpow_neg ht0.le, div_eq_mul_inv]
    · simp only [h, ↓reduceIte]; simp
  calc _ ≤ ∫⁻ t in Set.Ioi (0 : ℝ), (Set.Ici H).indicator
          (fun t => ENNReal.ofReal (K * t ^ (-p))) t := setLIntegral_mono' measurableSet_Ioi hpt
    _ = ∫⁻ t in Set.Ici H, ENNReal.ofReal (K * t ^ (-p)) := by
        rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
        congr 2
        ext t
        simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi]
        exact ⟨fun h => h.1, fun h => ⟨h, lt_of_lt_of_le hH h⟩⟩
    _ = ∫⁻ t in Set.Ioi H, ENNReal.ofReal (K * t ^ (-p)) :=
        setLIntegral_congr Ioi_ae_eq_Ici.symm
    _ = ENNReal.ofReal (∫ t in Set.Ioi H, K * t ^ (-p)) := by
        rw [ofReal_integral_eq_lintegral_ofReal]
        · exact (integrableOn_Ioi_rpow_of_lt (by linarith) hH).const_mul K
        · exact (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht =>
            mul_nonneg hK.le (Real.rpow_nonneg (lt_trans hH ht).le _))
    _ = ENNReal.ofReal (K / (p - 1) * H ^ (1 - p)) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hH]
        congr 1
        have h1 : -p + 1 = 1 - p := by ring
        rw [h1]
        have : (1 - p) ≠ 0 := by linarith
        have : p - 1 ≠ 0 := by linarith
        field_simp
        ring

/-! ### Layer cake for `g₊ = max g 0` -/

theorem measurable_rieszPos (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    Measurable (rieszPos d s) :=
  (measurable_periodicRiesz hd hs0 hsd).max measurable_const

theorem volume_le_one_torus (S : Set (Torus d)) : (volume : Measure (Torus d)) S ≤ 1 := by
  calc (volume : Measure (Torus d)) S ≤ volume Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := measure_univ

theorem tail_min (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 < t →
      (volume : Measure (Torus d)) {z | t ≤ rieszPos d s z} ≤
        min 1 (ENNReal.ofReal (K / t ^ ((d : ℝ) / s))) := by
  obtain ⟨K, hK, h⟩ := tail_volume hd hs0 hsd
  refine ⟨K, hK, fun t ht => le_min (volume_le_one_torus _) ?_⟩
  refine le_trans (measure_mono fun z hz => ?_) (h t ht)
  simp only [Set.mem_setOf_eq, rieszPos] at hz ⊢
  rcases le_max_iff.1 hz with h1 | h1
  · exact h1
  · exact absurd h1 (not_le.2 ht)

theorem lintegral_Phi_rieszPos (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) {K : ℝ}
    (hK : ∀ t : ℝ, 0 < t → (volume : Measure (Torus d)) {z | t ≤ rieszPos d s z} ≤
        min 1 (ENNReal.ofReal (K / t ^ ((d : ℝ) / s))))
    (γ : ℝ → ℝ) (hγ : Measurable γ) (hγ0 : ∀ t, 0 < t → 0 ≤ γ t)
    (hγi : ∀ t > 0, IntervalIntegrable γ volume 0 t) (Φ : ℝ → ℝ)
    (hΦ : ∀ h, 0 ≤ h → Φ h ≤ ∫ t in (0 : ℝ)..h, γ t) :
    ∫⁻ z, ENNReal.ofReal (Φ (rieszPos d s z)) ≤
      ∫⁻ t in Set.Ioi (0 : ℝ), min 1 (ENNReal.ofReal (K / t ^ ((d : ℝ) / s))) *
        ENNReal.ofReal (γ t) :=
  lintegral_le_tail (volume : Measure (Torus d)) (rieszPos d s) (measurable_rieszPos hd hs0.le hsd)
    (fun z => le_max_right _ _) γ hγ hγ0 hγi
    (fun t => min 1 (ENNReal.ofReal (K / t ^ ((d : ℝ) / s)))) hK Φ hΦ

/-- `∫ min(g₊, H)²`, `d/2 < s < d`. -/
theorem lintegral_min_sq_super (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hs2 : (d : ℝ) / 2 < s) :
    ∃ K : ℝ, 0 < K ∧ ∀ H : ℝ, 0 < H →
      ∫⁻ z, ENNReal.ofReal (min (rieszPos d s z) H ^ 2) ≤
        ENNReal.ofReal (K * H ^ (2 - (d : ℝ) / s)) := by
  obtain ⟨K, hK, ht⟩ := tail_min hd hs0 hsd
  have hp1 : 1 < (d : ℝ) / s := by rw [lt_div_iff₀ hs0]; linarith
  have hp2 : (d : ℝ) / s < 2 := by rw [div_lt_iff₀ hs0]; linarith
  refine ⟨2 * K / (2 - (d : ℝ) / s), by
    have : 0 < 2 - (d : ℝ) / s := by linarith
    positivity, fun H hH => ?_⟩
  refine (lintegral_Phi_rieszPos hd hs0 hsd ht _ (measurable_g1 H) (fun t ht0 => by
    split_ifs <;> linarith) (fun b hb => integrable_g1 H hH b hb) _
    (fun h hh => hPhi1 H hH h hh)).trans ?_
  exact (int1_bound_p K H _ hK hH hp1 hp2).trans (le_of_eq (by congr 1))

/-- `∫ (g₊ - min(g₊,H))`, `d/2 < s < d`. -/
theorem lintegral_excess_super (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hs2 : (d : ℝ) / 2 < s) :
    ∃ K : ℝ, 0 < K ∧ ∀ H : ℝ, 0 < H →
      ∫⁻ z, ENNReal.ofReal (rieszPos d s z - min (rieszPos d s z) H) ≤
        ENNReal.ofReal (K * H ^ (1 - (d : ℝ) / s)) := by
  obtain ⟨K, hK, ht⟩ := tail_min hd hs0 hsd
  have hp1 : 1 < (d : ℝ) / s := by rw [lt_div_iff₀ hs0]; linarith
  refine ⟨K / ((d : ℝ) / s - 1), by
    have : 0 < (d : ℝ) / s - 1 := by linarith
    positivity, fun H hH => ?_⟩
  refine (lintegral_Phi_rieszPos hd hs0 hsd ht _ (measurable_g2 H) (fun t ht0 => by
    split_ifs <;> norm_num) (fun b hb => integrable_g2 H b hb) _
    (fun h hh => hPhi2 H hH h hh)).trans ?_
  exact (int2_bound_p K H _ hK hH hp1).trans (le_of_eq (by congr 1))

/-- `∫ min(g₊, H)²`, `s = d/2`, `H ≥ 1`. -/
theorem lintegral_min_sq_crit (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ H : ℝ, 1 ≤ H →
      ∫⁻ z, ENNReal.ofReal (min (rieszPos d s z) H ^ 2) ≤
        ENNReal.ofReal (1 + 2 * K * Real.log H) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hcrit]; positivity
  have hsd : s < d := by rw [hcrit]; linarith
  obtain ⟨K, hK, ht⟩ := tail_min hd hs0 hsd
  have hp : (d : ℝ) / s = 2 := by rw [hcrit]; field_simp
  refine ⟨K, hK, fun H hH => ?_⟩
  have hH0 : 0 < H := by linarith
  refine (lintegral_Phi_rieszPos hd hs0 hsd ht _ (measurable_g1 H) (fun t ht0 => by
    split_ifs <;> linarith) (fun b hb => integrable_g1 H hH0 b hb) _
    (fun h hh => hPhi1 H hH0 h hh)).trans ?_
  rw [hp]
  simpa using int1_bound K H hK hH

/-- `∫ (g₊ - min(g₊,H))`, `s = d/2`, `H > 0`. -/
theorem lintegral_excess_crit (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ H : ℝ, 0 < H →
      ∫⁻ z, ENNReal.ofReal (rieszPos d s z - min (rieszPos d s z) H) ≤
        ENNReal.ofReal (K / H) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hcrit]; positivity
  have hsd : s < d := by rw [hcrit]; linarith
  obtain ⟨K, hK, ht⟩ := tail_min hd hs0 hsd
  have hp : (d : ℝ) / s = 2 := by rw [hcrit]; field_simp
  refine ⟨K, hK, fun H hH => ?_⟩
  refine (lintegral_Phi_rieszPos hd hs0 hsd ht _ (measurable_g2 H) (fun t ht0 => by
    split_ifs <;> norm_num) (fun b hb => integrable_g2 H b hb) _
    (fun h hh => hPhi2 H hH h hh)).trans ?_
  rw [hp]
  simpa using int2_bound K H hK hH

/-- `g₊² ∈ L¹` for `s < d/2` (`g ∈ L²`). -/
theorem lintegral_sq_sub (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs2 : s < (d : ℝ) / 2) :
    ∫⁻ z : Torus d, ENNReal.ofReal (rieszPos d s z ^ 2) < ∞ := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  have hd0 : 0 < d := by omega
  rcases hs0.eq_or_lt with h0 | hpos
  · subst h0
    have h1 := lintegral_exp_abs_log_lt_top (d := d) hd (a := 1) one_pos (by linarith)
    refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := 2)) h1)
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun z => ?_
    rw [← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hu : 0 ≤ rieszPos d 0 z := le_max_right _ _
    have hle : rieszPos d 0 z ≤ |periodicRiesz d 0 z| := by
      unfold rieszPos
      exact max_le (le_abs_self _) (abs_nonneg _)
    have h2 : rieszPos d 0 z ^ 2 / 2 ≤ Real.exp (rieszPos d 0 z) := by
      have := Real.quadratic_le_exp_of_nonneg hu
      nlinarith [Real.add_one_le_exp (rieszPos d 0 z)]
    have h3 : Real.exp (rieszPos d 0 z) ≤ Real.exp (1 * |periodicRiesz d 0 z|) :=
      Real.exp_le_exp.2 (by linarith)
    linarith
  · obtain ⟨A, hA1, hA⟩ := gPlus_envelope hd hpos hsd 0
    rw [lintegral_torus_box]
    have hint := (integrableOn_Box_rpow hd0 (α := 2 * s) (by linarith)).const_mul (A ^ 2)
    refine lt_of_le_of_lt ?_ hint.lintegral_lt_top
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_of_ae (ae_ne_pi hd0), ae_restrict_mem (measurableSet_Box d)] with y hy hyB
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hA y hyB hy
    simp only [gPlus, add_zero] at h1
    have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy
    have hp0 : 0 ≤ A * ‖y‖ ^ (-s) := by positivity
    have h2 : rieszPos d s (boxPt y) ≤ A * ‖y‖ ^ (-s) := max_le h1 hp0
    have h3 : 0 ≤ rieszPos d s (boxPt y) := le_max_right _ _
    calc rieszPos d s (boxPt y) ^ 2 ≤ (A * ‖y‖ ^ (-s)) ^ 2 := by gcongr
      _ = A ^ 2 * ‖y‖ ^ (-(2 * s)) := by
        rw [mul_pow, ← Real.rpow_natCast (‖y‖ ^ (-s)) 2, ← Real.rpow_mul hypos.le]
        congr 2; push_cast; ring

/-! ### Young-type inequalities (Schur / Cauchy-Schwarz) -/

theorem ennreal_add_sq_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 2) (by norm_num)
  simp only [ENNReal.rpow_two] at h
  have : (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) = 2 := by norm_num
  rwa [this] at h

/-- `‖k * F‖₂ ≤ ‖k‖₁ ‖F‖₂`. -/
theorem young1 (k : Torus d → ℝ≥0∞) (F : Torus d → ℝ) (hk : Measurable k) (hF : Measurable F) :
    ∫⁻ x, (∫⁻ y, k (x - y) * ‖F y‖ₑ) ^ 2 ≤ (∫⁻ y, k y) ^ 2 * ∫⁻ y, ‖F y‖ₑ ^ 2 := by
  set N : ℝ≥0∞ := ∫⁻ y, k y with hN
  have hga : ∀ x, Measurable fun y : Torus d => k (x - y) := fun x =>
    hk.comp (measurable_const.sub measurable_id)
  have h1 : ∀ x, (∫⁻ y, k (x - y) * ‖F y‖ₑ) ^ 2 ≤ N * ∫⁻ y, k (x - y) * ‖F y‖ₑ ^ 2 := by
    intro x
    have := ResponseAux.cs_lintegral (volume : Measure (Torus d)) (a := fun y => k (x - y))
      (b := fun y => ‖F y‖ₑ) (hga x).aemeasurable hF.enorm.aemeasurable
    rw [ResponseAux.lintegral_sub_left (fun z => k z) x] at this
    exact this
  have hm : Measurable fun p : Torus d × Torus d => k (p.1 - p.2) * ‖F p.2‖ₑ ^ 2 :=
    (hk.comp (measurable_fst.sub measurable_snd)).mul ((hF.comp measurable_snd).enorm.pow_const 2)
  calc ∫⁻ x, (∫⁻ y, k (x - y) * ‖F y‖ₑ) ^ 2
      ≤ ∫⁻ x, N * ∫⁻ y, k (x - y) * ‖F y‖ₑ ^ 2 := lintegral_mono h1
    _ = N * ∫⁻ x, ∫⁻ y, k (x - y) * ‖F y‖ₑ ^ 2 := by
        rw [lintegral_const_mul]
        exact Measurable.lintegral_prod_right' hm
    _ = N * ∫⁻ y, ∫⁻ x, k (x - y) * ‖F y‖ₑ ^ 2 := by
        rw [lintegral_lintegral_swap]
        exact hm.aemeasurable
    _ = N * ∫⁻ y, N * ‖F y‖ₑ ^ 2 := by
        congr 1
        refine lintegral_congr fun y => ?_
        have hm' : Measurable fun x : Torus d => k (x - y) :=
          hk.comp (measurable_id.sub measurable_const)
        rw [lintegral_mul_const _ hm', ResponseAux.lintegral_sub_right (fun z => k z) y]
    _ = _ := by
        rw [lintegral_const_mul _ (hF.enorm.pow_const 2)]
        ring

/-- `‖k * F‖₂ ≤ ‖k‖₂ ‖F‖₁`. -/
theorem young2 (k : Torus d → ℝ≥0∞) (F : Torus d → ℝ) (hk : Measurable k) (hF : Measurable F) :
    ∫⁻ x, (∫⁻ y, k (x - y) * ‖F y‖ₑ) ^ 2 ≤ (∫⁻ y, ‖F y‖ₑ) ^ 2 * ∫⁻ y, k y ^ 2 := by
  set N : ℝ≥0∞ := ∫⁻ y, ‖F y‖ₑ with hN
  have hga : ∀ x, Measurable fun y : Torus d => k (x - y) := fun x =>
    hk.comp (measurable_const.sub measurable_id)
  have h1 : ∀ x, (∫⁻ y, k (x - y) * ‖F y‖ₑ) ^ 2 ≤ N * ∫⁻ y, ‖F y‖ₑ * k (x - y) ^ 2 := by
    intro x
    have := ResponseAux.cs_lintegral (volume : Measure (Torus d)) (a := fun y => ‖F y‖ₑ)
      (b := fun y => k (x - y)) hF.enorm.aemeasurable (hga x).aemeasurable
    simp_rw [mul_comm (k (x - _)) (‖F _‖ₑ)]
    exact this
  have hm : Measurable fun p : Torus d × Torus d => ‖F p.2‖ₑ * k (p.1 - p.2) ^ 2 :=
    ((hF.comp measurable_snd).enorm).mul ((hk.comp (measurable_fst.sub measurable_snd)).pow_const 2)
  calc ∫⁻ x, (∫⁻ y, k (x - y) * ‖F y‖ₑ) ^ 2
      ≤ ∫⁻ x, N * ∫⁻ y, ‖F y‖ₑ * k (x - y) ^ 2 := lintegral_mono h1
    _ = N * ∫⁻ x, ∫⁻ y, ‖F y‖ₑ * k (x - y) ^ 2 := by
        rw [lintegral_const_mul]
        exact Measurable.lintegral_prod_right' hm
    _ = N * ∫⁻ y, ∫⁻ x, ‖F y‖ₑ * k (x - y) ^ 2 := by
        rw [lintegral_lintegral_swap]
        exact hm.aemeasurable
    _ = N * ∫⁻ y, ‖F y‖ₑ * ∫⁻ y, k y ^ 2 := by
        congr 1
        refine lintegral_congr fun y => ?_
        have hm' : Measurable fun x : Torus d => k (x - y) ^ 2 :=
          (hk.comp (measurable_id.sub measurable_const)).pow_const 2
        rw [lintegral_const_mul _ hm', ResponseAux.lintegral_sub_right (fun z => k z ^ 2) y]
    _ = _ := by
        rw [lintegral_mul_const _ hF.enorm]
        ring

/-- Truncation: `‖g‖ₑ ≤ k₁ + k₂` gives
`‖g * f‖₂² ≤ 2 ‖k₁‖₂² ‖f‖₁² + 2 ‖k₂‖₁² ‖f‖₂²`. -/
theorem conv_sq_le_split (g f : Torus d → ℝ) (k₁ k₂ : Torus d → ℝ≥0∞) (hk₁ : Measurable k₁)
    (hk₂ : Measurable k₂) (hf : Measurable f) (hgk : ∀ z, ‖g z‖ₑ ≤ k₁ z + k₂ z) :
    ∫⁻ x, (∫⁻ y, ‖g (x - y)‖ₑ * ‖f y‖ₑ) ^ 2 ≤
      2 * ((∫⁻ y, ‖f y‖ₑ) ^ 2 * ∫⁻ y, k₁ y ^ 2) + 2 * ((∫⁻ y, k₂ y) ^ 2 * ∫⁻ y, ‖f y‖ₑ ^ 2) := by
  have hpt : ∀ x, (∫⁻ y, ‖g (x - y)‖ₑ * ‖f y‖ₑ) ^ 2 ≤
      2 * ((∫⁻ y, k₁ (x - y) * ‖f y‖ₑ) ^ 2) + 2 * ((∫⁻ y, k₂ (x - y) * ‖f y‖ₑ) ^ 2) := by
    intro x
    have h1 : ∫⁻ y, ‖g (x - y)‖ₑ * ‖f y‖ₑ ≤
        (∫⁻ y, k₁ (x - y) * ‖f y‖ₑ) + ∫⁻ y, k₂ (x - y) * ‖f y‖ₑ := by
      rw [← lintegral_add_left]
      · refine lintegral_mono fun y => ?_
        rw [← add_mul]
        exact mul_le_mul' (hgk _) le_rfl
      · exact (hk₁.comp (measurable_const.sub measurable_id)).mul hf.enorm
    calc _ ≤ ((∫⁻ y, k₁ (x - y) * ‖f y‖ₑ) + ∫⁻ y, k₂ (x - y) * ‖f y‖ₑ) ^ 2 := by gcongr
      _ ≤ 2 * ((∫⁻ y, k₁ (x - y) * ‖f y‖ₑ) ^ 2 + (∫⁻ y, k₂ (x - y) * ‖f y‖ₑ) ^ 2) :=
          ennreal_add_sq_le _ _
      _ = _ := by ring
  have m1 : Measurable fun x => (∫⁻ y, k₁ (x - y) * ‖f y‖ₑ) ^ 2 := by
    refine Measurable.pow_const ?_ _
    exact Measurable.lintegral_prod_right' (f := fun p : Torus d × Torus d => k₁ (p.1 - p.2) * ‖f p.2‖ₑ)
      ((hk₁.comp (measurable_fst.sub measurable_snd)).mul ((hf.comp measurable_snd).enorm))
  calc ∫⁻ x, (∫⁻ y, ‖g (x - y)‖ₑ * ‖f y‖ₑ) ^ 2
      ≤ ∫⁻ x, (2 * ((∫⁻ y, k₁ (x - y) * ‖f y‖ₑ) ^ 2) + 2 * ((∫⁻ y, k₂ (x - y) * ‖f y‖ₑ) ^ 2)) :=
        lintegral_mono hpt
    _ = 2 * (∫⁻ x, (∫⁻ y, k₁ (x - y) * ‖f y‖ₑ) ^ 2) + 2 * (∫⁻ x, (∫⁻ y, k₂ (x - y) * ‖f y‖ₑ) ^ 2) := by
        rw [lintegral_add_left (m1.const_mul 2), lintegral_const_mul _ m1, lintegral_const_mul']
        exact ENNReal.ofNat_ne_top
    _ ≤ _ := by
        gcongr
        · exact young2 k₁ f hk₁ hf
        · exact young1 k₂ f hk₂ hf

/-! ### The convolution estimate -/

/-- `|g| ≤ B + min(g₊, H) + (g₊ - min(g₊,H))`. -/
theorem enorm_riesz_le (B H : ℝ) (hB0 : 0 ≤ B) (hB : ∀ z : Torus d, -B ≤ periodicRiesz d s z)
    (hH : 0 < H) (z : Torus d) :
    ‖periodicRiesz d s z‖ₑ ≤ ENNReal.ofReal (B + min (rieszPos d s z) H) +
      ENNReal.ofReal (rieszPos d s z - min (rieszPos d s z) H) := by
  have hmn0 : 0 ≤ min (rieszPos d s z) H := le_min (le_max_right _ _) hH.le
  have hmn1 : min (rieszPos d s z) H ≤ rieszPos d s z := min_le_left _ _
  rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
  rw [Real.enorm_eq_ofReal_abs]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := hB z
  have h2 : periodicRiesz d s z ≤ rieszPos d s z := le_max_left _ _
  have h3 : 0 ≤ rieszPos d s z := le_max_right _ _
  have h4 := min_le_left (rieszPos d s z) H
  rw [abs_le]
  constructor <;> linarith

theorem conv_core (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ z : Torus d, -B ≤ periodicRiesz d s z) {H : ℝ} (hH : 0 < H) {f : Torus d → ℝ}
    (hf : Measurable f) {M η : ℝ} (hM : ∀ y, |f y| ≤ M) (hη0 : 0 ≤ η)
    (hη : ∫⁻ y, ‖f y‖ₑ ≤ ENNReal.ofReal η) {a1 a2 : ℝ} (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2)
    (hmin : ∫⁻ z, ENNReal.ofReal (min (rieszPos d s z) H ^ 2) ≤ ENNReal.ofReal a1)
    (hex : ∫⁻ z, ENNReal.ofReal (rieszPos d s z - min (rieszPos d s z) H) ≤ ENNReal.ofReal a2) :
    ∫⁻ x, (∫⁻ y, ‖periodicRiesz d s (x - y)‖ₑ * ‖f y‖ₑ) ^ 2 ≤
      ENNReal.ofReal (2 * (η ^ 2 * (2 * B ^ 2 + 2 * a1)) + 2 * (a2 ^ 2 * (M * η))) := by
  have hgm := measurable_periodicRiesz hd hs0 hsd
  have hpm := measurable_rieszPos hd hs0 hsd
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hmn : Measurable fun z => min (rieszPos d s z) H := hpm.min measurable_const
  have hk1 : Measurable fun z : Torus d => ENNReal.ofReal (B + min (rieszPos d s z) H) :=
    ENNReal.measurable_ofReal.comp (measurable_const.add hmn)
  have hk2 : Measurable fun z : Torus d => ENNReal.ofReal (rieszPos d s z - min (rieszPos d s z) H) :=
    ENNReal.measurable_ofReal.comp (hpm.sub hmn)
  refine (conv_sq_le_split _ f _ _ hk1 hk2 hf (enorm_riesz_le B H hB0 hB hH)).trans ?_
  -- the three factors
  have e1 : ∫⁻ y, ENNReal.ofReal (B + min (rieszPos d s y) H) ^ 2 ≤
      ENNReal.ofReal (2 * B ^ 2 + 2 * a1) := by
    calc ∫⁻ y, ENNReal.ofReal (B + min (rieszPos d s y) H) ^ 2
        ≤ ∫⁻ y, (ENNReal.ofReal (2 * B ^ 2) + 2 * ENNReal.ofReal (min (rieszPos d s y) H ^ 2)) := by
          refine lintegral_mono fun y => ?_
          have hm0 : 0 ≤ min (rieszPos d s y) H := le_min (le_max_right _ _) hH.le
          rw [← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_ofNat 2,
            ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          nlinarith [sq_nonneg (B - min (rieszPos d s y) H)]
      _ = ENNReal.ofReal (2 * B ^ 2) + 2 * ∫⁻ y, ENNReal.ofReal (min (rieszPos d s y) H ^ 2) := by
          rw [lintegral_add_left measurable_const, lintegral_const, lintegral_const_mul]
          · simp
          · exact (ENNReal.measurable_ofReal.comp (hmn.pow_const 2))
      _ ≤ ENNReal.ofReal (2 * B ^ 2) + 2 * ENNReal.ofReal a1 := by gcongr
      _ = ENNReal.ofReal (2 * B ^ 2 + 2 * a1) := by
          rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have e2 : ∫⁻ y, ‖f y‖ₑ ^ 2 ≤ ENNReal.ofReal (M * η) := by
    calc ∫⁻ y, ‖f y‖ₑ ^ 2 ≤ ∫⁻ y, ENNReal.ofReal M * ‖f y‖ₑ := by
          refine lintegral_mono fun y => ?_
          rw [pow_two]
          refine mul_le_mul' ?_ le_rfl
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (hM y)
      _ = ENNReal.ofReal M * ∫⁻ y, ‖f y‖ₑ := lintegral_const_mul _ hf.enorm
      _ ≤ ENNReal.ofReal M * ENNReal.ofReal η := by gcongr
      _ = ENNReal.ofReal (M * η) := (ENNReal.ofReal_mul hM0).symm
  calc 2 * ((∫⁻ y, ‖f y‖ₑ) ^ 2 * ∫⁻ y, ENNReal.ofReal (B + min (rieszPos d s y) H) ^ 2) +
        2 * ((∫⁻ y, ENNReal.ofReal (rieszPos d s y - min (rieszPos d s y) H)) ^ 2 *
          ∫⁻ y, ‖f y‖ₑ ^ 2)
      ≤ 2 * (ENNReal.ofReal η ^ 2 * ENNReal.ofReal (2 * B ^ 2 + 2 * a1)) +
        2 * (ENNReal.ofReal a2 ^ 2 * ENNReal.ofReal (M * η)) := by gcongr
    _ = ENNReal.ofReal (2 * (η ^ 2 * (2 * B ^ 2 + 2 * a1)) + 2 * (a2 ^ 2 * (M * η))) := by
        rw [← ENNReal.ofReal_pow hη0, ← ENNReal.ofReal_pow ha2, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]

theorem excess_le_sq (a H : ℝ) (hH : 0 < H) : a - min a H ≤ a ^ 2 / (4 * H) := by
  rw [le_div_iff₀ (by positivity)]
  rcases le_total a H with h | h
  · rw [min_eq_left h]; nlinarith [sq_nonneg a]
  · rw [min_eq_right h]; nlinarith [sq_nonneg (a - 2 * H)]

theorem rieszB (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : Torus d, -B ≤ periodicRiesz d s z := by
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) hd hs0 hsd
  exact ⟨max B 0, le_max_right _ _, fun z => (neg_le_neg (le_max_left _ _)).trans (hB z)⟩

theorem conv_L2_sub (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs2 : s < (d : ℝ) / 2) (M K0 : ℝ) (hM : 0 ≤ M)
    (hK0 : 0 ≤ K0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ f : Torus d → ℝ, Measurable f → (∀ y, |f y| ≤ M) →
      ∫⁻ y, ‖f y‖ₑ ≤ ENNReal.ofReal (K0 * Real.sqrt (deltaN d s N / N)) →
      ∫⁻ x, (∫⁻ y, ‖periodicRiesz d s (x - y)‖ₑ * ‖f y‖ₑ) ^ 2 ≤
        ENNReal.ofReal ((C * deltaN d s N) ^ 2) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  obtain ⟨B, hB0, hB⟩ := rieszB hd hs0 hsd
  have hfin := lintegral_sq_sub hd hs0 hs2
  set Kg : ℝ := (∫⁻ z : Torus d, ENNReal.ofReal (rieszPos d s z ^ 2)).toReal with hKg
  have hKg0 : 0 ≤ Kg := ENNReal.toReal_nonneg
  have hKgle : ∫⁻ z : Torus d, ENNReal.ofReal (rieszPos d s z ^ 2) ≤ ENNReal.ofReal Kg := by
    rw [hKg, ENNReal.ofReal_toReal hfin.ne]
  refine ⟨Real.sqrt (2 * K0 ^ 2 * (2 * B ^ 2 + 2 * Kg) + 2 * (Kg / 4) ^ 2 * M * K0), Real.sqrt_nonneg _,
    fun N hN f hf hM' hη => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN0 : (0 : ℝ) < N := by linarith
  have hδ : deltaN d s N = (N : ℝ)⁻¹ := by unfold deltaN; rw [if_pos hs2]
  rw [hδ] at hη ⊢
  have hsq : Real.sqrt ((N : ℝ)⁻¹ / N) = (N : ℝ)⁻¹ := by
    rw [show ((N : ℝ)⁻¹ / N) = ((N : ℝ)⁻¹) ^ 2 by field_simp, Real.sqrt_sq (by positivity)]
  rw [hsq] at hη
  set H : ℝ := Real.sqrt N with hH
  have hHpos : 0 < H := Real.sqrt_pos.2 hN0
  have hH1 : 1 ≤ H := by rw [hH]; exact Real.one_le_sqrt.2 hN1
  have hmin : ∫⁻ z, ENNReal.ofReal (min (rieszPos d s z) H ^ 2) ≤ ENNReal.ofReal Kg := by
    refine le_trans (lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_) hKgle
    have h0 : 0 ≤ min (rieszPos d s z) H := le_min (le_max_right _ _) hHpos.le
    exact pow_le_pow_left₀ h0 (min_le_left _ _) 2
  have hex : ∫⁻ z, ENNReal.ofReal (rieszPos d s z - min (rieszPos d s z) H) ≤
      ENNReal.ofReal (Kg / (4 * H)) := by
    calc ∫⁻ z, ENNReal.ofReal (rieszPos d s z - min (rieszPos d s z) H)
        ≤ ∫⁻ z, ENNReal.ofReal (rieszPos d s z ^ 2) / ENNReal.ofReal (4 * H) := by
          refine lintegral_mono fun z => ?_
          rw [← ENNReal.ofReal_div_of_pos (by positivity)]
          exact ENNReal.ofReal_le_ofReal (excess_le_sq _ _ hHpos)
      _ = (∫⁻ z, ENNReal.ofReal (rieszPos d s z ^ 2)) / ENNReal.ofReal (4 * H) := by
          simp_rw [div_eq_mul_inv]
          rw [lintegral_mul_const']
          exact ENNReal.inv_ne_top.2 (by simp; positivity)
      _ ≤ ENNReal.ofReal Kg / ENNReal.ofReal (4 * H) := by gcongr
      _ = ENNReal.ofReal (Kg / (4 * H)) := (ENNReal.ofReal_div_of_pos (by positivity)).symm
  have hcore := conv_core hd hs0 hsd B hB0 hB hHpos hf hM' (η := K0 * (N : ℝ)⁻¹)
    (by positivity) hη (a1 := Kg) (a2 := Kg / (4 * H)) hKg0 (by positivity) hmin hex
  refine hcore.trans (ENNReal.ofReal_le_ofReal ?_)
  have hH2 : H ^ 2 = N := Real.sq_sqrt hN0.le
  have hk : (Kg / (4 * H)) ^ 2 = (Kg / 4) ^ 2 * (N : ℝ)⁻¹ := by
    rw [div_pow, mul_pow, hH2]; field_simp
  have key : ∀ q n : ℝ, 0 ≤ q → (Real.sqrt q * n) ^ 2 = q * n ^ 2 := fun q n hq => by
    rw [mul_pow, Real.sq_sqrt hq]
  rw [key _ _ (by positivity), hk]
  refine le_of_eq ?_
  ring

theorem conv_L2_crit (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (M K0 : ℝ) (hM : 0 ≤ M)
    (hK0 : 0 ≤ K0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ f : Torus d → ℝ, Measurable f → (∀ y, |f y| ≤ M) →
      ∫⁻ y, ‖f y‖ₑ ≤ ENNReal.ofReal (K0 * Real.sqrt (deltaN d s N / N)) →
      ∫⁻ x, (∫⁻ y, ‖periodicRiesz d s (x - y)‖ₑ * ‖f y‖ₑ) ^ 2 ≤
        ENNReal.ofReal ((C * deltaN d s N) ^ 2) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hcrit]; positivity
  have hsd : s < d := by rw [hcrit]; linarith
  obtain ⟨B, hB0, hB⟩ := rieszB hd hs0 hsd
  obtain ⟨K1, hK1, h1⟩ := lintegral_min_sq_crit hd hcrit
  obtain ⟨K2, hK2, h2⟩ := lintegral_excess_crit hd hcrit
  refine ⟨Real.sqrt (2 * K0 ^ 2 * (2 * B ^ 2 + 2 * (1 + K1)) + 2 * K2 ^ 2 * M * K0), Real.sqrt_nonneg _,
    fun N hN f hf hM' hη => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN0 : (0 : ℝ) < N := by linarith
  have hnl : ¬ s < (d : ℝ) / 2 := by rw [hcrit]; exact lt_irrefl _
  set L : ℝ := 1 + Real.log N with hL
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hL1 : 1 ≤ L := by rw [hL]; linarith
  have hδ : deltaN d s N = (N : ℝ)⁻¹ * L := by
    unfold deltaN
    rw [if_neg hnl, if_pos hcrit, Real.log_mul (Real.exp_pos 1).ne' hN0.ne', Real.log_exp]
  rw [hδ] at hη ⊢
  set x : ℝ := (N : ℝ)⁻¹ with hx
  have hx0 : 0 < x := by positivity
  have hsq : Real.sqrt (x * L / N) = x * Real.sqrt L := by
    rw [show x * L / N = x ^ 2 * L by rw [hx]; field_simp, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hx0.le]
  rw [hsq] at hη
  set sL : ℝ := Real.sqrt L with hsL
  have hsL0 : 0 ≤ sL := Real.sqrt_nonneg _
  have hsLL : sL ^ 2 = L := Real.sq_sqrt (by linarith)
  have hsL1 : 1 ≤ sL := by rw [hsL]; exact Real.one_le_sqrt.2 hL1
  have hsLle : sL ≤ L := by nlinarith
  set H : ℝ := Real.sqrt N with hH
  have hHpos : 0 < H := Real.sqrt_pos.2 hN0
  have hH1 : 1 ≤ H := by rw [hH]; exact Real.one_le_sqrt.2 hN1
  have hH2 : H ^ 2 = N := Real.sq_sqrt hN0.le
  have hlogH : Real.log H = Real.log N / 2 := by rw [hH, Real.log_sqrt hN0.le]
  have hmin := h1 H hH1
  have hex := h2 H hHpos
  have ha1 : 0 ≤ 1 + 2 * K1 * Real.log H := by
    have := Real.log_nonneg hH1; positivity
  have hcore := conv_core hd hs0 hsd B hB0 hB hHpos hf hM' (η := K0 * (x * sL))
    (by positivity) hη (a1 := 1 + 2 * K1 * Real.log H) (a2 := K2 / H) ha1 (by positivity) hmin hex
  refine hcore.trans (ENNReal.ofReal_le_ofReal ?_)
  have key : ∀ q n : ℝ, 0 ≤ q → (Real.sqrt q * n) ^ 2 = q * n ^ 2 := fun q n hq => by
    rw [mul_pow, Real.sq_sqrt hq]
  rw [key _ _ (by positivity)]
  have hk : (K2 / H) ^ 2 = K2 ^ 2 * x := by
    rw [div_pow, hH2, hx]; field_simp
  have ha1' : 1 + 2 * K1 * Real.log H ≤ (1 + K1) * L := by
    rw [hlogH]; rw [hL]; nlinarith
  have hη2 : (K0 * (x * sL)) ^ 2 = K0 ^ 2 * x ^ 2 * L := by
    rw [mul_pow, mul_pow, hsLL]; ring
  rw [hk, hη2]
  have hx2 : 0 ≤ x ^ 2 := by positivity
  have hLL : L ≤ L ^ 2 := by nlinarith
  have hsLL2 : sL ≤ L ^ 2 := hsLle.trans hLL
  -- main estimate
  have e1 : 2 * (K0 ^ 2 * x ^ 2 * L * (2 * B ^ 2 + 2 * (1 + 2 * K1 * Real.log H))) ≤
      2 * (K0 ^ 2 * x ^ 2 * L * (2 * B ^ 2 + 2 * ((1 + K1) * L))) := by
    gcongr
  have e2 : 2 * (K2 ^ 2 * x * (M * (K0 * (x * sL)))) ≤ 2 * (K2 ^ 2 * M * K0) * (x ^ 2 * L ^ 2) := by
    have : 2 * (K2 ^ 2 * x * (M * (K0 * (x * sL)))) = 2 * (K2 ^ 2 * M * K0) * (x ^ 2 * sL) := by ring
    rw [this]
    gcongr
  have e3 : 2 * (K0 ^ 2 * x ^ 2 * L * (2 * B ^ 2 + 2 * ((1 + K1) * L))) ≤
      2 * K0 ^ 2 * (2 * B ^ 2 + 2 * (1 + K1)) * (x ^ 2 * L ^ 2) := by
    have : 2 * (K0 ^ 2 * x ^ 2 * L * (2 * B ^ 2 + 2 * ((1 + K1) * L))) =
        2 * K0 ^ 2 * (x ^ 2) * (2 * B ^ 2 * L + 2 * (1 + K1) * L ^ 2) := by ring
    rw [this]
    have h3 : 2 * B ^ 2 * L + 2 * (1 + K1) * L ^ 2 ≤ (2 * B ^ 2 + 2 * (1 + K1)) * L ^ 2 := by
      nlinarith [sq_nonneg B, mul_nonneg (sq_nonneg B) (sub_nonneg.2 hLL)]
    calc 2 * K0 ^ 2 * x ^ 2 * (2 * B ^ 2 * L + 2 * (1 + K1) * L ^ 2)
        ≤ 2 * K0 ^ 2 * x ^ 2 * ((2 * B ^ 2 + 2 * (1 + K1)) * L ^ 2) := by gcongr
      _ = _ := by ring
  have : (2 * K0 ^ 2 * (2 * B ^ 2 + 2 * (1 + K1)) + 2 * K2 ^ 2 * M * K0) * (x * L) ^ 2 =
      2 * K0 ^ 2 * (2 * B ^ 2 + 2 * (1 + K1)) * (x ^ 2 * L ^ 2) +
        2 * (K2 ^ 2 * M * K0) * (x ^ 2 * L ^ 2) := by ring
  rw [this]
  linarith

theorem conv_L2_super (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hs2 : (d : ℝ) / 2 < s) (M K0 : ℝ)
    (hM : 0 ≤ M) (hK0 : 0 ≤ K0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ f : Torus d → ℝ, Measurable f → (∀ y, |f y| ≤ M) →
      ∫⁻ y, ‖f y‖ₑ ≤ ENNReal.ofReal (K0 * Real.sqrt (deltaN d s N / N)) →
      ∫⁻ x, (∫⁻ y, ‖periodicRiesz d s (x - y)‖ₑ * ‖f y‖ₑ) ^ 2 ≤
        ENNReal.ofReal ((C * deltaN d s N) ^ 2) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨B, hB0, hB⟩ := rieszB hd hs0.le hsd
  obtain ⟨K1, hK1, h1⟩ := lintegral_min_sq_super hd hs0 hsd hs2
  obtain ⟨K2, hK2, h2⟩ := lintegral_excess_super hd hs0 hsd hs2
  set p : ℝ := (d : ℝ) / s with hp
  have hp1 : 1 < p := by rw [hp, lt_div_iff₀ hs0]; linarith
  have hp2 : p < 2 := by rw [hp, div_lt_iff₀ hs0]; linarith
  refine ⟨Real.sqrt (2 * K0 ^ 2 * (2 * B ^ 2 + 2 * K1) + 2 * K2 ^ 2 * M * K0), Real.sqrt_nonneg _,
    fun N hN f hf hM' hη => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN0 : (0 : ℝ) < N := by linarith
  have hn1 : ¬ s < (d : ℝ) / 2 := not_lt.2 hs2.le
  have hn2 : ¬ s = (d : ℝ) / 2 := hs2.ne'
  have hδ : deltaN d s N = (N : ℝ) ^ (1 - p) := by
    unfold deltaN; rw [if_neg hn1, if_neg hn2]
  rw [hδ] at hη ⊢
  have hsq : Real.sqrt ((N : ℝ) ^ (1 - p) / N) = (N : ℝ) ^ (-p / 2) := by
    have : (N : ℝ) ^ (1 - p) / N = ((N : ℝ) ^ (-p / 2)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, show (1 - p) = (-p) + 1 by ring,
        Real.rpow_add hN0, Real.rpow_one]
      have : (-p / 2) * ((2 : ℕ) : ℝ) = -p := by push_cast; ring
      rw [this]; field_simp
    rw [this, Real.sqrt_sq (by positivity)]
  rw [hsq] at hη
  set H : ℝ := (N : ℝ) ^ ((1 : ℝ) / 2) with hH
  have hHpos : 0 < H := by positivity
  have hmin := h1 H hHpos
  have hex := h2 H hHpos
  have hH2p : H ^ (2 - p) = (N : ℝ) ^ ((2 - p) / 2) := by
    rw [hH, ← Real.rpow_mul hN0.le]; congr 1; ring
  have hH1p : H ^ (1 - p) = (N : ℝ) ^ ((1 - p) / 2) := by
    rw [hH, ← Real.rpow_mul hN0.le]; congr 1; ring
  rw [hH2p] at hmin
  rw [hH1p] at hex
  have ha1 : 0 ≤ K1 * (N : ℝ) ^ ((2 - p) / 2) := by positivity
  have ha2 : 0 ≤ K2 * (N : ℝ) ^ ((1 - p) / 2) := by positivity
  have hcore := conv_core hd hs0.le hsd B hB0 hB hHpos hf hM' (η := K0 * (N : ℝ) ^ (-p / 2))
    (by positivity) hη ha1 ha2 hmin hex
  refine hcore.trans (ENNReal.ofReal_le_ofReal ?_)
  have key : ∀ q n : ℝ, 0 ≤ q → (Real.sqrt q * n) ^ 2 = q * n ^ 2 := fun q n hq => by
    rw [mul_pow, Real.sq_sqrt hq]
  rw [key _ _ (by positivity)]
  -- exponent bookkeeping
  have sq_rp : ∀ a : ℝ, ((N : ℝ) ^ a) ^ 2 = (N : ℝ) ^ (2 * a) := fun a => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  have mul_rp : ∀ a b : ℝ, (N : ℝ) ^ a * (N : ℝ) ^ b = (N : ℝ) ^ (a + b) := fun a b =>
    (Real.rpow_add hN0 a b).symm
  have mono : ∀ a b : ℝ, a ≤ b → (N : ℝ) ^ a ≤ (N : ℝ) ^ b := fun a b h =>
    Real.rpow_le_rpow_of_exponent_le hN1 h
  have t1 : (N : ℝ) ^ (-p) ≤ (N : ℝ) ^ (2 - 2 * p) := mono _ _ (by linarith)
  have t2 : (N : ℝ) ^ (-p) * (N : ℝ) ^ ((2 - p) / 2) ≤ (N : ℝ) ^ (2 - 2 * p) := by
    rw [mul_rp]; exact mono _ _ (by linarith)
  have t3 : (N : ℝ) ^ (1 - p) * (N : ℝ) ^ (-p / 2) ≤ (N : ℝ) ^ (2 - 2 * p) := by
    rw [mul_rp]; exact mono _ _ (by linarith)
  have eη : (K0 * (N : ℝ) ^ (-p / 2)) ^ 2 = K0 ^ 2 * (N : ℝ) ^ (-p) := by
    rw [mul_pow, sq_rp]; congr 2; ring
  have ea2 : (K2 * (N : ℝ) ^ ((1 - p) / 2)) ^ 2 = K2 ^ 2 * (N : ℝ) ^ (1 - p) := by
    rw [mul_pow, sq_rp]; congr 2; ring
  have eδ : ((N : ℝ) ^ (1 - p)) ^ 2 = (N : ℝ) ^ (2 - 2 * p) := by
    rw [sq_rp]; congr 1; ring
  rw [eη, ea2, eδ]
  have hP0 : 0 ≤ (N : ℝ) ^ (-p) := by positivity
  have hP1 : 0 ≤ (N : ℝ) ^ (2 - 2 * p) := by positivity
  have hr1 : 0 ≤ (N : ℝ) ^ ((2 - p) / 2) := by positivity
  have hr2 : 0 ≤ (N : ℝ) ^ (-p / 2) := by positivity
  have hr3 : 0 ≤ (N : ℝ) ^ (1 - p) := by positivity
  have f1 : 2 * (K0 ^ 2 * (N : ℝ) ^ (-p) * (2 * B ^ 2 + 2 * (K1 * (N : ℝ) ^ ((2 - p) / 2)))) ≤
      2 * K0 ^ 2 * (2 * B ^ 2 + 2 * K1) * (N : ℝ) ^ (2 - 2 * p) := by
    have : 2 * (K0 ^ 2 * (N : ℝ) ^ (-p) * (2 * B ^ 2 + 2 * (K1 * (N : ℝ) ^ ((2 - p) / 2)))) =
        2 * K0 ^ 2 * (2 * B ^ 2 * (N : ℝ) ^ (-p) + 2 * K1 * ((N : ℝ) ^ (-p) * (N : ℝ) ^ ((2 - p) / 2))) := by
      ring
    rw [this]
    have : 2 * K0 ^ 2 * (2 * B ^ 2 + 2 * K1) * (N : ℝ) ^ (2 - 2 * p) =
        2 * K0 ^ 2 * (2 * B ^ 2 * (N : ℝ) ^ (2 - 2 * p) + 2 * K1 * (N : ℝ) ^ (2 - 2 * p)) := by ring
    rw [this]
    gcongr
  have f2 : 2 * (K2 ^ 2 * (N : ℝ) ^ (1 - p) * (M * (K0 * (N : ℝ) ^ (-p / 2)))) ≤
      2 * K2 ^ 2 * M * K0 * (N : ℝ) ^ (2 - 2 * p) := by
    have : 2 * (K2 ^ 2 * (N : ℝ) ^ (1 - p) * (M * (K0 * (N : ℝ) ^ (-p / 2)))) =
        2 * K2 ^ 2 * M * K0 * ((N : ℝ) ^ (1 - p) * (N : ℝ) ^ (-p / 2)) := by ring
    rw [this]
    gcongr
  nlinarith [f1, f2]


/-- **The convolution estimate** `A:eq:convolution` in the form used for the cavity forcing:
`|f| ≤ M`, `‖f‖₁ ≤ K₀ √(δ_N/N)` give `‖|g| * |f|‖_{L²(dx)} ≤ C δ_N`. -/
theorem conv_L2 (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (M K0 : ℝ) (hM : 0 ≤ M) (hK0 : 0 ≤ K0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ f : Torus d → ℝ, Measurable f → (∀ y, |f y| ≤ M) →
      ∫⁻ y, ‖f y‖ₑ ≤ ENNReal.ofReal (K0 * Real.sqrt (deltaN d s N / N)) →
      ∫⁻ x, (∫⁻ y, ‖periodicRiesz d s (x - y)‖ₑ * ‖f y‖ₑ) ^ 2 ≤
        ENNReal.ofReal ((C * deltaN d s N) ^ 2) := by
  rcases lt_trichotomy s ((d : ℝ) / 2) with h | h | h
  · exact conv_L2_sub hd hs0 h M K0 hM hK0
  · exact conv_L2_crit hd h M K0 hM hK0
  · exact conv_L2_super hd (by linarith [show (0 : ℝ) ≤ (d : ℝ) / 2 by positivity]) hsd h M K0 hM hK0

/-! ### The `D_N` integral `∫ min(g₊², H g₊)` -/

theorem min_sq_le_aux (a H : ℝ) (ha : 0 ≤ a) (hH : 0 < H) :
    min (a ^ 2) (H * a) ≤ min a H ^ 2 + H * (a - min a H) := by
  rcases le_total a H with h | h
  · rw [min_eq_left h, sub_self, mul_zero, add_zero]; exact min_le_left _ _
  · rw [min_eq_right h]
    calc min (a ^ 2) (H * a) ≤ H * a := min_le_right _ _
      _ = H ^ 2 + H * (a - H) := by ring

theorem lintegral_min_split (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {H : ℝ} (hH : 0 < H) :
    ∫⁻ z : Torus d, ENNReal.ofReal (min (rieszPos d s z ^ 2) (H * rieszPos d s z)) ≤
      (∫⁻ z : Torus d, ENNReal.ofReal (min (rieszPos d s z) H ^ 2)) +
        ENNReal.ofReal H * ∫⁻ z : Torus d, ENNReal.ofReal (rieszPos d s z - min (rieszPos d s z) H) := by
  have hpm := measurable_rieszPos hd hs0 hsd
  have hmn : Measurable fun z => min (rieszPos d s z) H := hpm.min measurable_const
  calc ∫⁻ z : Torus d, ENNReal.ofReal (min (rieszPos d s z ^ 2) (H * rieszPos d s z))
      ≤ ∫⁻ z : Torus d, (ENNReal.ofReal (min (rieszPos d s z) H ^ 2) +
          ENNReal.ofReal H * ENNReal.ofReal (rieszPos d s z - min (rieszPos d s z) H)) := by
        refine lintegral_mono fun z => ?_
        have h0 : 0 ≤ rieszPos d s z := le_max_right _ _
        have h1 : min (rieszPos d s z) H ≤ rieszPos d s z := min_le_left _ _
        rw [← ENNReal.ofReal_mul hH.le, ← ENNReal.ofReal_add (by positivity)
          (mul_nonneg hH.le (by linarith))]
        exact ENNReal.ofReal_le_ofReal (min_sq_le_aux _ _ h0 hH)
    _ = _ := by
        have hm1 : Measurable fun z : Torus d => ENNReal.ofReal (min (rieszPos d s z) H ^ 2) :=
          ENNReal.measurable_ofReal.comp (hmn.pow_const 2)
        rw [lintegral_add_left hm1, lintegral_const_mul]
        exact ENNReal.measurable_ofReal.comp (hpm.sub hmn)

theorem Ibound_sub (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs2 : s < (d : ℝ) / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, 0 < H →
      ∫⁻ z : Torus d, ENNReal.ofReal (min (rieszPos d s z ^ 2) (H * rieszPos d s z)) ≤ ENNReal.ofReal C := by
  have hfin := lintegral_sq_sub hd hs0 hs2
  refine ⟨(∫⁻ z : Torus d, ENNReal.ofReal (rieszPos d s z ^ 2)).toReal, ENNReal.toReal_nonneg, fun H hH => ?_⟩
  rw [ENNReal.ofReal_toReal hfin.ne]
  exact lintegral_mono fun z => ENNReal.ofReal_le_ofReal (min_le_left _ _)

theorem Ibound_crit (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ H : ℝ, 1 ≤ H →
      ∫⁻ z : Torus d, ENNReal.ofReal (min (rieszPos d s z ^ 2) (H * rieszPos d s z)) ≤
        ENNReal.ofReal (1 + K + 2 * K * Real.log H) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hcrit]; positivity
  have hsd : s < d := by rw [hcrit]; linarith
  obtain ⟨K1, hK1, h1⟩ := lintegral_min_sq_crit hd hcrit
  obtain ⟨K2, hK2, h2⟩ := lintegral_excess_crit hd hcrit
  refine ⟨K1 + K2, by positivity, fun H hH => ?_⟩
  have hH0 : 0 < H := by linarith
  refine (lintegral_min_split hd hs0 hsd hH0).trans ?_
  have hlog := Real.log_nonneg hH
  calc _ ≤ ENNReal.ofReal (1 + 2 * K1 * Real.log H) + ENNReal.ofReal H * ENNReal.ofReal (K2 / H) :=
        add_le_add (h1 H hH) (by gcongr; exact h2 H hH0)
    _ = ENNReal.ofReal ((1 + 2 * K1 * Real.log H) + H * (K2 / H)) := by
        rw [← ENNReal.ofReal_mul hH0.le, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [show H * (K2 / H) = K2 by field_simp]
        nlinarith [mul_nonneg hK2.le hlog, mul_nonneg hK1.le hlog]

theorem Ibound_super (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hs2 : (d : ℝ) / 2 < s) :
    ∃ K : ℝ, 0 < K ∧ ∀ H : ℝ, 0 < H →
      ∫⁻ z : Torus d, ENNReal.ofReal (min (rieszPos d s z ^ 2) (H * rieszPos d s z)) ≤
        ENNReal.ofReal (K * H ^ (2 - (d : ℝ) / s)) := by
  obtain ⟨K1, hK1, h1⟩ := lintegral_min_sq_super hd hs0 hsd hs2
  obtain ⟨K2, hK2, h2⟩ := lintegral_excess_super hd hs0 hsd hs2
  refine ⟨K1 + K2, by positivity, fun H hH => ?_⟩
  refine (lintegral_min_split hd hs0.le hsd hH).trans ?_
  calc _ ≤ ENNReal.ofReal (K1 * H ^ (2 - (d : ℝ) / s)) +
          ENNReal.ofReal H * ENNReal.ofReal (K2 * H ^ (1 - (d : ℝ) / s)) :=
        add_le_add (h1 H hH) (by gcongr; exact h2 H hH)
    _ = ENNReal.ofReal (K1 * H ^ (2 - (d : ℝ) / s) + H * (K2 * H ^ (1 - (d : ℝ) / s))) := by
        rw [← ENNReal.ofReal_mul hH.le, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ = _ := by
        congr 1
        have : H * H ^ (1 - (d : ℝ) / s) = H ^ (2 - (d : ℝ) / s) := by
          calc H * H ^ (1 - (d : ℝ) / s) = H ^ (1 : ℝ) * H ^ (1 - (d : ℝ) / s) := by rw [Real.rpow_one]
            _ = H ^ ((1 : ℝ) + (1 - (d : ℝ) / s)) := (Real.rpow_add hH _ _).symm
            _ = _ := by congr 1; ring
        calc K1 * H ^ (2 - (d : ℝ) / s) + H * (K2 * H ^ (1 - (d : ℝ) / s))
            = K1 * H ^ (2 - (d : ℝ) / s) + K2 * (H * H ^ (1 - (d : ℝ) / s)) := by ring
          _ = _ := by rw [this]; ring

/-- `∫ min(g₊², (N/β) g₊) ≤ C N δ_N`. -/
theorem Ibound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      ∫⁻ z : Torus d, ENNReal.ofReal (min (rieszPos d s z ^ 2) ((N : ℝ) / β * rieszPos d s z)) ≤
        ENNReal.ofReal (C * ((N : ℝ) * deltaN d s N)) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  rcases lt_trichotomy s ((d : ℝ) / 2) with h | h | h
  · obtain ⟨C, hC0, hC⟩ := Ibound_sub hd hs0 h
    refine ⟨C, hC0, fun N hN => ?_⟩
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hδ : (N : ℝ) * deltaN d s N = 1 := by
      unfold deltaN; rw [if_pos h]; field_simp
    rw [hδ, mul_one]
    exact hC _ (by positivity)
  · obtain ⟨K, hK, hI⟩ := Ibound_crit hd h
    refine ⟨1 + K + 2 * K * (1 + |Real.log β|), by positivity, fun N hN => ?_⟩
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    have hN0 : (0 : ℝ) < N := by linarith
    have hnl : ¬ s < (d : ℝ) / 2 := by rw [h]; exact lt_irrefl _
    have hδ : (N : ℝ) * deltaN d s N = 1 + Real.log N := by
      unfold deltaN
      rw [if_neg hnl, if_pos h, Real.log_mul (Real.exp_pos 1).ne' hN0.ne', Real.log_exp]
      field_simp
    set H : ℝ := max 1 ((N : ℝ) / β) with hH
    have hH1 : 1 ≤ H := le_max_left _ _
    have hlogN := Real.log_nonneg hN1
    have hlogH : Real.log H ≤ Real.log N + |Real.log β| := by
      rcases le_total 1 ((N : ℝ) / β) with h1 | h1
      · rw [hH, max_eq_right h1, Real.log_div hN0.ne' hβ.ne']
        have := neg_abs_le (Real.log β); linarith
      · rw [hH, max_eq_left h1, Real.log_one]; positivity
    refine (lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_).trans ((hI H hH1).trans
      (ENNReal.ofReal_le_ofReal ?_))
    · have h0 : 0 ≤ rieszPos d s z := le_max_right _ _
      exact min_le_min le_rfl (mul_le_mul_of_nonneg_right (le_max_right _ _) h0)
    · rw [hδ]
      have hlog0 : 0 ≤ Real.log H := Real.log_nonneg hH1
      have habs := abs_nonneg (Real.log β)
      nlinarith [mul_nonneg hK.le hlogN, mul_nonneg hK.le habs, mul_nonneg hK.le hlog0]
  · have hs0' : 0 < s := by linarith [show (0 : ℝ) ≤ (d : ℝ) / 2 by positivity]
    obtain ⟨K, hK, hI⟩ := Ibound_super hd hs0' hsd h
    set p : ℝ := (d : ℝ) / s with hp
    refine ⟨K * (1 / β) ^ (2 - p), by positivity, fun N hN => ?_⟩
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hn1 : ¬ s < (d : ℝ) / 2 := not_lt.2 h.le
    have hn2 : ¬ s = (d : ℝ) / 2 := h.ne'
    have hδ : (N : ℝ) * deltaN d s N = (N : ℝ) ^ (2 - p) := by
      unfold deltaN; rw [if_neg hn1, if_neg hn2, ← hp]
      calc (N : ℝ) * (N : ℝ) ^ (1 - p) = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (1 - p) := by rw [Real.rpow_one]
        _ = (N : ℝ) ^ ((1 : ℝ) + (1 - p)) := (Real.rpow_add hN0 _ _).symm
        _ = _ := by congr 1; ring
    rw [hδ]
    refine (hI _ (by positivity)).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [Real.div_rpow hN0.le hβ.le, one_div, Real.inv_rpow hβ.le, div_eq_mul_inv]
    ring

/-! ### Uniform smallness of `|g| * |f|` for `‖f‖₁ → 0`, `|f| ≤ M` -/

theorem lintegral_excess_tendsto (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    Tendsto (fun n : ℕ => ∫⁻ z : Torus d, ENNReal.ofReal (rieszPos d s z - min (rieszPos d s z) n))
      atTop (𝓝 0) := by
  have hpm := measurable_rieszPos hd hs0 hsd
  have hgi := KernelAux.integrable_periodicRiesz hd hs0 hsd
  have hbound : ∫⁻ z : Torus d, ENNReal.ofReal (rieszPos d s z) < ∞ := by
    refine lt_of_le_of_lt (lintegral_mono fun z => ?_) hgi.hasFiniteIntegral
    rw [Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold rieszPos
    exact max_le (le_abs_self _) (abs_nonneg _)
  have h := tendsto_lintegral_of_dominated_convergence (μ := (volume : Measure (Torus d)))
    (F := fun (n : ℕ) (z : Torus d) => ENNReal.ofReal (rieszPos d s z - min (rieszPos d s z) n))
    (f := fun _ => 0) (bound := fun z => ENNReal.ofReal (rieszPos d s z))
    (fun n => ENNReal.measurable_ofReal.comp (hpm.sub (hpm.min measurable_const)))
    (fun n => Filter.Eventually.of_forall fun z => by
      refine ENNReal.ofReal_le_ofReal ?_
      have : 0 ≤ min (rieszPos d s z) (n : ℝ) := le_min (le_max_right _ _) n.cast_nonneg
      linarith)
    hbound.ne
    (Filter.Eventually.of_forall fun z => by
      have hev : ∀ᶠ n : ℕ in atTop, rieszPos d s z ≤ (n : ℝ) := by
        obtain ⟨m, hm⟩ := exists_nat_ge (rieszPos d s z)
        filter_upwards [eventually_ge_atTop m] with n hn
        exact hm.trans (by exact_mod_cast hn)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with n hn
      rw [min_eq_left hn, sub_self, ENNReal.ofReal_zero])
  simpa using h

theorem sup_conv_small (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (M : ℝ) (hM : 0 ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ f : Torus d → ℝ, Measurable f → (∀ y, |f y| ≤ M) →
      ∫⁻ y, ‖f y‖ₑ ≤ ENNReal.ofReal δ →
      ∀ x : Torus d, ∫⁻ y, ‖periodicRiesz d s (x - y)‖ₑ * ‖f y‖ₑ ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨B, hB0, hB⟩ := rieszB hd hs0 hsd
  have hpm := measurable_rieszPos hd hs0 hsd
  have hlim := lintegral_excess_tendsto hd hs0 hsd
  have hev : ∀ᶠ n : ℕ in atTop, ∫⁻ z : Torus d, ENNReal.ofReal (rieszPos d s z - min (rieszPos d s z) n) <
      ENNReal.ofReal (ε / (2 * (M + 1))) :=
    (tendsto_order.1 hlim).2 _ (ENNReal.ofReal_pos.2 (by positivity))
  obtain ⟨n, hn⟩ := hev.exists
  set T : ℝ := (n : ℝ) with hT
  have hT0 : 0 ≤ T := n.cast_nonneg
  refine ⟨ε / (2 * (B + T + 1)), by positivity, fun f hf hM' hη x => ?_⟩
  have hgm := measurable_periodicRiesz hd hs0 hsd
  have hpt : ∀ z : Torus d, ‖periodicRiesz d s z‖ₑ ≤ ENNReal.ofReal (B + T) +
      ENNReal.ofReal (rieszPos d s z - min (rieszPos d s z) T) := by
    intro z
    have hmn0 : 0 ≤ min (rieszPos d s z) T := le_min (le_max_right _ _) hT0
    have hmn1 : min (rieszPos d s z) T ≤ rieszPos d s z := min_le_left _ _
    have hmn2 : min (rieszPos d s z) T ≤ T := min_le_right _ _
    have h1 := hB z
    have h2 : periodicRiesz d s z ≤ rieszPos d s z := le_max_left _ _
    have h3 : 0 ≤ rieszPos d s z := le_max_right _ _
    rw [← ENNReal.ofReal_add (by linarith) (by linarith), Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [abs_le]; constructor <;> linarith
  have hmeasx : ∀ k : Torus d → ℝ≥0∞, Measurable k → Measurable fun y => k (x - y) := fun k hk =>
    hk.comp (measurable_const.sub measurable_id)
  calc ∫⁻ y, ‖periodicRiesz d s (x - y)‖ₑ * ‖f y‖ₑ
      ≤ ∫⁻ y, (ENNReal.ofReal (B + T) * ‖f y‖ₑ +
          ENNReal.ofReal (rieszPos d s (x - y) - min (rieszPos d s (x - y)) T) * ENNReal.ofReal M) := by
        refine lintegral_mono fun y => ?_
        calc ‖periodicRiesz d s (x - y)‖ₑ * ‖f y‖ₑ
            ≤ (ENNReal.ofReal (B + T) + ENNReal.ofReal (rieszPos d s (x - y) - min (rieszPos d s (x - y)) T)) *
                ‖f y‖ₑ := by gcongr; exact hpt _
          _ = ENNReal.ofReal (B + T) * ‖f y‖ₑ +
              ENNReal.ofReal (rieszPos d s (x - y) - min (rieszPos d s (x - y)) T) * ‖f y‖ₑ := add_mul _ _ _
          _ ≤ _ := by
            gcongr
            rw [Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_ofReal (hM' y)
    _ = ENNReal.ofReal (B + T) * (∫⁻ y, ‖f y‖ₑ) +
          (∫⁻ y, ENNReal.ofReal (rieszPos d s (x - y) - min (rieszPos d s (x - y)) T)) * ENNReal.ofReal M := by
        have hm1 : Measurable fun y => ENNReal.ofReal (B + T) * ‖f y‖ₑ := hf.enorm.const_mul _
        have hm2 : Measurable fun y : Torus d =>
            ENNReal.ofReal (rieszPos d s (x - y) - min (rieszPos d s (x - y)) T) :=
          hmeasx (fun z => ENNReal.ofReal (rieszPos d s z - min (rieszPos d s z) T))
            (ENNReal.measurable_ofReal.comp (hpm.sub (hpm.min measurable_const)))
        rw [lintegral_add_left hm1, lintegral_const_mul _ hf.enorm, lintegral_mul_const _ hm2]
    _ ≤ ENNReal.ofReal (B + T) * ENNReal.ofReal (ε / (2 * (B + T + 1))) +
          ENNReal.ofReal (ε / (2 * (M + 1))) * ENNReal.ofReal M := by
        gcongr
        rw [ResponseAux.lintegral_sub_left (fun z => ENNReal.ofReal (rieszPos d s z - min (rieszPos d s z) T)) x]
        exact hn.le
    _ = ENNReal.ofReal ((B + T) * (ε / (2 * (B + T + 1))) + ε / (2 * (M + 1)) * M) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ε := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e1 : (B + T) * (ε / (2 * (B + T + 1))) ≤ ε / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_pos hε (show (0 : ℝ) < B + T + 1 by positivity)]
        have e2 : ε / (2 * (M + 1)) * M ≤ ε / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_pos hε (show (0 : ℝ) < M + 1 by positivity)]
        linarith

/-! ### Positivity of the interaction form -/

theorem Kt_nonneg (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : IsProbDensity ρ) {Λ : ℝ} (hΛ : ∀ x, ρ x ≤ Λ) {f : Torus d → ℝ}
    (hf : MemLp f 2 (withDensityReal ρ)) :
    0 ≤ ∫ x, ResponseAux.Kt (periodicRiesz d s) (withDensityReal ρ) f x * f x ∂(withDensityReal ρ) := by
  refine ResponseAux.Kt_form_nonneg hρ hΛ (measurable_periodicRiesz hd hs0 hsd)
    (KernelAux.integrable_periodicRiesz hd hs0 hsd) (rieszCoeff d s) (fun n => ?_)
    (ResponseAux.hcoef_of_funFourierCoeff (fun k => periodicRiesz_fourierCoeff hd hs0 hsd k)) hf
  by_cases hn : n = 0
  · simp [rieszCoeff, hn]
  · exact (rieszCoeff_pos hd hs0 hsd n hn).le

end MarginalAux

end HRS
