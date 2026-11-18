import HRS.MS.SobMul
import HRS.MS.ThCorrSobAux1
import HRS.MP.RdGenSob

/-!
# MOV-A4: the Sobolev algebra property `H^m · H^ρ ⊂ H^ρ` for real indices

Namespace `HRS.MS.MovA4`, helper prefix `mova4_`.  Fourier convention and Sobolev norms are those of
`HRS.PDE.ToolboxRd` (`MemSobolev s u`, `sobolevNormSq s u = ∫ ⟨ξ⟩^{2s} |û|²` with `⟨ξ⟩² = wt ξ`) and
`HRS.Whole.sobolevNormE`.

## Main statements (real `m`, `ρ` with `d/2 < m`, `0 ≤ ρ ≤ m`)

* `mova4_sobolev_algebra`: `∃ C > 0`, for all real functions `u ∈ H^m`, `v ∈ H^ρ`:
  `u v ∈ H^ρ` and `‖u v‖²_{H^ρ} ≤ C² ‖u‖²_{H^m} ‖v‖²_{H^ρ}`.
* `mova4_sobolevNormE_algebra`: the same in `ℝ≥0∞` form,
  `sobolevNormE ρ (u v) ≤ ofReal C * (sobolevNormE m u * sobolevNormE ρ v)`.

`C` depends on `d, m, ρ` only.  No integer-index restriction, no regularity of `u`, `v` beyond membership
(a.e. classes).  Hypotheses `0 ≤ ρ` and `ρ ≤ m` are the natural ones for this estimate; `ρ = 0` and `ρ = m`
are included.  The statement is not vacuous (`MemSobolev` contains `MemLp` and genuine integrability of the
weighted Fourier density, so no junk-value branch is involved).

## Proof

* `mova4_core`: pure `ℝ≥0∞` estimate for the weighted convolution of two measurable functions: Peetre-type
  splitting `⟨ξ⟩^ρ ≲ ⟨η⟩^ρ` (if `⟨ξ-η⟩ ≤ ⟨η⟩`) or `⟨ξ⟩^ρ ≲ ⟨ξ-η⟩^ρ ≤ ⟨ξ-η⟩^m ⟨η⟩^{ρ-m}` (otherwise); the first
  piece is `L¹ * L²` (Young, `sobmul_young`) with `‖û‖_{L¹} ≲ ‖u‖_{H^m}` by Cauchy-Schwarz (`m > d/2`), the second
  piece is `L² * L¹` with `∫ ⟨η⟩^{-m} ⟨η⟩^ρ |v̂| ≲ ‖v‖_{H^ρ}`.
* `mova4_inversion`: a.e. Fourier inversion for `φ ∈ L²` with `φ̂ ∈ L¹` (a.e. version of `rg_inversion`),
  hence `u` is a.e. bounded by `‖û‖_{L¹}` (`mova4_u_bdd`).
* `mova4_prod_L1`, `mova4_prod_L2`: `\widehat{u v} = û ⋆ v̂` a.e., first for `v ∈ L¹ ∩ L²` (Fubini through
  `VectorFourier.integral_fourierIntegral_smul_eq_flip`), then for `v ∈ L²` by approximation by continuous
  compactly supported functions and an a.e. convergent subsequence.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform ContDiff

namespace HRS.MS.MovA4
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.SobMul HRS.MP.RdGen HRS.MS.Tc3

variable {d : ℕ}

theorem mova4_add_sq_le (x y : ℝ≥0∞) : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
  by_cases hx : x = ⊤
  · simp [hx]
  by_cases hy : y = ⊤
  · simp [hy]
  lift x to ℝ≥0 using hx
  lift y to ℝ≥0 using hy
  have : ((x + y) ^ 2 : ℝ≥0) ≤ 2 * (x ^ 2 + y ^ 2) := by
    exact add_sq_le
  exact_mod_cast this

/-- Cauchy-Schwarz in `ℝ≥0∞` -/
theorem mova4_cs2 {f g : Euc d → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, f x * g x) ^ 2 ≤ (∫⁻ x, f x ^ 2) * ∫⁻ x, g x ^ 2 := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure (Euc d))
    Real.HolderConjugate.two_two hf.aemeasurable hg.aemeasurable
  have h2 : (∫⁻ x, f x * g x) ^ 2 ≤ ((∫⁻ x, f x ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) *
      (∫⁻ x, g x ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) ^ 2 := by
    simpa using pow_le_pow_left' h 2
  refine h2.trans (le_of_eq ?_)
  rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (_ ^ _ : ℝ≥0∞), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul]
  simp only [Nat.cast_ofNat, ENNReal.rpow_two]
  norm_num

theorem mova4_wt_add (ξ η : Euc d) : wt ξ ≤ 2 * wt (ξ - η) + 2 * wt η := by
  unfold wt
  have h1 : ‖ξ‖ ≤ ‖ξ - η‖ + ‖η‖ := by simpa using norm_add_le (ξ - η) η
  have h2 : ‖ξ‖ ^ 2 ≤ 2 * ‖ξ - η‖ ^ 2 + 2 * ‖η‖ ^ 2 := by
    nlinarith [sq_nonneg (‖ξ - η‖ - ‖η‖), norm_nonneg ξ]
  have hc : 0 ≤ 4 * Real.pi ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 hc]

/-- Peetre-type: `⟨ξ⟩^{ρ/2} ≤ 4^{ρ/2} · max`. -/
theorem mova4_peetre {ρ : ℝ} (hρ : 0 ≤ ρ) (ξ η : Euc d) {c : ℝ} (h1 : wt (ξ - η) ≤ c)
    (h2 : wt η ≤ c) : wt ξ ^ (ρ / 2) ≤ (4 : ℝ) ^ (ρ / 2) * c ^ (ρ / 2) := by
  have h3 : wt ξ ≤ 4 * c := by linarith [mova4_wt_add ξ η]
  rw [← Real.mul_rpow (by norm_num) (le_trans (wt_pos η).le h2)]
  exact Real.rpow_le_rpow (wt_pos ξ).le h3 (by positivity)

theorem mova4_meas_conv {A B : Euc d → ℝ≥0∞} (hA : Measurable A) (hB : Measurable B) :
    Measurable fun ξ => ∫⁻ η, A (ξ - η) * B η := by
  have := ((hA.comp (measurable_fst.sub measurable_snd)).mul
      (hB.comp measurable_snd)).lintegral_prod_right' (ν := (volume : Measure (Euc d)))
  exact this

/-- swapped Young -/
theorem mova4_young_swap {A B : Euc d → ℝ≥0∞} (hA : Measurable A) (hB : Measurable B) :
    ∫⁻ ξ, (∫⁻ η, A (ξ - η) * B η) ^ 2 ≤ (∫⁻ x, B x) ^ 2 * ∫⁻ η, A η ^ 2 := by
  have e : ∀ ξ : Euc d, ∫⁻ η, A (ξ - η) * B η = ∫⁻ η, B (ξ - η) * A η := by
    intro ξ
    rw [← lintegral_sub_left_eq_self (fun η => A (ξ - η) * B η) ξ]
    refine lintegral_congr fun η => ?_
    simp [mul_comm]
  simp_rw [e]
  exact sobmul_young hB hA


theorem mova4_transfer {m ρ : ℝ} (hρm : ρ ≤ m) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : y ≤ x) :
    x ^ (ρ / 2) ≤ x ^ (m / 2) * (y ^ (-m / 2) * y ^ (ρ / 2)) := by
  have e1 : y ^ (-m / 2) * y ^ (ρ / 2) = y ^ ((ρ - m) / 2) := by
    rw [← Real.rpow_add hy]; congr 1; ring
  have e2 : x ^ (m / 2) * x ^ ((ρ - m) / 2) = x ^ (ρ / 2) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  have e3 : x ^ ((ρ - m) / 2) ≤ y ^ ((ρ - m) / 2) :=
    Real.rpow_le_rpow_of_nonpos hy hxy (by linarith)
  rw [e1, ← e2]
  exact mul_le_mul_of_nonneg_left e3 (Real.rpow_nonneg hx.le _)

theorem mova4_pt {m ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρm : ρ ≤ m) (ξ η : Euc d) (a b : ℝ≥0∞) :
    ENNReal.ofReal (wt ξ ^ (ρ / 2)) * (a * b) ≤ ENNReal.ofReal ((4 : ℝ) ^ (ρ / 2)) *
      (a * (ENNReal.ofReal (wt η ^ (ρ / 2)) * b) +
        (ENNReal.ofReal (wt (ξ - η) ^ (m / 2)) * a) *
          (ENNReal.ofReal (wt η ^ (-m / 2)) * (ENNReal.ofReal (wt η ^ (ρ / 2)) * b))) := by
  rcases le_total (wt (ξ - η)) (wt η) with h | h
  · have hp := mova4_peetre hρ0 ξ η h le_rfl
    calc ENNReal.ofReal (wt ξ ^ (ρ / 2)) * (a * b)
        ≤ ENNReal.ofReal ((4 : ℝ) ^ (ρ / 2) * wt η ^ (ρ / 2)) * (a * b) := by
          gcongr
      _ = ENNReal.ofReal ((4 : ℝ) ^ (ρ / 2)) * (a * (ENNReal.ofReal (wt η ^ (ρ / 2)) * b)) := by
          rw [ENNReal.ofReal_mul (by positivity)]; ring
      _ ≤ _ := by
          gcongr
          exact le_self_add
  · have hp := mova4_peetre hρ0 ξ η le_rfl h
    have ht := mova4_transfer hρm (wt_pos (ξ - η)) (wt_pos η) h
    have hpos := wt_pos (ξ - η)
    have hpos' := wt_pos η
    calc ENNReal.ofReal (wt ξ ^ (ρ / 2)) * (a * b)
        ≤ ENNReal.ofReal ((4 : ℝ) ^ (ρ / 2) * (wt (ξ - η) ^ (m / 2) *
            (wt η ^ (-m / 2) * wt η ^ (ρ / 2)))) * (a * b) := by
          gcongr
          exact hp.trans (mul_le_mul_of_nonneg_left ht (by positivity))
      _ = ENNReal.ofReal ((4 : ℝ) ^ (ρ / 2)) *
          ((ENNReal.ofReal (wt (ξ - η) ^ (m / 2)) * a) *
          (ENNReal.ofReal (wt η ^ (-m / 2)) * (ENNReal.ofReal (wt η ^ (ρ / 2)) * b))) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by positivity)]
          ring
      _ ≤ _ := by
          gcongr
          exact le_add_self


theorem mova4_rpow_sq (s x : ℝ) (hx : 0 < x) : (x ^ (s / 2)) ^ 2 = x ^ s := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; congr 1; push_cast; ring

theorem mova4_wt_inv (s : ℝ) (ξ : Euc d) :
    ENNReal.ofReal (wt ξ ^ (-s / 2)) * ENNReal.ofReal (wt ξ ^ (s / 2)) = 1 := by
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (wt_pos ξ).le _), ← Real.rpow_add (wt_pos ξ)]
  have : -s / 2 + s / 2 = 0 := by ring
  rw [this]; simp

theorem mova4_core {m ρ : ℝ} (hm : (d : ℝ) / 2 < m) (hρ0 : 0 ≤ ρ) (hρm : ρ ≤ m) :
    ∃ k : ℝ, 0 ≤ k ∧ ∀ A B : Euc d → ℝ≥0∞, Measurable A → Measurable B →
      ∫⁻ ξ, (ENNReal.ofReal (wt ξ ^ (ρ / 2)) * ∫⁻ η, A (ξ - η) * B η) ^ 2 ≤
        ENNReal.ofReal k * ((∫⁻ x, (ENNReal.ofReal (wt x ^ (m / 2)) * A x) ^ 2) *
          ∫⁻ x, (ENNReal.ofReal (wt x ^ (ρ / 2)) * B x) ^ 2) := by
  have hint : Integrable (fun ξ : Euc d => wt ξ ^ (-m)) := by
    have := rg_integrable_a (d := d) (l := 0) (q := m) (by simpa using hm)
    refine this.congr (Eventually.of_forall fun ξ => ?_)
    simp only [pow_zero, one_mul]
    rw [mova4_rpow_sq _ _ (wt_pos ξ)]
  set Wm : ℝ := ∫ ξ, wt ξ ^ (-m) with hWm
  have hWm0 : 0 ≤ Wm := integral_nonneg fun ξ => Real.rpow_nonneg (wt_pos ξ).le _
  have hWmE : ∫⁻ ξ : Euc d, ENNReal.ofReal (wt ξ ^ (-m / 2)) ^ 2 = ENNReal.ofReal Wm := by
    rw [hWm, ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun ξ => Real.rpow_nonneg (wt_pos ξ).le _)]
    refine lintegral_congr fun ξ => ?_
    rw [← ENNReal.ofReal_pow (Real.rpow_nonneg (wt_pos ξ).le _), mova4_rpow_sq _ _ (wt_pos ξ)]
  set c0 : ℝ := (4 : ℝ) ^ (ρ / 2) with hc0
  have hc00 : 0 ≤ c0 := by positivity
  refine ⟨4 * c0 ^ 2 * Wm, by positivity, fun A B hA hB => ?_⟩
  have hwm : ∀ s : ℝ, Measurable fun x : Euc d => ENNReal.ofReal (wt x ^ s) := fun s =>
    ENNReal.measurable_ofReal.comp (continuous_wt_rpow s).measurable
  set Am : Euc d → ℝ≥0∞ := fun x => ENNReal.ofReal (wt x ^ (m / 2)) * A x with hAm
  set Bp : Euc d → ℝ≥0∞ := fun x => ENNReal.ofReal (wt x ^ (ρ / 2)) * B x with hBp
  set Bq : Euc d → ℝ≥0∞ := fun x => ENNReal.ofReal (wt x ^ (-m / 2)) * Bp x with hBq
  have hAmm : Measurable Am := (hwm _).mul hA
  have hBpm : Measurable Bp := (hwm _).mul hB
  have hBqm : Measurable Bq := (hwm _).mul hBpm
  set Sa := ∫⁻ x, Am x ^ 2 with hSa
  set Sb := ∫⁻ x, Bp x ^ 2 with hSb
  -- Cauchy-Schwarz bounds
  have hI : (∫⁻ x, A x) ^ 2 ≤ ENNReal.ofReal Wm * Sa := by
    have h := mova4_cs2 (hwm (-m / 2)) hAmm
    rw [hWmE] at h
    have e : ∫⁻ x, A x = ∫⁻ x, ENNReal.ofReal (wt x ^ (-m / 2)) * Am x := by
      refine lintegral_congr fun x => ?_
      simp only [hAm]
      rw [← mul_assoc, mova4_wt_inv, one_mul]
    rw [e]
    exact h
  have hJ : (∫⁻ x, Bq x) ^ 2 ≤ ENNReal.ofReal Wm * Sb := by
    have h := mova4_cs2 (hwm (-m / 2)) hBpm
    rw [hWmE] at h
    exact h
  have hP : ∀ ξ : Euc d, ENNReal.ofReal (wt ξ ^ (ρ / 2)) * ∫⁻ η, A (ξ - η) * B η ≤
      ENNReal.ofReal c0 * ((∫⁻ η, A (ξ - η) * Bp η) + ∫⁻ η, Am (ξ - η) * Bq η) := by
    intro ξ
    have hm1 : Measurable fun η => A (ξ - η) * Bp η :=
      (hA.comp (measurable_const.sub measurable_id)).mul hBpm
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_add_left hm1,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun η => ?_
    exact mova4_pt hρ0 hρm ξ η (A (ξ - η)) (B η)
  have hX := sobmul_young hA hBpm
  have hY := mova4_young_swap hAmm hBqm
  calc ∫⁻ ξ, (ENNReal.ofReal (wt ξ ^ (ρ / 2)) * ∫⁻ η, A (ξ - η) * B η) ^ 2
      ≤ ∫⁻ ξ, ENNReal.ofReal c0 ^ 2 * (2 * ((∫⁻ η, A (ξ - η) * Bp η) ^ 2 +
          (∫⁻ η, Am (ξ - η) * Bq η) ^ 2)) := by
        refine lintegral_mono fun ξ => ?_
        calc (ENNReal.ofReal (wt ξ ^ (ρ / 2)) * ∫⁻ η, A (ξ - η) * B η) ^ 2
            ≤ (ENNReal.ofReal c0 * ((∫⁻ η, A (ξ - η) * Bp η) + ∫⁻ η, Am (ξ - η) * Bq η)) ^ 2 :=
              pow_le_pow_left' (hP ξ) 2
          _ = ENNReal.ofReal c0 ^ 2 * ((∫⁻ η, A (ξ - η) * Bp η) + ∫⁻ η, Am (ξ - η) * Bq η) ^ 2 :=
              mul_pow _ _ _
          _ ≤ _ := by gcongr; exact mova4_add_sq_le _ _
    _ = ENNReal.ofReal c0 ^ 2 * (2 * ((∫⁻ ξ, (∫⁻ η, A (ξ - η) * Bp η) ^ 2) +
          ∫⁻ ξ, (∫⁻ η, Am (ξ - η) * Bq η) ^ 2)) := by
        rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),
          lintegral_const_mul' _ _ (by norm_num),
          lintegral_add_left ((mova4_meas_conv hA hBpm).pow_const 2)]
    _ ≤ ENNReal.ofReal c0 ^ 2 * (2 * ((∫⁻ x, A x) ^ 2 * Sb + (∫⁻ x, Bq x) ^ 2 * Sa)) :=
        by gcongr
    _ ≤ ENNReal.ofReal c0 ^ 2 * (2 * ((ENNReal.ofReal Wm * Sa) * Sb + (ENNReal.ofReal Wm * Sb) * Sa)) :=
        by gcongr
    _ = ENNReal.ofReal (4 * c0 ^ 2 * Wm) * (Sa * Sb) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_pow hc00]
        have : (ENNReal.ofReal 4 : ℝ≥0∞) = 4 := by
          rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]; norm_num
        rw [this]
        ring


theorem mova4_conv_bound {m ρ : ℝ} (hm : (d : ℝ) / 2 < m) (hρ0 : 0 ≤ ρ) (hρm : ρ ≤ m) :
    ∃ k : ℝ, 0 ≤ k ∧ ∀ a b : Euc d → ℂ, AEStronglyMeasurable a volume →
      AEStronglyMeasurable b volume →
      ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ ρ * ‖∫ η, a (ξ - η) * b η‖ ^ 2) ≤
        ENNReal.ofReal k * ((∫⁻ x, ENNReal.ofReal (wt x ^ m * ‖a x‖ ^ 2)) *
          ∫⁻ x, ENNReal.ofReal (wt x ^ ρ * ‖b x‖ ^ 2)) := by
  obtain ⟨k, hk0, hk⟩ := mova4_core (d := d) hm hρ0 hρm
  refine ⟨k, hk0, fun a b ha hb => ?_⟩
  set a' := ha.mk a with ha'
  set b' := hb.mk b with hb'
  have ha'm : Measurable a' := ha.stronglyMeasurable_mk.measurable
  have hb'm : Measurable b' := hb.stronglyMeasurable_mk.measurable
  have haa : a =ᵐ[volume] a' := ha.ae_eq_mk
  have hbb : b =ᵐ[volume] b' := hb.ae_eq_mk
  have key := hk (fun x => ‖a' x‖ₑ) (fun x => ‖b' x‖ₑ) ha'm.enorm hb'm.enorm
  have pw : ∀ ξ : Euc d, ‖∫ η, a (ξ - η) * b η‖ₑ ≤ ∫⁻ η, ‖a' (ξ - η)‖ₑ * ‖b' η‖ₑ := by
    intro ξ
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr_ae ?_
    have h1 : ∀ᵐ η ∂(volume : Measure (Euc d)), a (ξ - η) = a' (ξ - η) :=
      (Measure.measurePreserving_sub_left volume ξ).quasiMeasurePreserving.ae_eq_comp haa
    filter_upwards [h1, hbb] with η h1 h2
    rw [enorm_mul, h1, h2]
  have e1 : ∀ (c : ℝ) (f : Euc d → ℂ), ∫⁻ x, ENNReal.ofReal (wt x ^ c * ‖f x‖ ^ 2) =
      ∫⁻ x, (ENNReal.ofReal (wt x ^ (c / 2)) * ‖f x‖ₑ) ^ 2 := by
    intro c f
    refine lintegral_congr fun x => ?_
    rw [sobmul_sq_eq]
  have e2 : ∀ (c : ℝ) (f f' : Euc d → ℂ), f =ᵐ[volume] f' →
      ∫⁻ x, ENNReal.ofReal (wt x ^ c * ‖f x‖ ^ 2) = ∫⁻ x, ENNReal.ofReal (wt x ^ c * ‖f' x‖ ^ 2) := by
    intro c f f' h
    refine lintegral_congr_ae ?_
    filter_upwards [h] with x hx
    rw [hx]
  rw [e1 ρ, e2 m a a' haa, e2 ρ b b' hbb, e1 m, e1 ρ]
  refine le_trans ?_ key
  refine lintegral_mono fun ξ => pow_le_pow_left' ?_ 2
  gcongr
  exact pw ξ


/-- Fourier inversion for an `L²` function with integrable transform (a.e. version of `rg_inversion`). -/
theorem mova4_inversion {φ : Euc d → ℝ} (hφ : MemLp φ 2 volume)
    (hF1 : Integrable (fun ξ : Euc d => fourierL2 φ (-ξ))) :
    (fun x => 𝓕 (fun ξ : Euc d => fourierL2 φ (-ξ)) x) =ᵐ[volume] fun x => ((φ x : ℝ) : ℂ) := by
  set F' : Euc d → ℂ := fun ξ => fourierL2 φ (-ξ) with hF'
  set ψ : Euc d → ℂ := 𝓕 F' with hψ
  have hψc : Continuous ψ :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hF1
  have hφloc : LocallyIntegrable (fun x => ((φ x : ℝ) : ℂ)) volume :=
    hφ.ofReal.locallyIntegrable (by norm_num)
  have hψloc : LocallyIntegrable ψ volume := hψc.locallyIntegrable
  have key : ∀ g : Euc d → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, g x • (ψ x - ((φ x : ℝ) : ℂ)) = 0 := by
    intro g hg hsupp
    have hgC : ContDiff ℝ ∞ (fun x => ((g x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
    have hsC : HasCompactSupport (fun x => ((g x : ℝ) : ℂ)) :=
      hsupp.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
    set s : SchwartzMap (Euc d) ℂ := hsC.toSchwartzMap hgC with hsdef
    have hs : ⇑s = fun x => ((g x : ℝ) : ℂ) := rfl
    set t : SchwartzMap (Euc d) ℂ := 𝓕⁻ s with htdef
    have ht : 𝓕 t = s := FourierInvPair.fourier_fourierInv_eq s
    have htapply : ∀ ξ, t ξ = 𝓕 (⇑s) (-ξ) := by
      intro ξ
      rw [htdef, SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg]
    have h1 : ∫ x, g x • ψ x = ∫ ξ, 𝓕 (⇑s) (-ξ) * fourierL2 φ ξ := by
      have hflip : (innerₗ (Euc d)).flip = innerₗ (Euc d) := by
        ext x y
        simp
      have e0 := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
        (L := innerₗ (Euc d)) (f := F') (g := ⇑s)
        Real.continuous_fourierChar continuous_inner hF1 s.integrable
      rw [hflip] at e0
      simp only [smul_eq_mul] at e0
      have e1 : ∫ x, g x • ψ x = ∫ ξ, ψ ξ * s ξ := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [hs, Complex.real_smul]
        ring
      rw [e1]
      have e2 : (∫ ξ, ψ ξ * s ξ) = ∫ ξ, F' ξ * 𝓕 (⇑s) ξ := e0
      rw [e2]
      have e3 := integral_neg_eq_self (fun ξ : Euc d => F' ξ * 𝓕 (⇑s) ξ) (volume : Measure (Euc d))
      rw [← e3]
      refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
      simp only [hF', neg_neg]
      ring
    have h2 : ∫ x, g x • ((φ x : ℝ) : ℂ) = ∫ ξ, 𝓕 (⇑s) (-ξ) * fourierL2 φ ξ := by
      have e0 := rg_fourierL2_dual hφ t
      rw [ht] at e0
      have e1 : ∫ x, g x • ((φ x : ℝ) : ℂ) = ∫ x, s x * ((φ x : ℝ) : ℂ) := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [hs, Complex.real_smul]
      rw [e1, ← e0]
      refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
      show t ξ * fourierL2 φ ξ = _
      rw [htapply ξ]
    have hsplit : ∫ x, g x • (ψ x - ((φ x : ℝ) : ℂ)) =
        (∫ x, g x • ψ x) - ∫ x, g x • ((φ x : ℝ) : ℂ) := by
      rw [← integral_sub]
      · simp only [smul_sub]
      · exact hψloc.integrable_smul_left_of_hasCompactSupport hg.continuous hsupp
      · exact hφloc.integrable_smul_left_of_hasCompactSupport hg.continuous hsupp
    rw [hsplit, h1, h2, sub_self]
  have hzero := ae_eq_zero_of_integral_contDiff_smul_eq_zero (hψloc.sub hφloc) key
  filter_upwards [hzero] with x hx
  simpa [sub_eq_zero] using hx


theorem mova4_fourier_mod (G : Euc d → ℂ) (ξ ζ : Euc d) :
    𝓕 (fun x : Euc d => (Real.fourierChar (-inner ℝ x ξ) : Circle) • G x) ζ = 𝓕 G (ζ + ξ) := by
  rw [Real.fourier_eq, Real.fourier_eq]
  congr 1
  ext x
  rw [smul_smul, ← AddChar.map_add_eq_mul]
  congr 2
  rw [inner_add_right]; ring

/-- the multiplier formula: `𝓕(ψ · G)(ξ) = ∫ F'(ζ) 𝓕G(ζ+ξ)` for `ψ = 𝓕 F'`. -/
theorem mova4_fourier_mul_formula {F' G : Euc d → ℂ} (hF : Integrable F') (hG : Integrable G) (ξ : Euc d) :
    𝓕 (fun x => 𝓕 F' x * G x) ξ = ∫ ζ, F' ζ * 𝓕 G (ζ + ξ) := by
  have hflip : (innerₗ (Euc d)).flip = innerₗ (Euc d) := by
    ext x y
    simp
  set s : Euc d → ℂ := fun x => (Real.fourierChar (-inner ℝ x ξ) : Circle) • G x with hs
  have hsi : Integrable s := by
    refine hG.norm.mono' ?_ (ae_of_all _ fun x => ?_)
    · exact ((Real.continuous_fourierChar.comp (continuous_neg.comp
        (continuous_id.inner continuous_const))).aestronglyMeasurable).smul hG.aestronglyMeasurable
    · simp only [hs, norm_norm]
      exact (Circle.norm_smul _ _).le
  have e0 := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
    (L := innerₗ (Euc d)) (f := F') (g := s)
    Real.continuous_fourierChar continuous_inner hF hsi
  rw [hflip] at e0
  simp only [smul_eq_mul] at e0
  rw [Real.fourier_eq]
  have e1 : (∫ x, (Real.fourierChar (-inner ℝ x ξ) : Circle) • (𝓕 F' x * G x)) = ∫ x, 𝓕 F' x * s x := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [hs, smul_eq_mul, Circle.smul_def]
    ring
  refine e1.trans (e0.trans ?_)
  refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
  show F' ζ * 𝓕 s ζ = F' ζ * 𝓕 G (ζ + ξ)
  congr 1
  exact mova4_fourier_mod G ξ ζ


theorem mova4_norm_fourier_le (h : Euc d → ℂ) (w : Euc d) : ‖𝓕 h w‖ ≤ ∫ v, ‖h v‖ := by
  rw [Real.fourier_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext v
  exact Circle.norm_smul _ _

theorem mova4_u_bdd {u : Euc d → ℝ} (hu : MemLp u 2 volume) (ha : Integrable (fourierL2 u)) :
    ∀ᵐ x ∂(volume : Measure (Euc d)), |u x| ≤ ∫ ξ, ‖fourierL2 u ξ‖ := by
  have hF1 : Integrable (fun ξ : Euc d => fourierL2 u (-ξ)) := ha.comp_neg
  filter_upwards [mova4_inversion hu hF1] with x hx
  have h1 := mova4_norm_fourier_le (fun ξ : Euc d => fourierL2 u (-ξ)) x
  rw [hx, Complex.norm_real, Real.norm_eq_abs] at h1
  refine h1.trans (le_of_eq ?_)
  exact integral_neg_eq_self (fun ξ : Euc d => ‖fourierL2 u ξ‖) (volume : Measure (Euc d))

theorem mova4_memLp_mul {u g : Euc d → ℝ} (hu : MemLp u 2 volume) (ha : Integrable (fourierL2 u))
    {p : ℝ≥0∞} (_hp : 1 ≤ p) (hg : MemLp g p volume) : MemLp (fun x => u x * g x) p volume := by
  refine hg.of_le_mul (c := ∫ ξ, ‖fourierL2 u ξ‖) (hu.aestronglyMeasurable.mul hg.aestronglyMeasurable) ?_
  filter_upwards [mova4_u_bdd hu ha] with x hx
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

theorem mova4_prod_L1 {u g : Euc d → ℝ} (hu : MemLp u 2 volume) (ha : Integrable (fourierL2 u))
    (hg1 : Integrable g) (hg2 : MemLp g 2 volume) :
    fourierL2 (fun x => u x * g x) =ᵐ[volume] fun ξ => ∫ η, fourierL2 u (ξ - η) * fourierL2 g η := by
  set F' : Euc d → ℂ := fun ξ => fourierL2 u (-ξ) with hF'
  have hF1 : Integrable F' := ha.comp_neg
  have hinv := mova4_inversion hu hF1
  have hug2 := mova4_memLp_mul hu ha (p := 2) (by norm_num) hg2
  have hug1 : Integrable (fun x => u x * g x) := by
    have := (memLp_one_iff_integrable.1 (mova4_memLp_mul hu ha (p := 1) le_rfl
      (memLp_one_iff_integrable.2 hg1)))
    exact this
  have e1 := HRS.Commutator.Whole.energyAux_fourierL2_eq (fun x => u x * g x) hug1 hug2
  have e5 := HRS.Commutator.Whole.energyAux_fourierL2_eq g hg1 hg2
  have hG : Integrable (fun x : Euc d => ((g x : ℝ) : ℂ)) := hg1.ofReal
  filter_upwards [e1] with ξ h
  rw [h]
  have e2 : 𝓕 (fun x : Euc d => (((u x * g x : ℝ)) : ℂ)) ξ =
      𝓕 (fun x => 𝓕 F' x * ((g x : ℝ) : ℂ)) ξ := by
    rw [Real.fourier_eq, Real.fourier_eq]
    refine integral_congr_ae ?_
    filter_upwards [hinv] with x hx
    rw [hx]; simp
  rw [e2, mova4_fourier_mul_formula hF1 hG ξ]
  have e4 := integral_add_right_eq_self (μ := (volume : Measure (Euc d)))
    (fun η => fourierL2 u (ξ - η) * 𝓕 (fun x : Euc d => ((g x : ℝ) : ℂ)) η) ξ
  have e6 : ∫ ζ, F' ζ * 𝓕 (fun x : Euc d => ((g x : ℝ) : ℂ)) (ζ + ξ) =
      ∫ η, fourierL2 u (ξ - η) * 𝓕 (fun x : Euc d => ((g x : ℝ) : ℂ)) η := by
    rw [← e4]
    refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
    simp only [hF']
    congr 3
    abel
  rw [e6]
  refine integral_congr_ae ?_
  filter_upwards [e5] with η hη
  rw [hη]


theorem mova4_cs_c {k h : Euc d → ℂ} (hk : MemLp k 2 volume) (hh : MemLp h 2 volume) :
    ‖∫ η, k η * h η‖ ≤ (eLpNorm k 2 volume * eLpNorm h 2 volume).toReal := by
  have hint : Integrable (fun η => k η * h η) volume := hk.integrable_mul hh
  have hmeas : AEStronglyMeasurable (fun η => k η * h η) volume := hint.aestronglyMeasurable
  have h1 : eLpNorm (fun η => k η * h η) 1 volume ≤ eLpNorm k 2 volume * eLpNorm h 2 volume := by
    have := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := 2) (q := 2) (r := 1)
      (f := k) (g := h) (μ := volume) (fun x y : ℂ => x * y) 1 (by fun_prop)
      hk.aestronglyMeasurable hh.aestronglyMeasurable
      (Eventually.of_forall fun x => by simp)
    simpa using this
  have hfin : eLpNorm k 2 volume * eLpNorm h 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top (memLp_iff.1 hk).ne (memLp_iff.1 hh).ne
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [integral_norm_eq_lintegral_enorm hint.aestronglyMeasurable, ← eLpNorm_one_eq_lintegral_enorm]
  · exact ENNReal.toReal_mono hfin h1
  · exact hmeas


theorem mova4_prod_L2 {u v : Euc d → ℝ} (hu : MemLp u 2 volume) (ha : Integrable (fourierL2 u))
    (hv : MemLp v 2 volume) :
    fourierL2 (fun x => u x * v x) =ᵐ[volume] fun ξ => ∫ η, fourierL2 u (ξ - η) * fourierL2 v η := by
  set M : ℝ := ∫ ξ, ‖fourierL2 u ξ‖ with hM
  have hM0 : 0 ≤ M := integral_nonneg fun ξ => norm_nonneg _
  have hε : ∀ n : ℕ, ENNReal.ofReal (1 / ((n : ℝ) + 1)) ≠ 0 := fun n => by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  choose g hgs hgε hgc hg2 using fun n : ℕ =>
    hv.exists_hasCompactSupport_eLpNorm_sub_le (p := 2) (by norm_num) (hε n)
  have hg1 : ∀ n, Integrable (g n) := fun n => (hgc n).integrable_of_hasCompactSupport (hgs n)
  have huv := mova4_memLp_mul hu ha (p := 2) (by norm_num) hv
  have hug : ∀ n, MemLp (fun x => u x * g n x) 2 volume := fun n =>
    mova4_memLp_mul hu ha (p := 2) (by norm_num) (hg2 n)
  have hT : Tendsto (fun n : ℕ => eLpNorm (fourierL2 (fun x => u x * g n x) - fourierL2 (fun x => u x * v x)) 2
      volume) atTop (𝓝 0) := by
    have hle : ∀ n : ℕ, eLpNorm (fourierL2 (fun x => u x * g n x) - fourierL2 (fun x => u x * v x)) 2
        volume ≤ ENNReal.ofReal M * ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
      intro n
      have A1 : fourierL2 (fun x => u x * g n x) - fourierL2 (fun x => u x * v x) =ᵐ[volume]
          fourierL2 (fun x => u x * g n x - u x * v x) := by
        filter_upwards [fourierL2_sub (hug n) huv] with ξ h
        simp only [Pi.sub_apply, h]
      have hw : MemLp (fun x => u x * g n x - u x * v x) 2 volume := (hug n).sub huv
      rw [eLpNorm_congr_ae A1, tc3_eLpNorm_fourierL2 hw]
      have A2 : ∀ᵐ x ∂(volume : Measure (Euc d)), ‖u x * g n x - u x * v x‖ ≤ M * ‖v x - g n x‖ := by
        filter_upwards [mova4_u_bdd hu ha] with x hx
        rw [← mul_sub, norm_mul, Real.norm_eq_abs, ← norm_neg (g n x - v x), neg_sub]
        exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
      refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul ((hug n).sub huv).aestronglyMeasurable A2 2).trans ?_
      gcongr
      exact hgε n
    have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal M * ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal M)
        (ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
        (Or.inr ENNReal.ofReal_ne_top)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le) hle
  obtain ⟨ns, hmono, hns⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hT).exists_seq_tendsto_ae
  have hall : ∀ᵐ ξ ∂(volume : Measure (Euc d)), ∀ n : ℕ, fourierL2 (fun x => u x * g n x) ξ =
      ∫ η, fourierL2 u (ξ - η) * fourierL2 (g n) η := by
    rw [ae_all_iff]
    intro n
    exact mova4_prod_L1 hu ha (hg1 n) (hg2 n)
  filter_upwards [hns, hall] with ξ h1 h2
  have h1' : Tendsto (fun i => fourierL2 (fun x => u x * g (ns i) x) ξ) atTop
      (𝓝 (fourierL2 (fun x => u x * v x) ξ)) := h1
  have hak : MemLp (fun η : Euc d => fourierL2 u (ξ - η)) 2 volume :=
    (memLp_fourierL2 hu).comp_measurePreserving (Measure.measurePreserving_sub_left volume ξ)
  have hF : ∀ n : ℕ, MemLp (fun η => fourierL2 (g n) η - fourierL2 v η) 2 volume := fun n =>
    (memLp_fourierL2 (hg2 n)).sub (memLp_fourierL2 hv)
  have hFn : ∀ n : ℕ, (eLpNorm (fun η => fourierL2 (g n) η - fourierL2 v η) 2 volume).toReal ≤
      1 / ((n : ℝ) + 1) := by
    intro n
    have e : eLpNorm (fun η => fourierL2 (g n) η - fourierL2 v η) 2 volume =
        eLpNorm (fun x => v x - g n x) 2 volume := by
      have := fourierL2_sub (hg2 n) hv
      have hw : MemLp (fun x => g n x - v x) 2 volume := (hg2 n).sub hv
      rw [eLpNorm_congr_ae (this.symm), tc3_eLpNorm_fourierL2 hw]
      exact eLpNorm_sub_comm (p := 2) (μ := volume) (g n) v
    rw [e]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hgε n)
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have h3 : Tendsto (fun i => ∫ η, fourierL2 u (ξ - η) * fourierL2 (g (ns i)) η) atTop
      (𝓝 (∫ η, fourierL2 u (ξ - η) * fourierL2 v η)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    set C : ℝ := (eLpNorm (fun η : Euc d => fourierL2 u (ξ - η)) 2 volume).toReal with hC
    have hbd : ∀ n : ℕ, ‖(∫ η, fourierL2 u (ξ - η) * fourierL2 (g n) η) -
        ∫ η, fourierL2 u (ξ - η) * fourierL2 v η‖ ≤ C * (1 / ((n : ℝ) + 1)) := by
      intro n
      have hi1 : Integrable (fun η => fourierL2 u (ξ - η) * fourierL2 (g n) η) volume :=
        hak.integrable_mul (memLp_fourierL2 (hg2 n))
      have hi2 : Integrable (fun η => fourierL2 u (ξ - η) * fourierL2 v η) volume :=
        hak.integrable_mul (memLp_fourierL2 hv)
      rw [← integral_sub hi1 hi2]
      have := mova4_cs_c hak (hF n)
      have e : (fun η => fourierL2 u (ξ - η) * fourierL2 (g n) η - fourierL2 u (ξ - η) * fourierL2 v η) =
          fun η => fourierL2 u (ξ - η) * (fourierL2 (g n) η - fourierL2 v η) := by
        funext η; ring
      rw [e]
      refine this.trans ?_
      rw [ENNReal.toReal_mul]
      exact mul_le_mul_of_nonneg_left (hFn n) ENNReal.toReal_nonneg
    have hlim : Tendsto (fun n : ℕ => C * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => hbd (ns n))
      (hlim.comp hmono.tendsto_atTop)
  refine tendsto_nhds_unique h1' ?_
  refine h3.congr fun i => ?_
  exact (h2 (ns i)).symm


theorem mova4_sobolev_algebra {m ρ : ℝ} (hm : (d : ℝ) / 2 < m) (hρ0 : 0 ≤ ρ) (hρm : ρ ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v : Euc d → ℝ, HRS.PDE.ToolboxRd.MemSobolev m u → HRS.PDE.ToolboxRd.MemSobolev ρ v →
      HRS.PDE.ToolboxRd.MemSobolev ρ (fun x => u x * v x) ∧
        HRS.PDE.ToolboxRd.sobolevNormSq ρ (fun x => u x * v x) ≤ C ^ 2 * HRS.PDE.ToolboxRd.sobolevNormSq m u * HRS.PDE.ToolboxRd.sobolevNormSq ρ v := by
  obtain ⟨k, hk0, hk⟩ := mova4_conv_bound (d := d) hm hρ0 hρm
  refine ⟨Real.sqrt k + 1, by positivity, fun u v hu hv => ?_⟩
  have hu2 := hu.1
  have hv2 := hv.1
  have hFam := aestronglyMeasurable_fourierL2 hu2
  have hFbm := aestronglyMeasurable_fourierL2 hv2
  have ha : Integrable (fourierL2 u) := by
    obtain ⟨C0, -, hC0⟩ := rg_moment_bound (d := d) 0 (q := m) (by simpa using hm)
    have := (hC0 u hu).1
    simp only [pow_zero, one_mul] at this
    exact (integrable_norm_iff hFam).1 this
  have hp := mova4_memLp_mul hu2 ha (p := 2) (by norm_num) hv2
  have hbm := aestronglyMeasurable_fourierL2 hp
  have hF := mova4_prod_L2 hu2 ha hv2
  have key := hk (fourierL2 u) (fourierL2 v) hFam hFbm
  have hSig : ∀ (s : ℝ) (w : Euc d → ℝ), HRS.PDE.ToolboxRd.MemSobolev s w →
      ∫⁻ η, ENNReal.ofReal (wt η ^ s * ‖fourierL2 w η‖ ^ 2) = ENNReal.ofReal (HRS.PDE.ToolboxRd.sobolevNormSq s w) := by
    intro s w hw
    have hw2 : Integrable (fun ξ : Euc d => wt ξ ^ s * ‖fourierL2 w ξ‖ ^ 2) volume := hw.2
    rw [sobolevNormSq_eq, ofReal_integral_eq_lintegral_ofReal hw2
      (Filter.Eventually.of_forall fun η => by have := wt_pos (d := d) η; positivity)]
  rw [hSig m u hu, hSig ρ v hv] at key
  have hnn : ∀ (s : ℝ) (w : Euc d → ℝ), 0 ≤ HRS.PDE.ToolboxRd.sobolevNormSq s w := fun s w =>
    integral_nonneg fun η => by have := wt_pos (d := d) η; positivity
  have hL : ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ ρ * ‖fourierL2 (fun x => u x * v x) ξ‖ ^ 2) ≤
      ENNReal.ofReal (k * (HRS.PDE.ToolboxRd.sobolevNormSq m u * HRS.PDE.ToolboxRd.sobolevNormSq ρ v)) := by
    have e : ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ ρ * ‖fourierL2 (fun x => u x * v x) ξ‖ ^ 2) =
        ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ ρ * ‖∫ η, fourierL2 u (ξ - η) * fourierL2 v η‖ ^ 2) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hF] with ξ hξ
      rw [hξ]
    rw [e]
    refine key.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (hnn m u), ← ENNReal.ofReal_mul hk0]
  have hint : Integrable (fun ξ => wt ξ ^ ρ * ‖fourierL2 (fun x => u x * v x) ξ‖ ^ 2) volume := by
    refine ⟨aesm_wt_mul hbm ρ, ?_⟩
    unfold HasFiniteIntegral
    refine lt_of_le_of_lt ?_ (lt_of_le_of_lt hL ENNReal.ofReal_lt_top)
    refine le_of_eq (lintegral_congr fun ξ => ?_)
    rw [Real.enorm_eq_ofReal (by have := wt_pos (d := d) ξ; positivity)]
  refine ⟨⟨hp, hint⟩, ?_⟩
  rw [sobolevNormSq_eq]
  have h2 := hL
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun η => by have := wt_pos (d := d) η; positivity)] at h2
  have h3 := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hk0 (mul_nonneg (hnn m u) (hnn ρ v)))).1 h2
  refine h3.trans ?_
  have hsq : k ≤ (Real.sqrt k + 1) ^ 2 := by nlinarith [Real.sq_sqrt hk0, Real.sqrt_nonneg k]
  have := mul_nonneg (hnn m u) (hnn ρ v)
  nlinarith


/-- Extended-norm form: `‖u v‖_{H^ρ} ≤ C ‖u‖_{H^m} ‖v‖_{H^ρ}` for `u ∈ H^m`, `v ∈ H^ρ`. -/
theorem mova4_sobolevNormE_algebra {m ρ : ℝ} (hm : (d : ℝ) / 2 < m) (hρ0 : 0 ≤ ρ) (hρm : ρ ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v : Euc d → ℝ, HRS.PDE.ToolboxRd.MemSobolev m u →
      HRS.PDE.ToolboxRd.MemSobolev ρ v →
      HRS.Whole.sobolevNormE ρ (fun x => u x * v x) ≤
        ENNReal.ofReal C * (HRS.Whole.sobolevNormE m u * HRS.Whole.sobolevNormE ρ v) := by
  obtain ⟨C, hC, h⟩ := mova4_sobolev_algebra (d := d) hm hρ0 hρm
  refine ⟨C, hC, fun u v hu hv => ?_⟩
  obtain ⟨h1, h2⟩ := h u v hu hv
  unfold HRS.Whole.sobolevNormE
  rw [if_pos hu, if_pos hv, if_pos h1, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    ← ENNReal.ofReal_mul hC.le]
  apply ENNReal.ofReal_le_ofReal
  have hu0 : 0 ≤ HRS.PDE.ToolboxRd.sobolevNormSq m u := integral_nonneg fun η => by
    have := wt_pos (d := d) η; positivity
  have hv0 : 0 ≤ HRS.PDE.ToolboxRd.sobolevNormSq ρ v := integral_nonneg fun η => by
    have := wt_pos (d := d) η; positivity
  calc Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq ρ fun x => u x * v x)
      ≤ Real.sqrt (C ^ 2 * HRS.PDE.ToolboxRd.sobolevNormSq m u * HRS.PDE.ToolboxRd.sobolevNormSq ρ v) :=
        Real.sqrt_le_sqrt h2
    _ = C * (Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq m u) *
          Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq ρ v)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hC.le]
        ring

end HRS.MS.MovA4
