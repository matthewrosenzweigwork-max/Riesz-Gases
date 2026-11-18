import HRS.MS.SpecAux88
import HRS.MS.SpecAux16

/-!
# S8M: the master `L⁴(μ)` bound for convolutions with the Riesz kernel (S8.7, R4)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  For `0 < s`, `3s/2 < d` and `S8pRho d s ρ M`: there is `A ≥ 0` such that
every measurable `F` with `|F(x)| ≤ ∫ g(x-y) G(y) dy` (`g = rieszKernel d s`, `G ≥ 0`, `G, G² ∈ L¹`) satisfies
`∫ ρ F⁴ ≤ A ((∫ G²)² + (∫ G)⁴)` (`s8p_master`).  Splitting `g ≤ g 1_{B_1} + 1`, `s8p_young4` for the local part.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HRS.MS.Spec

open HRS HRS.Whole

variable {d : ℕ}

/-- The local part of the kernel. -/
def s8p_kloc (d : ℕ) (s : ℝ) : Euc d → ℝ≥0∞ :=
  (ball (0 : Euc d) 1).indicator fun z => ENNReal.ofReal (rieszKernel d s z)

theorem s8p_kloc_meas (s : ℝ) : Measurable (s8p_kloc d s) :=
  (ENNReal.measurable_ofReal.comp (s8p_riesz_meas s)).indicator measurableSet_ball

theorem s8p_kloc_int (s : ℝ) : ∫⁻ z, s8p_kloc d s z = s8p_Iball d s := by
  unfold s8p_kloc s8p_Iball
  rw [lintegral_indicator measurableSet_ball]

theorem s8p_kloc_rpow_int {s : ℝ} (hs0 : 0 < s) :
    ∫⁻ z, s8p_kloc d s z ^ ((3 : ℝ) / 2) = s8p_Iball d (3 * s / 2) := by
  unfold s8p_kloc s8p_Iball
  have e : ∀ z : Euc d, ((ball (0 : Euc d) 1).indicator (fun z => ENNReal.ofReal (rieszKernel d s z)) z) ^
      ((3 : ℝ) / 2) = (ball (0 : Euc d) 1).indicator
        (fun z => ENNReal.ofReal (rieszKernel d (3 * s / 2) z)) z := by
    intro z
    by_cases hz : z ∈ ball (0 : Euc d) 1
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz,
        ENNReal.ofReal_rpow_of_nonneg (s8p_riesz_nonneg hs0 z) (by norm_num)]
      congr 1
      unfold rieszKernel
      rw [if_neg hs0.ne', if_neg (by positivity), ← Real.rpow_mul (norm_nonneg _)]
      congr 1; ring
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
      exact ENNReal.zero_rpow_of_pos (by norm_num)
  simp_rw [e]
  rw [lintegral_indicator measurableSet_ball]

theorem s8p_riesz_le_kloc_add_one {s : ℝ} (hs0 : 0 < s) (z : Euc d) :
    ENNReal.ofReal (rieszKernel d s z) ≤ s8p_kloc d s z + 1 := by
  by_cases hz : z ∈ ball (0 : Euc d) 1
  · unfold s8p_kloc
    rw [Set.indicator_of_mem hz]; exact le_self_add
  · have : rieszKernel d s z ≤ 1 := s8p_riesz_le_one hs0 (by simpa using hz)
    calc ENNReal.ofReal (rieszKernel d s z) ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal this
      _ = 1 := ENNReal.ofReal_one
      _ ≤ _ := le_add_self

theorem s8p_master {s M : ℝ} {ρ : Euc d → ℝ} (h : S8pRho d s ρ M) (h32 : 3 * s / 2 < d) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (G F : Euc d → ℝ), Measurable G → (∀ x, 0 ≤ G x) → Integrable G →
      Integrable (fun x => G x ^ 2) → Measurable F →
      (∀ x, ENNReal.ofReal |F x| ≤ ∫⁻ y, ENNReal.ofReal (rieszKernel d s (x - y) * G y)) →
      Integrable (fun x => ρ x * F x ^ 4) ∧
        ∫ x, ρ x * F x ^ 4 ≤ A * ((∫ x, G x ^ 2) ^ 2 + (∫ x, G x) ^ 4) := by
  have hs0 := h.hs0
  have hA0 : s8p_Iball d s < ⊤ := s8p_Iball_lt_top hs0.le h.hsd
  have hA1 : s8p_Iball d (3 * s / 2) < ⊤ := s8p_Iball_lt_top (by positivity) h32
  set a0 : ℝ := (s8p_Iball d s).toReal with ha0
  set a1 : ℝ := (s8p_Iball d (3 * s / 2)).toReal with ha1
  have hM0 : 0 ≤ M := le_trans (h.nonneg 0) (h.le 0)
  refine ⟨8 * (M * a1 ^ 2 * a0 + 1), by positivity, fun G F hGm hG0 hGi hG2 hFm hF => ?_⟩
  set Gen : Euc d → ℝ≥0∞ := fun y => ENNReal.ofReal (G y) with hGen
  have hGenm : Measurable Gen := ENNReal.measurable_ofReal.comp hGm
  have hc : ∫⁻ y, Gen y = ENNReal.ofReal (∫ y, G y) :=
    (ofReal_integral_eq_lintegral_ofReal hGi (Filter.Eventually.of_forall hG0)).symm
  have hq : ∫⁻ y, Gen y ^ 2 = ENNReal.ofReal (∫ y, G y ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hG2 (Filter.Eventually.of_forall fun y => sq_nonneg _)]
    refine lintegral_congr fun y => ?_
    rw [hGen]; simp only; rw [ENNReal.ofReal_pow (hG0 y)]
  set kl := s8p_kloc d s with hkl
  have hklm : Measurable kl := s8p_kloc_meas s
  -- pointwise bound
  have hL : ∀ x, ENNReal.ofReal |F x| ≤ s8p_cv kl Gen x + ∫⁻ y, Gen y := by
    intro x
    refine (hF x).trans ?_
    unfold s8p_cv
    rw [← lintegral_add_left]
    · refine lintegral_mono fun y => ?_
      rw [ENNReal.ofReal_mul (s8p_riesz_nonneg hs0 _)]
      calc ENNReal.ofReal (rieszKernel d s (x - y)) * ENNReal.ofReal (G y)
          ≤ (kl (x - y) + 1) * Gen y := by
            gcongr; exact s8p_riesz_le_kloc_add_one hs0 _
        _ = _ := by rw [add_mul, one_mul]
    · exact (hklm.comp (measurable_const.sub measurable_id)).mul hGenm
  set c : ℝ≥0∞ := ∫⁻ y, Gen y with hcdef
  have hcv : Measurable (s8p_cv kl Gen) := by
    have hm : Measurable (fun p : Euc d × Euc d => kl (p.1 - p.2) * Gen p.2) :=
      (hklm.comp (measurable_fst.sub measurable_snd)).mul (hGenm.comp measurable_snd)
    exact hm.lintegral_prod_right'
  have h8 : ∀ x, ENNReal.ofReal |F x| ^ 4 ≤ 8 * (s8p_cv kl Gen x ^ 4 + c ^ 4) := by
    intro x
    have h1 : ENNReal.ofReal |F x| ^ 4 ≤ (s8p_cv kl Gen x + c) ^ 4 := pow_le_pow_left' (hL x) 4
    have h2 := ENNReal.rpow_add_le_mul_rpow_add_rpow (s8p_cv kl Gen x) c (p := 4) (by norm_num)
    have e1 : ∀ z : ℝ≥0∞, z ^ (4 : ℝ) = z ^ 4 := fun z => by
      rw [← ENNReal.rpow_natCast]; norm_num
    rw [e1, e1, e1] at h2
    refine h1.trans (h2.trans (le_of_eq ?_))
    norm_num
  have hY := s8p_young4 hklm hGenm
  rw [s8p_kloc_rpow_int hs0, s8p_kloc_int] at hY
  rw [hq] at hY
  -- the weighted lintegral
  have hρ1 : ∫⁻ x, ENNReal.ofReal (ρ x) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal h.int (Filter.Eventually.of_forall h.nonneg), h.one]
    simp
  have hρm : Measurable fun x => ENNReal.ofReal (ρ x) := ENNReal.measurable_ofReal.comp h.meas
  have step1 : ∀ x, ENNReal.ofReal (ρ x * F x ^ 4) ≤
      8 * (ENNReal.ofReal M * s8p_cv kl Gen x ^ 4) + 8 * c ^ 4 * ENNReal.ofReal (ρ x) := by
    intro x
    rw [ENNReal.ofReal_mul (h.nonneg x), ← Even.pow_abs (by decide : Even 4) (F x),
      ENNReal.ofReal_pow (abs_nonneg _)]
    calc ENNReal.ofReal (ρ x) * ENNReal.ofReal |F x| ^ 4
        ≤ ENNReal.ofReal (ρ x) * (8 * (s8p_cv kl Gen x ^ 4 + c ^ 4)) := by gcongr; exact h8 x
      _ = 8 * (ENNReal.ofReal (ρ x) * s8p_cv kl Gen x ^ 4) + 8 * c ^ 4 * ENNReal.ofReal (ρ x) := by ring
      _ ≤ _ := by
          gcongr
          exact h.le x
  have hmain : ∫⁻ x, ENNReal.ofReal (ρ x * F x ^ 4) ≤
      ENNReal.ofReal (8 * (M * a1 ^ 2 * a0) * (∫ x, G x ^ 2) ^ 2 + 8 * (∫ x, G x) ^ 4) := by
    calc ∫⁻ x, ENNReal.ofReal (ρ x * F x ^ 4)
        ≤ ∫⁻ x, (8 * (ENNReal.ofReal M * s8p_cv kl Gen x ^ 4) + 8 * c ^ 4 * ENNReal.ofReal (ρ x)) :=
          lintegral_mono step1
      _ = 8 * (ENNReal.ofReal M * ∫⁻ x, s8p_cv kl Gen x ^ 4) + 8 * c ^ 4 := by
          have hu : Measurable fun x => s8p_cv kl Gen x ^ 4 := hcv.pow_const 4
          have hv : Measurable fun x => 8 * (ENNReal.ofReal M * s8p_cv kl Gen x ^ 4) :=
            (hu.const_mul (ENNReal.ofReal M)).const_mul 8
          rw [lintegral_add_left hv, lintegral_const_mul _ (hu.const_mul (ENNReal.ofReal M)),
            lintegral_const_mul _ hu, lintegral_const_mul _ hρm, hρ1, mul_one]
      _ ≤ 8 * (ENNReal.ofReal M * ((s8p_Iball d (3 * s / 2)) ^ 2 * (s8p_Iball d s) *
            ENNReal.ofReal (∫ y, G y ^ 2) ^ 2)) + 8 * c ^ 4 := by
          gcongr
      _ = _ := by
          have hQ : 0 ≤ ∫ x, G x ^ 2 := integral_nonneg fun x => sq_nonneg _
          have hP : 0 ≤ ∫ x, G x := integral_nonneg hG0
          have ha0' : 0 ≤ a0 := ENNReal.toReal_nonneg
          have ha1' : 0 ≤ a1 := ENNReal.toReal_nonneg
          rw [← ENNReal.ofReal_toReal hA1.ne, ← ENNReal.ofReal_toReal hA0.ne, hc]
          have e8 : ENNReal.ofReal (8 * (M * a1 ^ 2 * a0)) =
              ENNReal.ofReal 8 * (ENNReal.ofReal M * (ENNReal.ofReal a1 ^ 2 * ENNReal.ofReal a0)) := by
            rw [ENNReal.ofReal_mul (p := 8) (by norm_num), ENNReal.ofReal_mul (p := M * a1 ^ 2) (by positivity),
              ENNReal.ofReal_mul (p := M) hM0, ENNReal.ofReal_pow ha1']
            ring
          have e9 : ENNReal.ofReal (8 * (M * a1 ^ 2 * a0) * (∫ x, G x ^ 2) ^ 2 + 8 * (∫ x, G x) ^ 4) =
              ENNReal.ofReal (8 * (M * a1 ^ 2 * a0)) * ENNReal.ofReal (∫ x, G x ^ 2) ^ 2 +
                ENNReal.ofReal 8 * ENNReal.ofReal (∫ x, G x) ^ 4 := by
            have f1 : ENNReal.ofReal (8 * (M * a1 ^ 2 * a0) * (∫ x, G x ^ 2) ^ 2) =
                ENNReal.ofReal (8 * (M * a1 ^ 2 * a0)) * ENNReal.ofReal (∫ x, G x ^ 2) ^ 2 := by
              rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hQ]
            have f2 : ENNReal.ofReal (8 * (∫ x, G x) ^ 4) = ENNReal.ofReal 8 * ENNReal.ofReal (∫ x, G x) ^ 4 := by
              rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow hP]
            rw [ENNReal.ofReal_add (by positivity) (by positivity), f1, f2]
          rw [e9, e8, ENNReal.ofReal_ofNat]
          ring
  have hfm : Measurable fun x => ρ x * F x ^ 4 := h.meas.mul (hFm.pow_const 4)
  have hfn : ∀ x, 0 ≤ ρ x * F x ^ 4 := fun x => mul_nonneg (h.nonneg x) (by positivity)
  have hBnn : 0 ≤ 8 * (M * a1 ^ 2 * a0) * (∫ x, G x ^ 2) ^ 2 + 8 * (∫ x, G x) ^ 4 := by
    have : 0 ≤ ∫ x, G x ^ 2 := integral_nonneg fun x => sq_nonneg _
    have ha0' : 0 ≤ a0 := ENNReal.toReal_nonneg
    positivity
  have hint : Integrable (fun x => ρ x * F x ^ 4) := by
    rw [← lintegral_ofReal_ne_top_iff_integrable hfm.aestronglyMeasurable
      (Filter.Eventually.of_forall hfn)]
    exact (lt_of_le_of_lt hmain ENNReal.ofReal_lt_top).ne
  refine ⟨hint, ?_⟩
  have h1 : ENNReal.ofReal (∫ x, ρ x * F x ^ 4) ≤
      ENNReal.ofReal (8 * (M * a1 ^ 2 * a0) * (∫ x, G x ^ 2) ^ 2 + 8 * (∫ x, G x) ^ 4) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hfn)]
    exact hmain
  have h2 := (ENNReal.ofReal_le_ofReal_iff hBnn).1 h1
  refine h2.trans ?_
  have hQ : 0 ≤ (∫ x, G x ^ 2) ^ 2 := sq_nonneg _
  have hP4 : 0 ≤ (∫ x, G x) ^ 4 := by positivity
  have ha0' : 0 ≤ a0 := ENNReal.toReal_nonneg
  have hm0 : 0 ≤ M * a1 ^ 2 * a0 := by positivity
  nlinarith [mul_nonneg hm0 hQ, mul_nonneg hm0 hP4]

end HRS.MS.Spec
