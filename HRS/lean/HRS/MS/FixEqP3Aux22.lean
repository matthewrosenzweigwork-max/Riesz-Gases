import HRS.MS.FixEqP3Aux21
import HRS.MP.KolmChentsov

/-!
# S5.7 `fixed_equation` (worker S57P), part 34: `E sup_t ‖Z_t - Z_0‖⁴ ≤ C(T) A` from fourth-moment increments

Dyadic chaining (`mkc_chain`): if `E‖Z_t - Z_s‖⁴ ≤ A|t-s|²` and `Z` is continuous on `[0,T]` for every sample point, then
`E sup_{t ≤ T} ‖Z_t - Z_0‖⁴ ≤ C_0 A`, `C_0` depending only on `T` (`s57p_sup_moment`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MS.FixEq

open HRS.MP.KC

section Det

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ω : Type*} [MeasurableSpace Ω]

/-- the grid sums -/
def s57pSfun (Z : ℝ → Ω → E) (T r : ℝ) (ζ : Ω) : ℝ≥0∞ :=
  ∑' n : ℕ, ∑ k ∈ Finset.range (2 ^ n),
    (‖Z (mkc_pt T n (k + 1)) ζ - Z (mkc_pt T n k) ζ‖ₑ / ENNReal.ofReal (r ^ n)) ^ 4

theorem s57p_sup_det {T r : ℝ} (hT : 0 < T) (hr0 : 0 < r) (hr1 : r < 1) {Z : ℝ → Ω → E} (ζ : Ω)
    (hc : ContinuousOn (fun t => Z t ζ) (Set.Icc 0 T)) :
    (⨆ t : Set.Icc (0 : ℝ) T, ‖Z t ζ - Z 0 ζ‖ₑ) ^ 4 ≤
      ENNReal.ofReal ((1 + r / (1 - r)) ^ 4) * s57pSfun Z T r ζ := by
  set C1 : ℝ := 1 + r / (1 - r) with hC1
  have hC10 : 0 < C1 := by have : 0 < r / (1 - r) := div_pos hr0 (by linarith); rw [hC1]; linarith
  by_cases hS : s57pSfun Z T r ζ = ⊤
  · rw [hS, ENNReal.mul_top (ENNReal.ofReal_pos.2 (pow_pos hC10 4)).ne']; exact le_top
  set S := s57pSfun Z T r ζ with hSdef
  set lam : ℝ := S.toReal ^ (1 / 4 : ℝ) with hlam
  have hlam0 : 0 ≤ lam := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hlam4 : lam ^ 4 = S.toReal := by
    rw [hlam, ← Real.rpow_natCast, ← Real.rpow_mul ENNReal.toReal_nonneg]; norm_num
  -- the increments
  have hInc : mkc_Inc (mkc_xs Z T ζ) lam r := by
    intro n k hk
    have h1 : (‖Z (mkc_pt T n (k + 1)) ζ - Z (mkc_pt T n k) ζ‖ₑ / ENNReal.ofReal (r ^ n)) ^ 4 ≤ S := by
      refine le_trans ?_ (ENNReal.le_tsum n)
      exact Finset.single_le_sum (f := fun k => (‖Z (mkc_pt T n (k + 1)) ζ - Z (mkc_pt T n k) ζ‖ₑ /
        ENNReal.ofReal (r ^ n)) ^ 4) (fun _ _ => zero_le) (Finset.mem_range.2 hk)
    set a : ℝ := ‖Z (mkc_pt T n (k + 1)) ζ - Z (mkc_pt T n k) ζ‖ / r ^ n with ha
    have hrn : 0 < r ^ n := pow_pos hr0 n
    have e : (‖Z (mkc_pt T n (k + 1)) ζ - Z (mkc_pt T n k) ζ‖ₑ / ENNReal.ofReal (r ^ n)) = ENNReal.ofReal a := by
      rw [ha, ENNReal.ofReal_div_of_pos hrn, ofReal_norm]
    rw [e, ← ENNReal.ofReal_pow (div_nonneg (norm_nonneg _) hrn.le)] at h1
    have h2 : a ^ 4 ≤ S.toReal := (ENNReal.ofReal_le_iff_le_toReal hS).1 h1
    have h3 : a ≤ lam := by
      refine le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) hlam0 ?_
      rw [hlam4]; exact h2
    show ‖Z (mkc_pt T n (k + 1)) ζ - Z (mkc_pt T n k) ζ‖ ≤ lam * r ^ n
    rw [ha, div_le_iff₀ hrn] at h3
    linarith
  have hgrid : ∀ n k : ℕ, k ≤ 2 ^ n → ‖Z (mkc_pt T n k) ζ - Z 0 ζ‖ ≤ C1 * lam := by
    intro n k hk
    have hch := mkc_chain (mkc_cons_xs Z T ζ) hInc 0 n k (by simpa using hk)
    have hgeo := mkc_geom_le hlam0 hr0.le hr1 0 n
    have h0 : mkc_xs Z T ζ 0 0 = Z 0 ζ := by simp [mkc_xs, mkc_pt]
    have hq : k / 2 ^ n = 0 ∨ k / 2 ^ n = 1 :=
      Nat.le_one_iff_eq_zero_or_eq_one.1 (Nat.div_le_of_le_mul (by simpa using hk))
    have hx0 : ‖mkc_xs Z T ζ 0 (k / 2 ^ n) - mkc_xs Z T ζ 0 0‖ ≤ lam := by
      rcases hq with h | h
      · rw [h]; simp [hlam0]
      · rw [h]
        have := hInc 0 0 (by norm_num)
        simpa using this
    have hsum : ‖mkc_xs Z T ζ (0 + n) k - mkc_xs Z T ζ 0 0‖ ≤ C1 * lam := by
      calc ‖mkc_xs Z T ζ (0 + n) k - mkc_xs Z T ζ 0 0‖
          ≤ ‖mkc_xs Z T ζ (0 + n) k - mkc_xs Z T ζ 0 (k / 2 ^ n)‖ + ‖mkc_xs Z T ζ 0 (k / 2 ^ n) - mkc_xs Z T ζ 0 0‖ := by
            refine (norm_sub_le_norm_sub_add_norm_sub _ _ _)
        _ ≤ lam * r ^ (0 + 1) / (1 - r) + lam := add_le_add (hch.trans hgeo) hx0
        _ = C1 * lam := by rw [hC1]; field_simp; ring
    rw [h0] at hsum
    simpa [mkc_xs] using hsum
  -- all the points
  have hall : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖Z t ζ - Z 0 ζ‖ ≤ C1 * lam := by
    intro t ht
    set tn : ℕ → ℝ := fun n => mkc_pt T n (mkc_idx T n t) with htn
    have hmem : ∀ n, tn n ∈ Set.Icc (0 : ℝ) T := fun n => mkc_pt_mem hT n _ (mkc_idx_le hT ht.2 n)
    have hlim : Tendsto tn atTop (𝓝 t) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun n => t - T / 2 ^ n) (h := fun _ => t) ?_
        tendsto_const_nhds (fun n => ?_) (fun n => (mkc_pt_idx hT ht.1 n).1)
      · have : Tendsto (fun n : ℕ => T / 2 ^ n) atTop (𝓝 0) := by
          simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).const_mul T
            |>.congr fun n => by simp [div_eq_mul_inv, inv_pow]
        simpa using tendsto_const_nhds.sub this
      · have := (mkc_pt_idx hT ht.1 n).2
        linarith
    have hT' : Tendsto (fun n => Z (tn n) ζ) atTop (𝓝 (Z t ζ)) :=
      (hc t ht).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hmem⟩)
    have := hT'.sub_const (Z 0 ζ) |>.norm
    exact le_of_tendsto this (Eventually.of_forall fun n => hgrid n _ (mkc_idx_le hT ht.2 n))
  -- conclude
  have hsup : (⨆ t : Set.Icc (0 : ℝ) T, ‖Z t ζ - Z 0 ζ‖ₑ) ≤ ENNReal.ofReal (C1 * lam) :=
    iSup_le fun t => by
      rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hall t t.2)
  refine (pow_le_pow_left₀ zero_le hsup 4).trans ?_
  rw [← ENNReal.ofReal_pow (mul_nonneg hC10.le hlam0), mul_pow, hlam4, ENNReal.ofReal_mul (pow_nonneg hC10.le 4),
    ENNReal.ofReal_toReal hS]

end Det

/-- the constant `C_0(T)` -/
def s57pC0 (T : ℝ) : ℝ := 10 ^ 4 * T ^ 2 * (6561 / 1561)

theorem s57p_sup_moment {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {Z : ℝ → Ω → E} {T A : ℝ} (hT : 0 < T) (hA : 0 ≤ A)
    (hZm : ∀ t, Measurable (Z t)) (hZc : ∀ ζ, ContinuousOn (fun t => Z t ζ) (Set.Icc 0 T))
    (hmom : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T, ∫⁻ ζ, ‖Z t ζ - Z s ζ‖ₑ ^ 4 ∂μ ≤
      ENNReal.ofReal (A * |t - s| ^ 2)) :
    ∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) T, ‖Z t ζ - Z 0 ζ‖ₑ) ^ 4 ∂μ ≤ ENNReal.ofReal (s57pC0 T * A) := by
  set r : ℝ := 9 / 10 with hr
  have hr0 : 0 < r := by norm_num [hr]
  have hr1 : r < 1 := by norm_num [hr]
  set ρ0 : ℝ := 5000 / 6561 with hρ0
  have hρ00 : 0 ≤ ρ0 := by norm_num [hρ0]
  have hρ01 : ρ0 < 1 := by norm_num [hρ0]
  have hC1 : (1 + r / (1 - r)) ^ 4 = 10 ^ 4 := by norm_num [hr]
  -- pointwise
  have hpt : ∀ ζ, (⨆ t : Set.Icc (0 : ℝ) T, ‖Z t ζ - Z 0 ζ‖ₑ) ^ 4 ≤ ENNReal.ofReal (10 ^ 4) * s57pSfun Z T r ζ := by
    intro ζ; have := s57p_sup_det hT hr0 hr1 (Z := Z) ζ (hZc ζ); rwa [hC1] at this
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hS : ∫⁻ ζ, s57pSfun Z T r ζ ∂μ ≤ ENNReal.ofReal (A * T ^ 2 * (6561 / 1561)) := by
    unfold s57pSfun
    have hterm : ∀ (n k : ℕ), Measurable fun ζ => (‖Z (mkc_pt T n (k + 1)) ζ - Z (mkc_pt T n k) ζ‖ₑ / ENNReal.ofReal (r ^ n)) ^ 4 :=
      fun n k => (((hZm _).sub (hZm _)).enorm.div_const _).pow_const 4
    rw [lintegral_tsum (fun n => (Finset.measurable_sum _ fun k _ => hterm n k).aemeasurable)]
    have hn : ∀ n : ℕ, ∫⁻ ζ, ∑ k ∈ Finset.range (2 ^ n), (‖Z (mkc_pt T n (k + 1)) ζ - Z (mkc_pt T n k) ζ‖ₑ /
        ENNReal.ofReal (r ^ n)) ^ 4 ∂μ ≤ ENNReal.ofReal (A * T ^ 2 * ρ0 ^ n) := by
      intro n
      rw [lintegral_finset_sum _ (fun k _ => hterm n k)]
      have hk : ∀ k ∈ Finset.range (2 ^ n), ∫⁻ ζ, (‖Z (mkc_pt T n (k + 1)) ζ - Z (mkc_pt T n k) ζ‖ₑ /
          ENNReal.ofReal (r ^ n)) ^ 4 ∂μ ≤ ENNReal.ofReal (A * (T / 2 ^ n) ^ 2) * (ENNReal.ofReal (r ^ n) ^ 4)⁻¹ := by
        intro k hk
        have hk' : k + 1 ≤ 2 ^ n := Finset.mem_range.1 hk
        have h1 := hmom (mkc_pt T n k) (mkc_pt_mem hT n k (by omega)) (mkc_pt T n (k + 1)) (mkc_pt_mem hT n (k + 1) hk')
        have hsub : |mkc_pt T n (k + 1) - mkc_pt T n k| = T / 2 ^ n := by
          rw [mkc_pt_succ_sub]; exact abs_of_pos (by positivity)
        rw [hsub] at h1
        have hc0 : ENNReal.ofReal (r ^ n) ^ 4 ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.2 (pow_pos hr0 n)).ne'
        have e : ∀ ζ, (‖Z (mkc_pt T n (k + 1)) ζ - Z (mkc_pt T n k) ζ‖ₑ / ENNReal.ofReal (r ^ n)) ^ 4 =
            ‖Z (mkc_pt T n (k + 1)) ζ - Z (mkc_pt T n k) ζ‖ₑ ^ 4 * (ENNReal.ofReal (r ^ n) ^ 4)⁻¹ := fun ζ => by
          rw [div_eq_mul_inv, mul_pow, ENNReal.inv_pow]
        calc ∫⁻ ζ, (‖Z (mkc_pt T n (k + 1)) ζ - Z (mkc_pt T n k) ζ‖ₑ / ENNReal.ofReal (r ^ n)) ^ 4 ∂μ
            = ∫⁻ ζ, ‖Z (mkc_pt T n (k + 1)) ζ - Z (mkc_pt T n k) ζ‖ₑ ^ 4 * (ENNReal.ofReal (r ^ n) ^ 4)⁻¹ ∂μ :=
              lintegral_congr fun ζ => e ζ
          _ = (∫⁻ ζ, ‖Z (mkc_pt T n (k + 1)) ζ - Z (mkc_pt T n k) ζ‖ₑ ^ 4 ∂μ) * (ENNReal.ofReal (r ^ n) ^ 4)⁻¹ :=
              lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hc0)
          _ ≤ _ := mul_le_mul' h1 le_rfl
      refine (Finset.sum_le_sum hk).trans ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hrn : 0 < (r ^ n) ^ 4 := by positivity
      rw [← ENNReal.ofReal_pow (pow_pos hr0 n).le, ← ENNReal.ofReal_inv_of_pos hrn,
        ← ENNReal.ofReal_mul (by positivity), show ((2 ^ n : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ n) by
          rw [ENNReal.ofReal_pow (by norm_num)]; simp, ← ENNReal.ofReal_mul (by positivity)]
      refine le_of_eq (congrArg ENNReal.ofReal ?_)
      have hρ' : ρ0 = (2 * r ^ 4)⁻¹ := by rw [hρ0, hr]; norm_num
      have e1 : (r ^ 4) ^ n = (r ^ n) ^ 4 := by rw [← pow_mul, ← pow_mul, mul_comm]
      have e2 : ρ0 ^ n = ((2 : ℝ) ^ n * (r ^ n) ^ 4)⁻¹ := by rw [hρ', inv_pow, mul_pow, e1]
      rw [e2]
      field_simp
    refine (ENNReal.tsum_le_tsum hn).trans ?_
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) ((summable_geometric_of_lt_one hρ00 hρ01).mul_left _)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [tsum_mul_left, tsum_geometric_of_lt_one hρ00 hρ01, hρ0]
    norm_num
  refine (mul_le_mul' le_rfl hS).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  unfold s57pC0
  ring

end HRS.MS.FixEq
