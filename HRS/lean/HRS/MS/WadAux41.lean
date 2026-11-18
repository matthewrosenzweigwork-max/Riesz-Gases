import HRS.MS.WadAux40

/-!
# S8.3, packet D7 (Route A), part 6: linearity and weighted size of `U_t` on `C_c^∞`

`s85_Ucc_lin`: linearity of `φ ↦ U_t φ` on `C_c^∞`; `s85_Ucc_props`: for `φ ∈ C_c^∞` the function `U_t φ`
is continuous and of weight `⟨x⟩^{M'}` for every `M' ≥ 0` (hence in `C_M` for `M' < M`);
`s85_cm_of_wt`: weight `⟨x⟩^{M'}` with `M' < M` and continuity give `MemCM M`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s85_Cc_lin {c : ℝ} {φ₁ φ₂ : Euc d → ℝ} (h1 : S85Cc φ₁) (h2 : S85Cc φ₂) :
    S85Cc (fun y => c * φ₁ y + φ₂ y) :=
  ⟨(contDiff_const.mul h1.1).add h2.1, HasCompactSupport.add (h1.2.mul_left (f := fun _ => c)) h2.2⟩

theorem s85_Ucc_lin (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {t : ℝ} (ht : 0 ≤ t) {c : ℝ}
    {φ₁ φ₂ : Euc d → ℝ} (h1 : S85Cc φ₁) (h2 : S85Cc φ₂) (x : Euc d) :
    s85_Ucc a β ρβ t (fun y => c * φ₁ y + φ₂ y) x =
      c * s85_Ucc a β ρβ t φ₁ x + s85_Ucc a β ρβ t φ₂ x := by
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρβ) := s85_isProb hρ.1.1
  obtain ⟨w₁, hw₁⟩ := s85_exists_cl hd ha hβ hρ ht h1
  obtain ⟨w₂, hw₂⟩ := s85_exists_cl hd ha hβ hρ ht h2
  obtain ⟨w, hw⟩ := s85_exists_cl hd ha hβ hρ ht (s85_Cc_lin (c := c) h1 h2)
  rw [s85_Ucc_eq hd ha hβ hρ ht hw, s85_Ucc_eq hd ha hβ hρ ht hw₁, s85_Ucc_eq hd ha hβ hρ ht hw₂]
  obtain ⟨i1, iφ1⟩ := s85_cl_int hd ha hβ hρ ht hw₁
  obtain ⟨i2, iφ2⟩ := s85_cl_int hd ha hβ hρ ht hw₂
  have hw0 : ∀ y, w 0 y = c * w₁ 0 y + w₂ 0 y := by
    rcases ht.eq_or_lt with h0 | hpos
    · subst h0
      intro y
      have a1 := congrFun hw.terminal y
      have b1 := congrFun hw₁.terminal y
      have c1 := congrFun hw₂.terminal y
      rw [a1, b1, c1]
    · intro y
      exact s85_cl_lin hd ha hβ hρ hpos hw₁ hw₂ hw (fun y => rfl) ⟨le_rfl, ht⟩ y
  unfold s85_V
  have hpair : ∀ φ : Euc d → ℝ, HRS.Whole.pair (HRS.Whole.withDensityReal ρβ) φ = ∫ z, φ z ∂(HRS.Whole.withDensityReal ρβ) :=
    fun φ => rfl
  rw [hpair, hpair, hpair]
  have e1 : ∫ z, w 0 z ∂(HRS.Whole.withDensityReal ρβ) =
      c * ∫ z, w₁ 0 z ∂(HRS.Whole.withDensityReal ρβ) + ∫ z, w₂ 0 z ∂(HRS.Whole.withDensityReal ρβ) := by
    simp_rw [hw0]
    rw [integral_add (i1.const_mul c) i2, integral_const_mul]
  have e2 : ∫ z, (c * φ₁ z + φ₂ z) ∂(HRS.Whole.withDensityReal ρβ) =
      c * ∫ z, φ₁ z ∂(HRS.Whole.withDensityReal ρβ) + ∫ z, φ₂ z ∂(HRS.Whole.withDensityReal ρβ) := by
    rw [integral_add (iφ1.const_mul c) iφ2, integral_const_mul]
  rw [e1, e2, hw0 x]
  ring

theorem s85_tendsto_jb : Tendsto (fun x : Euc d => jbracket x) (cocompact (Euc d)) atTop :=
  tendsto_atTop_mono (fun x => s83_norm_le_jb x) tendsto_norm_cocompact_atTop

/-- Continuity and weight `⟨x⟩^{M'}` with `M' < M` give membership in `C_M`. -/
theorem s85_cm_of_wt {M M' Φ : ℝ} (hM : M' < M) {f : Euc d → ℝ} (hc : Continuous f) (hw : Wt M' Φ f) :
    MemCM M f := by
  refine ⟨hc, ?_⟩
  have hexp : Tendsto (fun x : Euc d => jbracket x ^ (-(M - M'))) (cocompact (Euc d)) (𝓝 0) :=
    (tendsto_rpow_neg_atTop (sub_pos.2 hM)).comp s85_tendsto_jb
  have h1 : Tendsto (fun x : Euc d => Φ * jbracket x ^ (-(M - M'))) (cocompact (Euc d)) (𝓝 0) := by
    simpa using hexp.const_mul Φ
  refine squeeze_zero_norm (fun x => ?_) h1
  have hp : 0 < jbracket x ^ M := Real.rpow_pos_of_pos (s83_jb_pos x) _
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hp, div_le_iff₀ hp]
  have e : jbracket x ^ (-(M - M')) * jbracket x ^ M = jbracket x ^ M' := by
    rw [← Real.rpow_add (s83_jb_pos x)]; congr 1; ring
  have := hw x
  rw [Real.norm_eq_abs] at this
  calc |f x| ≤ Φ * jbracket x ^ M' := this
    _ = Φ * jbracket x ^ (-(M - M')) * jbracket x ^ M := by rw [mul_assoc, e]

/-- For `φ ∈ C_c^∞`: `U_t φ` is continuous and of weight `⟨x⟩^{M'}`, uniformly bounded constant. -/
theorem s85_Ucc_props (hd : 2 ≤ d) {a β T M' : ℝ} (ha : 0 < a) (hβ : 0 < β) (hT : 0 < T) (hM' : 0 ≤ M')
    {ρβ : Euc d → ℝ} (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {t : ℝ} (ht : 0 ≤ t)
    (htT : t ≤ T) {φ : Euc d → ℝ} (hφ : S85Cc φ) :
    Continuous (s85_Ucc a β ρβ t φ) ∧ ∃ C, Wt M' C (s85_Ucc a β ρβ t φ) := by
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρβ) := s85_isProb hρ.1.1
  obtain ⟨w, hw⟩ := s85_exists_cl hd ha hβ hρ ht hφ
  obtain ⟨B0, BG, hB0, hBG0, hb0, hbG, hwc, hGc⟩ := s85_cl_facts hd ha hβ hρ hw
  have hUeq : ∀ x, s85_Ucc a β ρβ t φ x = s85_V ρβ w φ x := s85_Ucc_eq hd ha hβ hρ ht hw
  have hcont : Continuous (s85_Ucc a β ρβ t φ) := by
    have : Continuous (s85_V ρβ w φ) :=
      (((hw.c2 0 ⟨le_rfl, ht⟩).continuous.sub continuous_const).add continuous_const)
    exact this.congr fun x => (hUeq x).symm
  refine ⟨hcont, ?_⟩
  obtain ⟨Bφ, hBφ⟩ := hφ.1.continuous.bounded_above_of_compact_support hφ.2
  have hBφ0 : 0 ≤ Bφ := (norm_nonneg _).trans (hBφ 0)
  have hJ : ∀ x : Euc d, 1 ≤ jbracket x ^ M' := fun x => Real.one_le_rpow (s83_one_le_jb x) hM'
  have hwφ : Wt M' Bφ φ := fun x => (hBφ x).trans (le_mul_of_one_le_right hBφ0 (hJ x))
  have hI1 : |∫ z, w 0 z ∂(HRS.Whole.withDensityReal ρβ)| ≤ B0 := by
    have := s85_abs_integral_le (μ := HRS.Whole.withDensityReal ρβ) (h := w 0) (bd := fun _ => B0)
      (integrable_const B0) (fun z => hb0 0 ⟨le_rfl, ht⟩ z)
    simpa using this
  have hI2 : |HRS.Whole.pair (HRS.Whole.withDensityReal ρβ) φ| ≤ Bφ := by
    have := s85_abs_integral_le (μ := HRS.Whole.withDensityReal ρβ) (h := φ) (bd := fun _ => Bφ)
      (integrable_const Bφ) (fun z => by simpa [Real.norm_eq_abs] using hBφ z)
    simpa [HRS.Whole.pair] using this
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    refine ⟨Bφ, fun x => ?_⟩
    rw [Real.norm_eq_abs, hUeq x]
    unfold s85_V
    rw [hw.terminal]
    have : φ x - ∫ z, φ z ∂(HRS.Whole.withDensityReal ρβ) + HRS.Whole.pair (HRS.Whole.withDensityReal ρβ) φ = φ x := by
      unfold HRS.Whole.pair; ring
    rw [this]
    have := hwφ x
    rwa [Real.norm_eq_abs] at this
  · obtain ⟨K, hK0, hK⟩ := s84_apriori_classical hd ha hβ hT hM' hρ
    have hb : ∀ x, |w 0 x| ≤ K * Bφ * jbracket x ^ M' := fun x =>
      hK hpos htT hw hwφ 0 ⟨le_rfl, ht⟩ x
    refine ⟨K * Bφ + B0 + Bφ, fun x => ?_⟩
    rw [Real.norm_eq_abs, hUeq x]
    unfold s85_V
    have h1 := hb x
    have h2 := hJ x
    have habs : |w 0 x - ∫ z, w 0 z ∂(HRS.Whole.withDensityReal ρβ) + HRS.Whole.pair (HRS.Whole.withDensityReal ρβ) φ| ≤
        |w 0 x| + |∫ z, w 0 z ∂(HRS.Whole.withDensityReal ρβ)| + |HRS.Whole.pair (HRS.Whole.withDensityReal ρβ) φ| := by
      have := abs_add_three (w 0 x) (-∫ z, w 0 z ∂(HRS.Whole.withDensityReal ρβ)) (HRS.Whole.pair (HRS.Whole.withDensityReal ρβ) φ)
      simpa [sub_eq_add_neg, abs_neg] using this
    have hB0' : 0 ≤ B0 := hB0
    have hKB : 0 ≤ K * Bφ := mul_nonneg hK0 hBφ0
    nlinarith [mul_nonneg hB0' (sub_nonneg.2 h2), mul_nonneg hBφ0 (sub_nonneg.2 h2)]

end HRS.MS.Wad
