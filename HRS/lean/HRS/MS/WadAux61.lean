import HRS.MS.WadAux60

/-!
# S8.3, packet S8D-2, part 7: essential-radius estimate for `U_1` on `C_M`

`s8d_tail_Ucc`: for `φ ∈ C_c^∞` with `|φ| ≤ Φ⟨x⟩^M`: `|U_1 φ(x)| ≤ Φ (e^{-aM} + ε) ⟨x⟩^M` for `‖x‖ ≥ R`
(`R` independent of `φ`): the classical far-field bound `s8d_tail_classical` plus the two constants
`μ(w_0)`, `μ(φ)` of the projected solution (Gaussian moments).
`s8d_tail_U1`: the same for the extension `U_1 f`, `f ∈ C_M` (by the approximating sequence).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

set_option maxHeartbeats 800000 in
theorem s8d_tail_Ucc (hd : 2 ≤ d) {a β M : ℝ} {ρβ : Euc d → ℝ} (ha : 0 < a) (hβ : 0 < β)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hMpos : 0 < M) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ {Φ : ℝ} {φ : Euc d → ℝ}, S85Cc φ → Wt M Φ φ →
      ∀ x : Euc d, R ≤ ‖x‖ →
        |s85_Ucc a β ρβ 1 φ x| ≤ Φ * (Real.exp (-a * M) + ε) * jbracket x ^ M := by
  have hM := hMpos.le
  have hP : HRS.Whole.IsProbDensity ρβ := hρ.1.1
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρβ) := s85_isProb hP
  have hg : s84_GaussReg ρβ := s84_thermal_gaussReg hd ha hβ hρ
  obtain ⟨Kap, hKap0, hKap⟩ := s84_apriori_classical hd ha hβ (T := 1) (M := M) one_pos hM hρ
  obtain ⟨R₁, hR₁⟩ := s8d_tail_classical hd ha hβ hρ hMpos (ε := ε / 2) (by positivity)
  set mM : ℝ := ∫ z, jbracket z ^ M ∂(HRS.Whole.withDensityReal ρβ) with hmM
  have hmM0 : 0 ≤ mM := integral_nonneg fun z => Real.rpow_nonneg (s83_jb_pos z).le _
  have hjint : Integrable (fun z : Euc d => jbracket z ^ M) (HRS.Whole.withDensityReal ρβ) :=
    s85_jb_integrable hP hg hM
  set N : ℝ := 2 * (Kap + 1) * mM / ε with hN
  have hN0 : 0 ≤ N := by positivity
  refine ⟨max R₁ (N ^ (1 / M)), ?_⟩
  intro Φ φ hφcc hφ x hx
  have hxR₁ : R₁ ≤ ‖x‖ := (le_max_left _ _).trans hx
  have hxN : N ^ (1 / M) ≤ ‖x‖ := (le_max_right _ _).trans hx
  have hΦ0 : 0 ≤ Φ := hφ.nonneg
  have hjx : N ≤ jbracket x ^ M := by
    have h1 : N = (N ^ (1 / M)) ^ M := by
      rw [← Real.rpow_mul hN0, one_div, inv_mul_cancel₀ hMpos.ne', Real.rpow_one]
    calc N = (N ^ (1 / M)) ^ M := h1
      _ ≤ ‖x‖ ^ M := Real.rpow_le_rpow (Real.rpow_nonneg hN0 _) hxN hM
      _ ≤ jbracket x ^ M := Real.rpow_le_rpow (norm_nonneg _) (s83_norm_le_jb x) hM
  obtain ⟨w, hw⟩ := s85_exists_cl hd ha hβ hρ zero_le_one hφcc
  rw [s85_Ucc_eq hd ha hβ hρ zero_le_one hw x]
  have hw0 := hR₁ hw hφ x hxR₁
  have hbw : ∀ y, |w 0 y| ≤ Kap * Φ * jbracket y ^ M := fun y =>
    hKap one_pos le_rfl hw hφ 0 ⟨le_rfl, zero_le_one⟩ y
  have hI1 : |∫ z, w 0 z ∂(HRS.Whole.withDensityReal ρβ)| ≤ Kap * Φ * mM := by
    have := s85_abs_integral_le (μ := HRS.Whole.withDensityReal ρβ) (h := w 0)
      (bd := fun z => Kap * Φ * jbracket z ^ M) (hjint.const_mul (Kap * Φ)) hbw
    rwa [integral_const_mul] at this
  have hI2 : |HRS.Whole.pair (HRS.Whole.withDensityReal ρβ) φ| ≤ Φ * mM := by
    have := s85_abs_integral_le (μ := HRS.Whole.withDensityReal ρβ) (h := φ)
      (bd := fun z => Φ * jbracket z ^ M) (hjint.const_mul Φ) (fun y => by
        have := hφ y; rwa [Real.norm_eq_abs] at this)
    rw [integral_const_mul] at this
    simpa [HRS.Whole.pair] using this
  unfold s85_V
  have habs : |w 0 x - ∫ z, w 0 z ∂(HRS.Whole.withDensityReal ρβ) +
      HRS.Whole.pair (HRS.Whole.withDensityReal ρβ) φ| ≤ |w 0 x| +
      |∫ z, w 0 z ∂(HRS.Whole.withDensityReal ρβ)| + |HRS.Whole.pair (HRS.Whole.withDensityReal ρβ) φ| := by
    have := abs_add_three (w 0 x) (-∫ z, w 0 z ∂(HRS.Whole.withDensityReal ρβ))
      (HRS.Whole.pair (HRS.Whole.withDensityReal ρβ) φ)
    simpa [sub_eq_add_neg, abs_neg] using this
  have hcon : (Kap * Φ * mM + Φ * mM) ≤ ε / 2 * (Φ * jbracket x ^ M) := by
    have h1 : 2 * (Kap + 1) * mM ≤ ε * jbracket x ^ M := by
      have := mul_le_mul_of_nonneg_right hjx (show 0 ≤ ε by linarith)
      have e : N * ε = 2 * (Kap + 1) * mM := by rw [hN]; field_simp
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hΦ0]
  show |w 0 x - ∫ z, w 0 z ∂(HRS.Whole.withDensityReal ρβ) +
      HRS.Whole.pair (HRS.Whole.withDensityReal ρβ) φ| ≤ _
  refine habs.trans ?_
  nlinarith [hw0, hI1, hI2, hcon]

theorem s8d_tail_U1 {a β M : ℝ} {ρβ : Euc d → ℝ} (H : S85Hyp d a β 1 M ρβ) (hMpos : 0 < M) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ R : ℝ, ∀ {Φ : ℝ} {f : Euc d → ℝ}, MemCM M f → Wt M Φ f →
      ∀ x : Euc d, R ≤ ‖x‖ →
        |s85_Ulim a β ρβ M 1 f x| ≤ Φ * (Real.exp (-a * M) + ε) * jbracket x ^ M := by
  obtain ⟨hd, ha, hβ, hT, hM, hρ⟩ := id H
  obtain ⟨R, hR⟩ := s8d_tail_Ucc hd ha hβ hρ hMpos hε
  refine ⟨R, fun {Φ f} hf hΦ x hx => ?_⟩
  obtain ⟨φ, hφ⟩ := s85_exists_approx hM hf
  have hφ' := hφ
  obtain ⟨hcc, C, hC0, hC⟩ := hφ'
  set e : ℕ → ℝ := fun n => C / ((n : ℝ) + 1) with he_def
  have he0 : ∀ n, 0 ≤ e n := fun n => by positivity
  have he : Tendsto e atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
    simpa [e, div_eq_mul_inv] using this
  have hφn : ∀ n, Wt M (Φ + e n) (φ n) := fun n y => by
    have h1 := hC n y
    have h2 := hΦ y
    have h3 : ‖φ n y‖ ≤ ‖φ n y - f y‖ + ‖f y‖ := by
      have := norm_add_le (φ n y - f y) (f y)
      simpa using this
    have hj := Real.rpow_nonneg (s83_jb_pos y).le M
    nlinarith
  have hlim : Tendsto (fun n => (Φ + e n) * (Real.exp (-a * M) + ε) * jbracket x ^ M) atTop
      (𝓝 ((Φ + 0) * (Real.exp (-a * M) + ε) * jbracket x ^ M)) :=
    (((he.const_add Φ).mul_const _).mul_const _)
  have := le_of_tendsto_of_tendsto' ((s85_Ulim_spec H zero_le_one le_rfl hφ x).abs) hlim
    (fun n => hR (hcc n) (hφn n) x hx)
  simpa using this

end HRS.MS.Wad
