import HRS.MS.WadAux67

/-!
# S8.3, packet S8D-2, part 14: the Lasota-Yorke inequality for `S = U_1 - Π`

`s8d_far`: for `‖x‖ ≥ R` one has `|U_1 y(x) - μ(y)| ≤ Φ (e^{-aM} + 2ε) ⟨x⟩^M` (`s8d_tail_U1` and the Gaussian moment of `y`).
`s8d_near`: for `‖x‖ ≤ R₀`, `|U_1 y(x) - μ(y)| ≤ Φ/2 + C' ‖U_1 y - μ(y)‖_{L²(μ)}` (positive-time smoothing `s8d_smoothing` gives
the Lipschitz bound, `s8d_interp` the local interpolation).
`s8d_LY`: the combination, `|S y| ≤ (θ' Φ + C' ‖S y‖_{L²(μ)}) ⟨x⟩^M` with `θ' < 1`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8d_far (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hMpos : 0 < M) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ {y : Euc d → ℝ} {Φ : ℝ}, MemCM M y → Wt M Φ y → ∀ x : Euc d, R ≤ ‖x‖ →
      |s85_Ulim a β ρβ M 1 y x - ∫ z, y z ∂(HRS.Whole.withDensityReal ρβ)| ≤
        Φ * (Real.exp (-a * M) + ε + ε) * jbracket x ^ M := by
  have hM := hMpos.le
  have hP : HRS.Whole.IsProbDensity ρβ := hρ.1.1
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρβ) := s85_isProb hP
  have hg : s84_GaussReg ρβ := s84_thermal_gaussReg hd ha hβ hρ
  have H1 : S85Hyp d a β 1 M ρβ := ⟨hd, ha, hβ, one_pos, hM, hρ⟩
  obtain ⟨R₁, hR₁⟩ := s8d_tail_U1 H1 hMpos hε
  have hjint : Integrable (fun z : Euc d => jbracket z ^ M) (HRS.Whole.withDensityReal ρβ) :=
    s85_jb_integrable hP hg hM
  obtain ⟨mM, hmM0, hmM⟩ : ∃ mM : ℝ, 0 ≤ mM ∧ mM = ∫ z, jbracket z ^ M ∂(HRS.Whole.withDensityReal ρβ) :=
    ⟨_, integral_nonneg fun z => Real.rpow_nonneg (s83_jb_pos z).le _, rfl⟩
  obtain ⟨N₂, hN₂0, hN₂⟩ : ∃ N₂ : ℝ, 0 ≤ N₂ ∧ N₂ = mM / ε := ⟨_, by positivity, rfl⟩
  refine ⟨max R₁ (N₂ ^ (1 / M)), fun {y Φ} hy hΦ x hx => ?_⟩
  have hΦ0 : 0 ≤ Φ := hΦ.nonneg
  have hxR₁ : R₁ ≤ ‖x‖ := (le_max_left _ _).trans hx
  have hxN : N₂ ^ (1 / M) ≤ ‖x‖ := (le_max_right _ _).trans hx
  have hjx : N₂ ≤ jbracket x ^ M := by
    have h1 : N₂ = (N₂ ^ (1 / M)) ^ M := by
      rw [← Real.rpow_mul hN₂0, one_div, inv_mul_cancel₀ hMpos.ne', Real.rpow_one]
    calc N₂ = (N₂ ^ (1 / M)) ^ M := h1
      _ ≤ ‖x‖ ^ M := Real.rpow_le_rpow (Real.rpow_nonneg hN₂0 _) hxN hM
      _ ≤ jbracket x ^ M := Real.rpow_le_rpow (norm_nonneg _) (s83_norm_le_jb x) hM
  have hcb : |∫ z, y z ∂(HRS.Whole.withDensityReal ρβ)| ≤ Φ * mM := by
    have := s85_abs_integral_le (μ := HRS.Whole.withDensityReal ρβ) (h := y)
      (bd := fun z => Φ * jbracket z ^ M) (hjint.const_mul Φ) (fun z => by
        have := hΦ z; rwa [Real.norm_eq_abs] at this)
    rw [integral_const_mul] at this
    rw [hmM]; exact this
  have h1 := hR₁ hy hΦ x hxR₁
  have h2 : mM ≤ ε * jbracket x ^ M := by
    have := mul_le_mul_of_nonneg_right hjx hε.le
    have e : N₂ * ε = mM := by rw [hN₂]; field_simp
    linarith
  have h3 := abs_sub (s85_Ulim a β ρβ M 1 y x) (∫ z, y z ∂(HRS.Whole.withDensityReal ρβ))
  have h4 : Φ * mM ≤ Φ * (ε * jbracket x ^ M) := mul_le_mul_of_nonneg_left h2 hΦ0
  nlinarith [h1, h3, h4, hcb]

theorem s8d_near (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hMpos : 0 < M) (R₀ : ℝ) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ {y : Euc d → ℝ} {Φ : ℝ}, MemCM M y → Wt M Φ y → ∀ x : Euc d, ‖x‖ ≤ R₀ →
      |s85_Ulim a β ρβ M 1 y x - ∫ z, y z ∂(HRS.Whole.withDensityReal ρβ)| ≤
        1 / 2 * Φ + C' * Real.sqrt (∫ z, (s85_Ulim a β ρβ M 1 y z -
          ∫ w, y w ∂(HRS.Whole.withDensityReal ρβ)) ^ 2 ∂(HRS.Whole.withDensityReal ρβ)) := by
  have hM := hMpos.le
  have hd1 : 1 ≤ d := by omega
  have hP : HRS.Whole.IsProbDensity ρβ := hρ.1.1
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρβ) := s85_isProb hP
  have hg : s84_GaussReg ρβ := s84_thermal_gaussReg hd ha hβ hρ
  have H1 : S85Hyp d a β 1 M ρβ := ⟨hd, ha, hβ, one_pos, hM, hρ⟩
  have hs0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨Bg, -, hR, -⟩ := HRS.MS.Mov0.mv0_gapref hd hs0 hsd ha hβ hρ
  have hρpos : ∀ x, 0 < ρβ x := hR.pos
  have hρc : Continuous ρβ := hg.1.continuous
  obtain ⟨Ks, hKs0, hKs⟩ := s8d_smoothing H1 hMpos
  obtain ⟨Kb, hKb0, hKb⟩ := s85_Ulim_bound H1
  have hjint : Integrable (fun z : Euc d => jbracket z ^ M) (HRS.Whole.withDensityReal ρβ) :=
    s85_jb_integrable hP hg hM
  have hj2 := s8d_jb_sq_integrable hP hg hM
  obtain ⟨mM, hmM0, hmM⟩ : ∃ mM : ℝ, 0 ≤ mM ∧ mM = ∫ z, jbracket z ^ M ∂(HRS.Whole.withDensityReal ρβ) :=
    ⟨_, integral_nonneg fun z => Real.rpow_nonneg (s83_jb_pos z).le _, rfl⟩
  have hR0 : 0 ≤ |R₀| := abs_nonneg _
  obtain ⟨Ks', hKs'0, hKs'⟩ : ∃ Ks' : ℝ, 0 ≤ Ks' ∧ Ks' = Ks * (|R₀| + 2) ^ M := ⟨_, by positivity, rfl⟩
  obtain ⟨η, hη0, hη1, hKη⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ Ks' * η ≤ 1 / 2 := by
    refine ⟨min 1 (1 / (2 * (Ks' + 1))), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
    have h1 : min 1 (1 / (2 * (Ks' + 1))) ≤ 1 / (2 * (Ks' + 1)) := min_le_right _ _
    calc Ks' * min 1 (1 / (2 * (Ks' + 1))) ≤ Ks' * (1 / (2 * (Ks' + 1))) :=
          mul_le_mul_of_nonneg_left h1 hKs'0
      _ ≤ 1 / 2 := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  obtain ⟨ρ₀, hρ₀, hint⟩ := s8d_interp hd1 hρc hρpos hP.measurable |R₀|
  obtain ⟨om, hom⟩ : ∃ om : ℝ, om = (volume (ball (0 : Euc d) 1)).toReal := ⟨_, rfl⟩
  have hom0 : 0 < om := by
    rw [hom]
    exact ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne' (measure_ball_lt_top).ne
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = 1 / Real.sqrt (ρ₀ * om * η ^ d) := ⟨_, rfl⟩
  have hC'0 : 0 ≤ C' := by rw [hC']; positivity
  refine ⟨C', hC'0, fun {y Φ} hy hΦ x hx => ?_⟩
  have hΦ0 : 0 ≤ Φ := hΦ.nonneg
  have hcb : |∫ z, y z ∂(HRS.Whole.withDensityReal ρβ)| ≤ Φ * mM := by
    have := s85_abs_integral_le (μ := HRS.Whole.withDensityReal ρβ) (h := y)
      (bd := fun z => Φ * jbracket z ^ M) (hjint.const_mul Φ) (fun z => by
        have := hΦ z; rwa [Real.norm_eq_abs] at this)
    rw [integral_const_mul] at this
    rw [hmM]; exact this
  obtain ⟨hC1, hgrad, -⟩ := hKs one_pos le_rfl hy hΦ
  have hU1 : Differentiable ℝ (s85_Ulim a β ρβ M 1 y) := hC1.1.differentiable one_ne_zero
  have hlip : ∀ z : Euc d, ‖z - x‖ ≤ 1 →
      |(s85_Ulim a β ρβ M 1 y z - ∫ w, y w ∂(HRS.Whole.withDensityReal ρβ)) -
        (s85_Ulim a β ρβ M 1 y x - ∫ w, y w ∂(HRS.Whole.withDensityReal ρβ))| ≤ (Ks' * Φ) * ‖z - x‖ :=
    fun z hz => by
      have hbd : ∀ w ∈ closedBall x 1, ‖fderiv ℝ (s85_Ulim a β ρβ M 1 y) w‖ ≤ Ks' * Φ := fun w hw => by
        rw [mem_closedBall_iff_norm'] at hw
        have h1 := hgrad w
        rw [Real.one_rpow, mul_one] at h1
        refine h1.trans ?_
        have hjw : jbracket w ^ M ≤ (|R₀| + 2) ^ M := by
          refine Real.rpow_le_rpow (s83_jb_pos w).le ((s83_jb_le_one_add w).trans ?_) hM
          have : ‖w‖ ≤ ‖x‖ + 1 := by
            have := norm_le_norm_add_norm_sub' w x
            rw [norm_sub_rev] at this
            linarith
          have := le_abs_self R₀
          linarith
        rw [hKs']
        nlinarith [mul_nonneg hKs0 hΦ0, mul_le_mul_of_nonneg_left hjw (mul_nonneg hKs0 hΦ0)]
      have hmv := (convex_closedBall x 1).norm_image_sub_le_of_norm_fderiv_le
        (f := s85_Ulim a β ρβ M 1 y) (C := Ks' * Φ) (fun w _ => hU1 w) hbd
        (mem_closedBall_self zero_le_one) (show z ∈ closedBall x 1 by
          rw [mem_closedBall_iff_norm]; exact hz)
      rw [Real.norm_eq_abs] at hmv
      have e : (s85_Ulim a β ρβ M 1 y z - ∫ w, y w ∂(HRS.Whole.withDensityReal ρβ)) -
          (s85_Ulim a β ρβ M 1 y x - ∫ w, y w ∂(HRS.Whole.withDensityReal ρβ)) =
          s85_Ulim a β ρβ M 1 y z - s85_Ulim a β ρβ M 1 y x := by ring
      rw [e]
      exact hmv
  -- integrability of `h²`
  have hUb : ∀ z, |s85_Ulim a β ρβ M 1 y z| ≤ Kb * Φ * jbracket z ^ M := fun z => by
    have := hKb zero_le_one le_rfl hy (s85_zero_memCM M) (Φ := Φ) (fun w => by simpa using hΦ w) z
    rw [s85_Ulim_zero_fun H1 zero_le_one le_rfl, sub_zero] at this
    exact this
  have hhb : ∀ z, |s85_Ulim a β ρβ M 1 y z - ∫ w, y w ∂(HRS.Whole.withDensityReal ρβ)| ≤
      (Kb * Φ + Φ * mM) * jbracket z ^ M := fun z => by
    have h1 := hUb z
    have h2 := abs_sub (s85_Ulim a β ρβ M 1 y z) (∫ w, y w ∂(HRS.Whole.withDensityReal ρβ))
    have h3 := Real.one_le_rpow (s83_one_le_jb z) hM
    nlinarith [mul_nonneg hΦ0 hmM0]
  have hmeas : AEStronglyMeasurable (fun z => s85_Ulim a β ρβ M 1 y z -
      ∫ w, y w ∂(HRS.Whole.withDensityReal ρβ)) (HRS.Whole.withDensityReal ρβ) :=
    ((s85_Ulim_memCM H1 hMpos zero_le_one le_rfl hy).1.sub continuous_const).aestronglyMeasurable
  have hint2 : Integrable (fun z => (s85_Ulim a β ρβ M 1 y z -
      ∫ w, y w ∂(HRS.Whole.withDensityReal ρβ)) ^ 2) (HRS.Whole.withDensityReal ρβ) := by
    refine (hj2.const_mul ((Kb * Φ + Φ * mM) ^ 2)).mono' (hmeas.pow 2) (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc _ = |s85_Ulim a β ρβ M 1 y z - ∫ w, y w ∂(HRS.Whole.withDensityReal ρβ)| ^ 2 := (sq_abs _).symm
      _ ≤ ((Kb * Φ + Φ * mM) * jbracket z ^ M) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hhb z) 2
      _ = _ := by ring
  have key := hint (h := fun z => s85_Ulim a β ρβ M 1 y z - ∫ w, y w ∂(HRS.Whole.withDensityReal ρβ))
    (L := Ks' * Φ) (r := η) (x₀ := x) (mul_nonneg hKs'0 hΦ0) hη0 hη1 (hx.trans (le_abs_self R₀)) hlip hint2
  have h3 : Real.sqrt (∫ z, (s85_Ulim a β ρβ M 1 y z - ∫ w, y w ∂(HRS.Whole.withDensityReal ρβ)) ^ 2
      ∂(HRS.Whole.withDensityReal ρβ)) / Real.sqrt (ρ₀ * om * η ^ d) =
      C' * Real.sqrt (∫ z, (s85_Ulim a β ρβ M 1 y z - ∫ w, y w ∂(HRS.Whole.withDensityReal ρβ)) ^ 2
      ∂(HRS.Whole.withDensityReal ρβ)) := by
    rw [hC']; ring
  rw [hom] at h3
  rw [h3] at key
  have h2 : Ks' * Φ * η ≤ 1 / 2 * Φ := by
    nlinarith [mul_le_mul_of_nonneg_right hKη hΦ0]
  linarith

theorem s8d_LY (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hMpos : 0 < M) :
    ∃ θ' C' : ℝ, 0 ≤ θ' ∧ θ' < 1 ∧ 0 ≤ C' ∧ ∀ {y : Euc d → ℝ} {Φ : ℝ}, MemCM M y → Wt M Φ y →
      ∀ x : Euc d, |s85_Ulim a β ρβ M 1 y x - ∫ z, y z ∂(HRS.Whole.withDensityReal ρβ)| ≤
        (θ' * Φ + C' * Real.sqrt (∫ z, (s85_Ulim a β ρβ M 1 y z -
          ∫ w, y w ∂(HRS.Whole.withDensityReal ρβ)) ^ 2 ∂(HRS.Whole.withDensityReal ρβ))) *
          jbracket x ^ M := by
  have he0pos : 0 < Real.exp (-a * M) := Real.exp_pos _
  have he0lt : Real.exp (-a * M) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith
  obtain ⟨ε₁, hε₁0, hε₁⟩ : ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ = (1 - Real.exp (-a * M)) / 4 :=
    ⟨_, by linarith, rfl⟩
  obtain ⟨R₁, hR₁⟩ := s8d_far hd ha hβ hρ hMpos hε₁0
  obtain ⟨C', hC'0, hnear⟩ := s8d_near hd ha hβ hρ hMpos R₁
  have hθ : Real.exp (-a * M) + ε₁ + ε₁ ≤ (3 + Real.exp (-a * M)) / 4 := by rw [hε₁]; linarith
  refine ⟨(3 + Real.exp (-a * M)) / 4, C', by linarith, by linarith, hC'0, fun {y Φ} hy hΦ x => ?_⟩
  have hΦ0 := hΦ.nonneg
  have hjx1 : 1 ≤ jbracket x ^ M := Real.one_le_rpow (s83_one_le_jb x) hMpos.le
  have hNh0 := Real.sqrt_nonneg (∫ z, (s85_Ulim a β ρβ M 1 y z -
          ∫ w, y w ∂(HRS.Whole.withDensityReal ρβ)) ^ 2 ∂(HRS.Whole.withDensityReal ρβ))
  by_cases hxR : R₁ ≤ ‖x‖
  · have h1 := hR₁ hy hΦ x hxR
    have hPJ : 0 ≤ Φ * jbracket x ^ M := mul_nonneg hΦ0 (by linarith)
    have h2 := mul_le_mul_of_nonneg_left hθ hPJ
    have h3 : 0 ≤ C' * Real.sqrt (∫ z, (s85_Ulim a β ρβ M 1 y z -
          ∫ w, y w ∂(HRS.Whole.withDensityReal ρβ)) ^ 2 ∂(HRS.Whole.withDensityReal ρβ)) *
        jbracket x ^ M := mul_nonneg (mul_nonneg hC'0 hNh0) (by linarith)
    nlinarith
  · push Not at hxR
    have h1 := hnear hy hΦ x hxR.le
    have hθ' : 1 / 2 ≤ (3 + Real.exp (-a * M)) / 4 := by linarith
    have h2 : 1 / 2 * Φ ≤ (3 + Real.exp (-a * M)) / 4 * Φ := mul_le_mul_of_nonneg_right hθ' hΦ0
    calc _ ≤ 1 / 2 * Φ + C' * Real.sqrt (∫ z, (s85_Ulim a β ρβ M 1 y z -
          ∫ w, y w ∂(HRS.Whole.withDensityReal ρβ)) ^ 2 ∂(HRS.Whole.withDensityReal ρβ)) := h1
      _ ≤ (3 + Real.exp (-a * M)) / 4 * Φ + C' * Real.sqrt (∫ z, (s85_Ulim a β ρβ M 1 y z -
          ∫ w, y w ∂(HRS.Whole.withDensityReal ρβ)) ^ 2 ∂(HRS.Whole.withDensityReal ρβ)) := by linarith
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hjx1

end HRS.MS.Wad
