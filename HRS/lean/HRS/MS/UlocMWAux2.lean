import HRS.MS.UlocMWAux1

/-!
# MS-ULOC-MW, part 2: `H^s` norm of a modulated cutoff `χ(x) cos(2π k·x + φ)`

Translation of the spectrum of `χ̂` by `±k` and Peetre's inequality give
`‖χ cos(2π k·x + φ)‖²_{H^s} ≤ 2^s ⟨k⟩^{2s} ‖χ‖²_{H^s}` (`um_mod_bound`).
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform ContDiff

namespace HRS.MS.UlocMW
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

/-- the plane wave `e^{2πi c·x}` -/
def um_E (c x : Euc d) : ℂ := Complex.exp (((2 * Real.pi * inner ℝ c x : ℝ) : ℂ) * Complex.I)

theorem um_E_norm (c x : Euc d) : ‖um_E c x‖ = 1 := by
  unfold um_E; exact Complex.norm_exp_ofReal_mul_I _

theorem um_fourier_E (X : Euc d → ℂ) (c ξ : Euc d) :
    𝓕 (fun x => um_E c x * X x) ξ = 𝓕 X (ξ - c) := by
  rw [Real.fourier_eq', Real.fourier_eq']
  congr 1; ext x
  rw [smul_eq_mul, smul_eq_mul, ← mul_assoc]
  unfold um_E
  rw [← Complex.exp_add, ← add_mul]
  congr 3
  push_cast
  rw [inner_sub_right, real_inner_comm c x]
  push_cast
  ring

theorem um_E_continuous (c : Euc d) : Continuous (um_E c) := by
  unfold um_E; fun_prop

theorem um_integrable_E {X : Euc d → ℂ} (hX : Integrable X) (c : Euc d) :
    Integrable (fun x => um_E c x * X x) volume := by
  refine hX.bdd_mul (c := 1) (um_E_continuous c).aestronglyMeasurable (Filter.Eventually.of_forall fun x => (um_E_norm c x).le)

theorem um_fourier_two {X : Euc d → ℂ} (hX : Integrable X) (k ξ : Euc d) (a b : ℂ) :
    𝓕 (fun x => a * (um_E k x * X x) + b * (um_E (-k) x * X x)) ξ =
      a * 𝓕 X (ξ - k) + b * 𝓕 X (ξ + k) := by
  have h1 := um_integrable_E hX k
  have h2 := um_integrable_E hX (-k)
  have hA : Integrable (fun x : Euc d => 𝐞 (-inner ℝ x ξ) • (a * (um_E k x * X x))) volume :=
    (Real.fourierIntegral_convergent_iff ξ).2 (h1.const_mul a)
  have hB : Integrable (fun x : Euc d => 𝐞 (-inner ℝ x ξ) • (b * (um_E (-k) x * X x))) volume :=
    (Real.fourierIntegral_convergent_iff ξ).2 (h2.const_mul b)
  have e : ∀ x : Euc d, 𝐞 (-inner ℝ x ξ) • (a * (um_E k x * X x) + b * (um_E (-k) x * X x)) =
      a * (𝐞 (-inner ℝ x ξ) • (um_E k x * X x)) + b * (𝐞 (-inner ℝ x ξ) • (um_E (-k) x * X x)) := by
    intro x; simp only [Circle.smul_def, smul_eq_mul]; ring
  have eA : ∀ x : Euc d, 𝐞 (-inner ℝ x ξ) • (a * (um_E k x * X x)) =
      a * (𝐞 (-inner ℝ x ξ) • (um_E k x * X x)) := by
    intro x; simp only [Circle.smul_def, smul_eq_mul]; ring
  have eB : ∀ x : Euc d, 𝐞 (-inner ℝ x ξ) • (b * (um_E (-k) x * X x)) =
      b * (𝐞 (-inner ℝ x ξ) • (um_E (-k) x * X x)) := by
    intro x; simp only [Circle.smul_def, smul_eq_mul]; ring
  simp only [eA] at hA
  simp only [eB] at hB
  rw [Real.fourier_eq]
  simp_rw [e]
  rw [integral_add hA hB, integral_const_mul, integral_const_mul]
  have f1 : ∫ x : Euc d, 𝐞 (-inner ℝ x ξ) • (um_E k x * X x) = 𝓕 X (ξ - k) := by
    rw [← um_fourier_E, Real.fourier_eq]
  have f2 : ∫ x : Euc d, 𝐞 (-inner ℝ x ξ) • (um_E (-k) x * X x) = 𝓕 X (ξ + k) := by
    rw [← sub_neg_eq_add, ← um_fourier_E, Real.fourier_eq]
  rw [f1, f2]

/-- `U = a E_k X + b E_{-k} X` for `U = χ cos(2π k·x + φ)` -/
theorem um_cos_eq (χ : Euc d → ℝ) (k : Euc d) (φ : ℝ) (x : Euc d) :
    (((χ x * Real.cos (2 * Real.pi * inner ℝ k x + φ) : ℝ)) : ℂ) =
      (Complex.exp ((φ : ℂ) * Complex.I) / 2) * (um_E k x * ((χ x : ℝ) : ℂ)) +
      (Complex.exp (-(φ : ℂ) * Complex.I) / 2) * (um_E (-k) x * ((χ x : ℝ) : ℂ)) := by
  unfold um_E
  rw [Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  rw [inner_neg_left]
  push_cast
  have e1 : Complex.exp ((2 * (Real.pi : ℂ) * (inner ℝ k x : ℝ) + φ) * Complex.I) =
      Complex.exp ((φ : ℂ) * Complex.I) * Complex.exp (2 * (Real.pi : ℂ) * (inner ℝ k x : ℝ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e2 : Complex.exp (-(2 * (Real.pi : ℂ) * (inner ℝ k x : ℝ) + φ) * Complex.I) =
      Complex.exp (-(φ : ℂ) * Complex.I) * Complex.exp (2 * (Real.pi : ℂ) * (-(inner ℝ k x : ℝ)) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [e1, e2]; ring

theorem um_peetre {s : ℝ} (hs : 0 ≤ s) (ξ η : Euc d) :
    wt ξ ^ s ≤ 2 ^ s * wt η ^ s * wt (ξ - η) ^ s := by
  calc wt ξ ^ s ≤ (2 * (wt (ξ - η) * wt η)) ^ s :=
        Real.rpow_le_rpow (wt_pos ξ).le (HRS.MS.SobMul.sobmul_wt_le ξ η) hs
    _ = _ := by
        rw [Real.mul_rpow (by norm_num) (mul_nonneg (wt_pos _).le (wt_pos _).le),
          Real.mul_rpow (wt_pos _).le (wt_pos _).le]
        ring

theorem um_mod_bound {χ : Euc d → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {s : ℝ} (hs : 0 ≤ s) (k : Euc d) (φ : ℝ) :
    HRS.Whole.sobolevNormE s (fun y => χ y * Real.cos (2 * Real.pi * inner ℝ k y + φ)) ^ 2 ≤
      ENNReal.ofReal (2 ^ s * wt k ^ s) * HRS.Whole.sobolevNormE s χ ^ 2 := by
  set u : Euc d → ℝ := fun y => χ y * Real.cos (2 * Real.pi * inner ℝ k y + φ) with hu
  have huc : Continuous u := by
    have := hχ.continuous
    simp only [hu]; fun_prop
  have huk : HasCompactSupport u := hc.mul_right
  have hu2 : MemLp u 2 volume := huc.memLp_of_hasCompactSupport huk
  have hu1 : Integrable u := huc.integrable_of_hasCompactSupport huk
  have hχ2 : MemLp χ 2 volume := hχ.continuous.memLp_of_hasCompactSupport hc
  have hχ1 : Integrable χ := hχ.continuous.integrable_of_hasCompactSupport hc
  set X : Euc d → ℂ := fun x => ((χ x : ℝ) : ℂ) with hXdef
  have hX1 : Integrable X := hχ1.ofReal
  set f : Euc d → ℝ≥0∞ := fun ξ => ENNReal.ofReal (wt ξ ^ s * ‖𝓕 X ξ‖ ^ 2) with hfdef
  have hXc : Continuous (𝓕 X) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).continuous₂ hX1
  have hfm : Measurable f := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact ((continuous_wt_rpow s).mul (hXc.norm.pow 2)).measurable
  have hI : ∫⁻ ξ, f ξ = HRS.Whole.sobolevNormE s χ ^ 2 := by
    rw [um_sobE_sq hχ2]
    refine lintegral_congr_ae ?_
    filter_upwards [um_L1L2 hχ1 hχ2] with ξ h
    simp only [hfdef, h]
    rfl
  rw [um_sobE_sq hu2]
  set a : ℂ := Complex.exp ((φ : ℂ) * Complex.I) / 2 with ha
  set b : ℂ := Complex.exp (-(φ : ℂ) * Complex.I) / 2 with hb
  have hna : ‖a‖ = 1 / 2 := by
    rw [ha, norm_div, Complex.norm_exp_ofReal_mul_I]; simp
  have hnb : ‖b‖ = 1 / 2 := by
    rw [hb, norm_div]
    have : -(φ : ℂ) * Complex.I = ((-φ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]; simp
  have hU : ∀ ξ, 𝓕 (fun x => ((u x : ℝ) : ℂ)) ξ = a * 𝓕 X (ξ - k) + b * 𝓕 X (ξ + k) := by
    intro ξ
    have : (fun x => ((u x : ℝ) : ℂ)) =
        fun x => a * (um_E k x * X x) + b * (um_E (-k) x * X x) := by
      ext x; exact um_cos_eq χ k φ x
    rw [this, um_fourier_two hX1]
  set K : ℝ := 2 ^ s * wt k ^ s with hK
  have hK0 : 0 ≤ K := by
    rw [hK]; exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (wt_pos k).le _)
  have pw : ∀ ξ : Euc d, ENNReal.ofReal (wt ξ ^ s * ‖𝓕 (fun x => ((u x : ℝ) : ℂ)) ξ‖ ^ 2) ≤
      ENNReal.ofReal (K / 2) * (f (ξ - k) + f (ξ + k)) := by
    intro ξ
    rw [hU ξ]
    simp only [hfdef]
    rw [← ENNReal.ofReal_add (mul_nonneg (Real.rpow_nonneg (wt_pos _).le _) (sq_nonneg _))
        (mul_nonneg (Real.rpow_nonneg (wt_pos _).le _) (sq_nonneg _)),
      ← ENNReal.ofReal_mul (by linarith [hK0])]
    apply ENNReal.ofReal_le_ofReal
    set α := 𝓕 X (ξ - k)
    set β := 𝓕 X (ξ + k)
    have h1 : ‖a * α + b * β‖ ≤ 1 / 2 * ‖α‖ + 1 / 2 * ‖β‖ := by
      calc ‖a * α + b * β‖ ≤ ‖a * α‖ + ‖b * β‖ := norm_add_le _ _
        _ = _ := by rw [norm_mul, norm_mul, hna, hnb]
    have h2 : ‖a * α + b * β‖ ^ 2 ≤ 1 / 2 * (‖α‖ ^ 2 + ‖β‖ ^ 2) := by
      have h0 := norm_nonneg (a * α + b * β)
      nlinarith [sq_nonneg (‖α‖ - ‖β‖), norm_nonneg α, norm_nonneg β,
        mul_self_le_mul_self h0 h1]
    have p1 := um_peetre hs ξ k
    have p2 : wt ξ ^ s ≤ 2 ^ s * wt k ^ s * wt (ξ + k) ^ s := by
      have := um_peetre hs ξ (-k)
      have hk : wt (-k) = wt k := by simp [wt]
      rwa [sub_neg_eq_add, hk] at this
    have hw0 := Real.rpow_nonneg (wt_pos ξ).le s
    calc wt ξ ^ s * ‖a * α + b * β‖ ^ 2 ≤ wt ξ ^ s * (1 / 2 * (‖α‖ ^ 2 + ‖β‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 hw0
      _ = 1 / 2 * (wt ξ ^ s * ‖α‖ ^ 2) + 1 / 2 * (wt ξ ^ s * ‖β‖ ^ 2) := by ring
      _ ≤ 1 / 2 * (K * wt (ξ - k) ^ s * ‖α‖ ^ 2) + 1 / 2 * (K * wt (ξ + k) ^ s * ‖β‖ ^ 2) := by
          gcongr
      _ = K / 2 * (wt (ξ - k) ^ s * ‖α‖ ^ 2 + wt (ξ + k) ^ s * ‖β‖ ^ 2) := by ring
  calc ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ s * ‖fourierL2 u ξ‖ ^ 2)
      = ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ s * ‖𝓕 (fun x => ((u x : ℝ) : ℂ)) ξ‖ ^ 2) := by
        refine lintegral_congr_ae ?_
        filter_upwards [um_L1L2 hu1 hu2] with ξ h
        rw [h]
    _ ≤ ∫⁻ ξ, ENNReal.ofReal (K / 2) * (f (ξ - k) + f (ξ + k)) := lintegral_mono pw
    _ = ENNReal.ofReal (K / 2) * ((∫⁻ ξ, f (ξ - k)) + ∫⁻ ξ, f (ξ + k)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_add_left (f := fun ξ => f (ξ - k)) (hfm.comp (measurable_id.sub_const k)) (fun ξ => f (ξ + k))
    _ = ENNReal.ofReal K * ∫⁻ ξ, f ξ := by
        rw [lintegral_sub_right_eq_self f k, lintegral_add_right_eq_self f k, ← two_mul,
          ← mul_assoc]
        congr 1
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring
    _ = _ := by rw [hI]

theorem um_chi_finite {χ : Euc d → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {s : ℝ} (hs : 0 ≤ s) : HRS.Whole.sobolevNormE s χ ≠ ⊤ := by
  have hχ2 : MemLp χ 2 volume := hχ.continuous.memLp_of_hasCompactSupport hc
  have hχ1 : Integrable χ := hχ.continuous.integrable_of_hasCompactSupport hc
  set S := um_S χ hχ hc with hS
  set a : SchwartzMap (Euc d) ℂ := 𝓕 S with ha
  have hint0 : Integrable (fun x : Euc d => wt x ^ s * ‖a x‖) volume := by
    have := HRS.MS.SobMul.sobmul_integrable_weight (d := d) (s := 2 * s) (by positivity) a
    simpa [mul_div_cancel_left₀] using this
  set B : ℝ := SchwartzMap.seminorm ℝ 0 0 a with hB
  have hint : Integrable (fun ξ : Euc d => wt ξ ^ s * ‖a ξ‖ ^ 2) volume := by
    refine (hint0.const_mul B).mono' ?_ ?_
    · exact ((continuous_wt_rpow s).mul (a.continuous.norm.pow 2)).aestronglyMeasurable
    · filter_upwards with ξ
      have h0 : 0 ≤ wt ξ ^ s * ‖a ξ‖ ^ 2 := mul_nonneg (Real.rpow_nonneg (wt_pos ξ).le _) (sq_nonneg _)
      rw [Real.norm_of_nonneg h0]
      have := SchwartzMap.norm_le_seminorm ℝ a ξ
      have hw := Real.rpow_nonneg (wt_pos ξ).le s
      calc wt ξ ^ s * ‖a ξ‖ ^ 2 = (wt ξ ^ s * ‖a ξ‖) * ‖a ξ‖ := by ring
        _ ≤ (wt ξ ^ s * ‖a ξ‖) * B := by gcongr
        _ = B * (wt ξ ^ s * ‖a ξ‖) := by ring
  have hlt : HRS.Whole.sobolevNormE s χ ^ 2 < ⊤ := by
    rw [um_sobE_sq hχ2]
    have e : ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ s * ‖fourierL2 χ ξ‖ ^ 2) =
        ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ s * ‖a ξ‖ ^ 2) := by
      refine lintegral_congr_ae ?_
      filter_upwards [um_L1L2 hχ1 hχ2] with ξ h
      rw [h, ha, SchwartzMap.fourier_coe]
      rfl
    rw [e, ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun ξ =>
      mul_nonneg (Real.rpow_nonneg (wt_pos ξ).le _) (sq_nonneg _))]
    exact ENNReal.ofReal_lt_top
  intro h
  rw [h] at hlt
  simp at hlt

theorem um_mod_bound' {χ : Euc d → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {s : ℝ} (hs : 0 ≤ s) (k : Euc d) (φ : ℝ) :
    HRS.Whole.sobolevNormE s (fun y => χ y * Real.cos (2 * Real.pi * inner ℝ k y + φ)) ≤
      ENNReal.ofReal (Real.sqrt (2 ^ s * wt k ^ s)) * HRS.Whole.sobolevNormE s χ := by
  have h := um_mod_bound hχ hc hs k φ
  have hK0 : 0 ≤ 2 ^ s * wt k ^ s :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (wt_pos k).le _)
  have e : ENNReal.ofReal (2 ^ s * wt k ^ s) * HRS.Whole.sobolevNormE s χ ^ 2 =
      (ENNReal.ofReal (Real.sqrt (2 ^ s * wt k ^ s)) * HRS.Whole.sobolevNormE s χ) ^ 2 := by
    rw [mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hK0]
  by_contra hlt
  rw [not_le] at hlt
  rw [e] at h
  exact absurd h (not_le.2 ((ENNReal.pow_lt_pow_left_iff two_ne_zero).2 hlt))

theorem um_sqrt_le (m : ℕ) (k : Euc d) :
    Real.sqrt (2 ^ (m : ℝ) * wt k ^ (m : ℝ)) ≤
      (Real.sqrt 2 * (1 + 2 * Real.pi)) ^ m * (1 + ‖k‖) ^ m := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  rw [Real.rpow_natCast, Real.rpow_natCast, ← mul_pow (2 : ℝ) (wt k) m, ← mul_pow, ← pow_mul,
    mul_comm m 2, pow_mul]
  refine pow_le_pow_left₀ (by have := wt_pos k; positivity) ?_ m
  have hk := norm_nonneg k
  have h1 : (Real.sqrt 2 * (1 + 2 * Real.pi) * (1 + ‖k‖)) ^ 2 =
      2 * ((1 + 2 * Real.pi) * (1 + ‖k‖)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]; ring
  rw [h1]
  unfold wt
  nlinarith [Real.pi_pos, mul_nonneg hk Real.pi_pos.le, mul_nonneg (mul_nonneg hk hk) Real.pi_pos.le]

end HRS.MS.UlocMW
