import HRS.MS.SobMulAux2

/-!
# MS-SOBMUL: `H^s` multiplier by translates of smooth compactly supported functions

For `s ≥ 0` and `θ ∈ C_c^∞(ℝ^d)` there is a constant `C` such that
`‖θ(· - z) u‖_{H^s} ≤ C ‖u‖_{H^s}` for all translations `z` and all `u`.
The proof: `\widehat{θ u} = \hatθ ⋆ û` (density from Schwartz functions), Peetre's inequality
`⟨ξ⟩^s ≤ 2^{s/2}⟨ξ-η⟩^s⟨η⟩^s` and a Young-type inequality `‖A ⋆ B‖₂ ≤ ‖A‖₁ ‖B‖₂`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform Convolution ContDiff

namespace HRS.MS.SobMul
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

/-! ### The complexified cutoff as a Schwartz function -/

/-- `θ ∈ C_c^∞` as a complex Schwartz function -/
def sobmul_T (θ : Euc d → ℝ) (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ) :
    SchwartzMap (Euc d) ℂ :=
  (hc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hθ)

theorem sobmul_T_apply (θ : Euc d → ℝ) (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (x : Euc d) : sobmul_T θ hθ hc x = ((θ x : ℝ) : ℂ) := rfl

/-! ### Fourier transform of a product -/

theorem sobmul_memLp_mul {T : SchwartzMap (Euc d) ℂ} {θ : Euc d → ℝ} (hθc : Continuous θ)
    (hT : ∀ x, T x = ((θ x : ℝ) : ℂ)) {u : Euc d → ℝ} (hu : MemLp u 2 volume) :
    MemLp (fun x => θ x * u x) 2 volume := by
  refine hu.of_le_mul (c := SchwartzMap.seminorm ℝ 0 0 T)
    (hθc.aestronglyMeasurable.mul hu.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have := SchwartzMap.norm_le_seminorm ℝ T x
  rw [hT x] at this
  simpa using this

theorem sobmul_fourierL2_mul {T : SchwartzMap (Euc d) ℂ} {θ : Euc d → ℝ} (hθc : Continuous θ)
    (hT : ∀ x, T x = ((θ x : ℝ) : ℂ)) {u : Euc d → ℝ} (hu : MemLp u 2 volume) :
    fourierL2 (fun x => θ x * u x) =ᵐ[volume]
      fun ξ => ∫ η, (𝓕 T : SchwartzMap (Euc d) ℂ) (ξ - η) * fourierL2 u η := by
  have hp := sobmul_memLp_mul hθc hT hu
  have h1 : ofRealLp hp = sobmul_mulLp T (ofRealLp hu) := by
    apply Lp.ext
    filter_upwards [ofRealLp_coe hp, sobmul_mulLp_coe T (ofRealLp hu), ofRealLp_coe hu] with x a b c
    rw [a, b, c, hT x]; simp
  have h2 := sobmul_fourier_mulLp T (ofRealLp hu)
  rw [fourierL2_eq hp, h1]
  refine h2.trans (Filter.Eventually.of_forall fun ξ => ?_)
  unfold sobmul_conv
  rw [fourierL2_eq hu]

/-! ### The weighted estimate -/

theorem sobmul_sq_eq (s : ℝ) (ξ : Euc d) (F : ℂ) :
    (ENNReal.ofReal (wt ξ ^ (s / 2)) * ‖F‖ₑ) ^ 2 = ENNReal.ofReal (wt ξ ^ s * ‖F‖ ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (by have := wt_pos (d := d) ξ; positivity),
    ← ENNReal.ofReal_pow (by have := wt_pos (d := d) ξ; positivity), mul_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul (wt_pos ξ).le]
  norm_num

theorem sobmul_stepB {s : ℝ} (hs : 0 ≤ s) {a b : Euc d → ℂ} (ha : Continuous a)
    (hb : AEStronglyMeasurable b volume) :
    ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ s * ‖∫ η, a (ξ - η) * b η‖ ^ 2) ≤
      ENNReal.ofReal (2 ^ (s / 2)) ^ 2 *
        ((∫⁻ x, ENNReal.ofReal (wt x ^ (s / 2)) * ‖a x‖ₑ) ^ 2 *
          ∫⁻ η, ENNReal.ofReal (wt η ^ s * ‖b η‖ ^ 2)) := by
  set b' := hb.mk b with hb'
  have hbm : Measurable b' := hb.stronglyMeasurable_mk.measurable
  have hbb : b =ᵐ[volume] b' := hb.ae_eq_mk
  set A : Euc d → ℝ≥0∞ := fun x => ENNReal.ofReal (wt x ^ (s / 2)) * ‖a x‖ₑ with hAdef
  set B : Euc d → ℝ≥0∞ := fun η => ENNReal.ofReal (wt η ^ (s / 2)) * ‖b' η‖ₑ with hBdef
  have hwm : Measurable fun x : Euc d => ENNReal.ofReal (wt x ^ (s / 2)) :=
    ENNReal.measurable_ofReal.comp (continuous_wt_rpow (s / 2)).measurable
  have hA : Measurable A := hwm.mul ha.measurable.enorm
  have hB : Measurable B := hwm.mul hbm.enorm
  have pw : ∀ ξ : Euc d, ENNReal.ofReal (wt ξ ^ (s / 2)) * ‖∫ η, a (ξ - η) * b η‖ₑ ≤
      ENNReal.ofReal (2 ^ (s / 2)) * ∫⁻ η, A (ξ - η) * B η := by
    intro ξ
    have e1 : ‖∫ η, a (ξ - η) * b η‖ₑ ≤ ∫⁻ η, ‖a (ξ - η)‖ₑ * ‖b' η‖ₑ := by
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      refine lintegral_congr_ae ?_
      filter_upwards [hbb] with η hη
      rw [enorm_mul, hη]
    calc ENNReal.ofReal (wt ξ ^ (s / 2)) * ‖∫ η, a (ξ - η) * b η‖ₑ
        ≤ ENNReal.ofReal (wt ξ ^ (s / 2)) * ∫⁻ η, ‖a (ξ - η)‖ₑ * ‖b' η‖ₑ :=
          by gcongr
      _ = ∫⁻ η, ENNReal.ofReal (wt ξ ^ (s / 2)) * (‖a (ξ - η)‖ₑ * ‖b' η‖ₑ) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ η, ENNReal.ofReal (2 ^ (s / 2)) * (A (ξ - η) * B η) := by
          refine lintegral_mono fun η => ?_
          have hp := sobmul_wt_rpow_le hs ξ η
          have h1 : ENNReal.ofReal (wt ξ ^ (s / 2)) ≤ ENNReal.ofReal (2 ^ (s / 2)) *
              (ENNReal.ofReal (wt (ξ - η) ^ (s / 2)) * ENNReal.ofReal (wt η ^ (s / 2))) := by
            rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (wt_pos _).le _),
              ← ENNReal.ofReal_mul (by positivity)]
            exact ENNReal.ofReal_le_ofReal hp
          calc ENNReal.ofReal (wt ξ ^ (s / 2)) * (‖a (ξ - η)‖ₑ * ‖b' η‖ₑ)
              ≤ (ENNReal.ofReal (2 ^ (s / 2)) *
                (ENNReal.ofReal (wt (ξ - η) ^ (s / 2)) * ENNReal.ofReal (wt η ^ (s / 2)))) *
                (‖a (ξ - η)‖ₑ * ‖b' η‖ₑ) := by gcongr
            _ = _ := by simp only [hAdef, hBdef]; ring
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hY := sobmul_young hA hB
  have e2 : ∫⁻ η, B η ^ 2 = ∫⁻ η, ENNReal.ofReal (wt η ^ s * ‖b η‖ ^ 2) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hbb] with η hη
    simp only [hBdef]
    rw [sobmul_sq_eq, hη]
  calc ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ s * ‖∫ η, a (ξ - η) * b η‖ ^ 2)
      = ∫⁻ ξ, (ENNReal.ofReal (wt ξ ^ (s / 2)) * ‖∫ η, a (ξ - η) * b η‖ₑ) ^ 2 := by
        refine lintegral_congr fun ξ => ?_
        rw [sobmul_sq_eq]
    _ ≤ ∫⁻ ξ, (ENNReal.ofReal (2 ^ (s / 2)) * ∫⁻ η, A (ξ - η) * B η) ^ 2 :=
        lintegral_mono fun ξ => pow_le_pow_left' (pw ξ) 2
    _ = ENNReal.ofReal (2 ^ (s / 2)) ^ 2 * ∫⁻ ξ, (∫⁻ η, A (ξ - η) * B η) ^ 2 := by
        simp_rw [mul_pow]
        exact lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    _ ≤ _ := by
        rw [← e2]
        exact mul_le_mul_right hY _

theorem sobmul_integrable_weight {s : ℝ} (hs : 0 ≤ s) (a : SchwartzMap (Euc d) ℂ) :
    Integrable (fun x : Euc d => wt x ^ (s / 2) * ‖a x‖) volume := by
  set g : Euc d → ℝ := fun x => (1 + ‖x‖ ^ 2) ^ (s / 2) with hgdef
  have hg : g.HasTemperateGrowth :=
    Function.hasTemperateGrowth_one_add_norm_sq_rpow (Euc d) (s / 2)
  have hI := (SchwartzMap.smulLeftCLM (𝕜 := ℝ) ℂ g a).integrable (μ := volume)
  have hI' : Integrable (fun x : Euc d => g x * ‖a x‖) volume := by
    refine hI.norm.congr ?_
    filter_upwards with x
    rw [SchwartzMap.smulLeftCLM_apply_apply hg, norm_smul, Real.norm_of_nonneg
      (Real.rpow_nonneg (by positivity) _)]
  refine (hI'.const_mul ((1 + 4 * Real.pi ^ 2) ^ (s / 2))).mono' ?_ ?_
  · exact ((continuous_wt_rpow (s / 2)).aestronglyMeasurable).mul a.continuous.norm.aestronglyMeasurable
  · filter_upwards with x
    have h0 : 0 ≤ wt x ^ (s / 2) * ‖a x‖ := mul_nonneg (Real.rpow_nonneg (wt_pos x).le _) (norm_nonneg _)
    rw [Real.norm_of_nonneg h0]
    have h1 : wt x ≤ (1 + 4 * Real.pi ^ 2) * (1 + ‖x‖ ^ 2) := by
      unfold wt; nlinarith [sq_nonneg ‖x‖, sq_nonneg Real.pi, mul_nonneg (sq_nonneg ‖x‖) (sq_nonneg Real.pi)]
    have h2 : wt x ^ (s / 2) ≤ (1 + 4 * Real.pi ^ 2) ^ (s / 2) * g x := by
      calc wt x ^ (s / 2) ≤ ((1 + 4 * Real.pi ^ 2) * (1 + ‖x‖ ^ 2)) ^ (s / 2) :=
            Real.rpow_le_rpow (wt_pos x).le h1 (by positivity)
        _ = _ := Real.mul_rpow (by positivity) (by positivity)
    calc wt x ^ (s / 2) * ‖a x‖ ≤ ((1 + 4 * Real.pi ^ 2) ^ (s / 2) * g x) * ‖a x‖ := by gcongr
      _ = _ := by ring

theorem sobmul_bound {s : ℝ} (hs : 0 ≤ s) (θ : Euc d → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hc : HasCompactSupport θ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ u : Euc d → ℝ, HRS.PDE.ToolboxRd.MemSobolev s u →
      HRS.PDE.ToolboxRd.MemSobolev s (fun x => θ x * u x) ∧
        HRS.PDE.ToolboxRd.sobolevNormSq s (fun x => θ x * u x) ≤ K ^ 2 * HRS.PDE.ToolboxRd.sobolevNormSq s u := by
  set T := sobmul_T θ hθ hc with hTdef
  have hT : ∀ x, T x = ((θ x : ℝ) : ℂ) := fun x => rfl
  set a : SchwartzMap (Euc d) ℂ := 𝓕 T with hadef
  set Ir : ℝ := ∫ x, wt x ^ (s / 2) * ‖a x‖ with hIr
  have hIr0 : 0 ≤ Ir := integral_nonneg fun x =>
    mul_nonneg (Real.rpow_nonneg (wt_pos x).le _) (norm_nonneg _)
  have hIe : ∫⁻ x, ENNReal.ofReal (wt x ^ (s / 2)) * ‖a x‖ₑ = ENNReal.ofReal Ir := by
    rw [hIr, ofReal_integral_eq_lintegral_ofReal (sobmul_integrable_weight hs a)
      (Filter.Eventually.of_forall fun x =>
        mul_nonneg (Real.rpow_nonneg (wt_pos x).le _) (norm_nonneg _))]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (wt_pos x).le _), ofReal_norm]
  refine ⟨2 ^ (s / 2) * Ir, by positivity, fun u hu => ?_⟩
  have hp := sobmul_memLp_mul hθ.continuous hT hu.1
  have hbm := aestronglyMeasurable_fourierL2 hu.1
  have key := sobmul_stepB hs (a := a) (b := fourierL2 u) a.continuous hbm
  rw [hIe] at key
  have hSig : ∫⁻ η, ENNReal.ofReal (wt η ^ s * ‖fourierL2 u η‖ ^ 2) =
      ENNReal.ofReal (HRS.PDE.ToolboxRd.sobolevNormSq s u) := by
    have hu2 : Integrable (fun ξ : Euc d => wt ξ ^ s * ‖fourierL2 u ξ‖ ^ 2) volume := hu.2
    rw [sobolevNormSq_eq, ofReal_integral_eq_lintegral_ofReal hu2
      (Filter.Eventually.of_forall fun η => by have := wt_pos (d := d) η; positivity)]
  rw [hSig] at key
  have hSig0 : 0 ≤ HRS.PDE.ToolboxRd.sobolevNormSq s u := integral_nonneg fun η => by
    have := wt_pos (d := d) η; positivity
  have hF := sobmul_fourierL2_mul hθ.continuous hT hu.1
  have hL : ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ s * ‖fourierL2 (fun x => θ x * u x) ξ‖ ^ 2) ≤
      ENNReal.ofReal ((2 ^ (s / 2) * Ir) ^ 2 * HRS.PDE.ToolboxRd.sobolevNormSq s u) := by
    have e : ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ s * ‖fourierL2 (fun x => θ x * u x) ξ‖ ^ 2) =
        ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ s * ‖∫ η, a (ξ - η) * fourierL2 u η‖ ^ 2) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hF] with ξ hξ
      rw [hξ]
    rw [e]
    refine key.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow hIr0,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), mul_pow]
    congr 1
    ring
  have hint : Integrable (fun ξ => wt ξ ^ s * ‖fourierL2 (fun x => θ x * u x) ξ‖ ^ 2) volume := by
    refine ⟨aesm_wt_mul (aestronglyMeasurable_fourierL2 hp) s, ?_⟩
    unfold HasFiniteIntegral
    refine lt_of_le_of_lt ?_ (lt_of_le_of_lt hL ENNReal.ofReal_lt_top)
    refine le_of_eq (lintegral_congr fun ξ => ?_)
    rw [Real.enorm_eq_ofReal (by have := wt_pos (d := d) ξ; positivity)]
  refine ⟨⟨hp, hint⟩, ?_⟩
  rw [sobolevNormSq_eq]
  have h2 := hL
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun η => by have := wt_pos (d := d) η; positivity)] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

/-- the base case (no translation) -/
theorem sobmul_base {s : ℝ} (hs : 0 ≤ s) (θ : Euc d → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hc : HasCompactSupport θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Euc d → ℝ,
      HRS.Whole.sobolevNormE s (fun x => θ x * u x) ≤
        ENNReal.ofReal C * HRS.Whole.sobolevNormE s u := by
  obtain ⟨K, hK, h⟩ := sobmul_bound hs θ hθ hc
  refine ⟨K + 1, by positivity, fun u => ?_⟩
  by_cases hu : HRS.PDE.ToolboxRd.MemSobolev s u
  · obtain ⟨h1, h2⟩ := h u hu
    unfold HRS.Whole.sobolevNormE
    rw [if_pos hu, if_pos h1, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s fun x => θ x * u x)
        ≤ Real.sqrt (K ^ 2 * HRS.PDE.ToolboxRd.sobolevNormSq s u) := Real.sqrt_le_sqrt h2
      _ = K * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s u) := by
          rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK]
      _ ≤ (K + 1) * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s u) := by
          gcongr; linarith [Real.sqrt_nonneg (HRS.PDE.ToolboxRd.sobolevNormSq s u)]
  · unfold HRS.Whole.sobolevNormE
    rw [if_neg hu, ENNReal.mul_top (by simp; positivity)]
    exact le_top

theorem sobolevNormE_mul_translate_le (s : ℝ) (hs : 0 ≤ s) (θ : Euc d → ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : Euc d) (u : Euc d → ℝ),
      HRS.Whole.sobolevNormE s (fun x => θ (x - z) * u x) ≤
        ENNReal.ofReal C * HRS.Whole.sobolevNormE s u := by
  obtain ⟨C, hC, h⟩ := sobmul_base hs θ hθ hc
  refine ⟨C, hC, fun z u => ?_⟩
  have e : (fun x => θ (x - z) * u x) = fun x => (fun y => θ y * u (y + z)) (x - z) := by
    ext x; simp
  have h1 := sobolevNormE_translate s (fun y => θ y * u (y + z)) z
  rw [e]
  refine h1.le.trans ((h (fun y => u (y + z))).trans (le_of_eq ?_))
  congr 1
  have := sobolevNormE_translate s u (-z)
  simpa using this

end HRS.MS.SobMul
