import HRS.MS.IidInitAux2
import HRS.MS.SuppU5Aux8
import HRS.Prob.Metrics

/-!
# SA27, part 3: Wasserstein closeness and the `L²` coupling bound in `H^{-q}`

* `sa27_lip_le_w1`, `sa27_tendsto_of_w1`: `W₁(μ_n, ν) → 0` implies weak convergence.
* `sa27_cb1_of_partial`: `C_b^1` membership and norm from the bounds on the partial derivatives.
* `sa27_coupling`: for two `H^{-q}`-valued representatives `Y_i` of `φ ↦ a_i η(ψ_i φ)` of the same bridge `η`,
  `E‖Y₁ - Y₂‖² ≤ B²` as soon as `|a₁ψ₁φ(x) - a₂ψ₂φ(x)| ≤ B‖φ‖_{H^q}` for all `x`
  (Parseval over a smooth orthonormal system, the Riesz representative of `φ ↦ a₁ψ₁φ(x) - a₂ψ₂φ(x)`, and the
  variance of the bridge, `u5_bridge_sq`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

noncomputable section

namespace HRS.MS.IidInit

open HRS HRS.Whole HRS.MP.HNegInfra HRS.MP.RdProp HRS.U5

variable {d : ℕ}

/-! ### Wasserstein closeness and weak convergence -/

section W1

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]

/-- Lipschitz tests and `W₁`. -/
theorem sa27_lip_le_w1 (P Q : Measure B) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : B → ℝ) (Lc : ℝ≥0) (hL : Lc ≠ 0) (hf : LipschitzWith Lc f) (C : ℝ) (hb : ∀ x, |f x| ≤ C) :
    ENNReal.ofReal |∫ z, f z ∂P - ∫ z, f z ∂Q| ≤ (Lc : ℝ≥0∞) * wassersteinE 1 P Q := by
  unfold wassersteinE
  rw [ENNReal.mul_iInf_of_ne (by simpa using hL) ENNReal.coe_ne_top]
  refine le_iInf fun π => ?_
  have := π.2.isProbabilityMeasure
  simp only [Real.rpow_one, div_one, ENNReal.rpow_one]
  have hc : Continuous f := hf.continuous
  have hm1 : Measurable fun z : B × B => f z.1 := hc.measurable.comp measurable_fst
  have hm2 : Measurable fun z : B × B => f z.2 := hc.measurable.comp measurable_snd
  have hi : ∀ g : B × B → ℝ, Measurable g → (∀ z, |g z| ≤ C) → Integrable g π.1 := fun g hg hbd =>
    Integrable.of_bound hg.aestronglyMeasurable C (ae_of_all _ fun z => by simpa using hbd z)
  have hi1 := hi _ hm1 fun z => hb _
  have hi2 := hi _ hm2 fun z => hb _
  have e1 : ∫ z, f z ∂P = ∫ z, f z.1 ∂π.1 := by
    have := integral_map (μ := π.1) (φ := Prod.fst) (f := f) measurable_fst.aemeasurable
      (by rw [π.2.1]; exact hc.aestronglyMeasurable)
    rwa [π.2.1] at this
  have e2 : ∫ z, f z ∂Q = ∫ z, f z.2 ∂π.1 := by
    have := integral_map (μ := π.1) (φ := Prod.snd) (f := f) measurable_snd.aemeasurable
      (by rw [π.2.2]; exact hc.aestronglyMeasurable)
    rwa [π.2.2] at this
  rw [e1, e2, ← integral_sub hi1 hi2, ← Real.norm_eq_abs]
  calc ENNReal.ofReal ‖∫ z, (f z.1 - f z.2) ∂π.1‖
      ≤ ENNReal.ofReal (∫ z, ‖f z.1 - f z.2‖ ∂π.1) :=
        ENNReal.ofReal_le_ofReal (norm_integral_le_integral_norm _)
    _ = ∫⁻ z, ‖f z.1 - f z.2‖ₑ ∂π.1 := ofReal_integral_norm_eq_lintegral_enorm (hi1.sub hi2)
    _ ≤ ∫⁻ z, (Lc : ℝ≥0∞) * ENNReal.ofReal ‖z.1 - z.2‖ ∂π.1 := by
        refine lintegral_mono fun z => ?_
        have := hf.edist_le_mul (z.1) (z.2)
        rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm] at this
        rw [← ofReal_norm]
        simpa [ENNReal.ofReal_mul, ← ENNReal.ofReal_coe_nnreal] using this
    _ = (Lc : ℝ≥0∞) * ∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ∂π.1 :=
        lintegral_const_mul' _ _ ENNReal.coe_ne_top

/-- `W₁(μ_n, ν) → 0` implies weak convergence. -/
theorem sa27_tendsto_of_w1 (μ : ℕ → Measure B) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : Measure B) [IsProbabilityMeasure ν]
    (h : Tendsto (fun n => wassersteinE 1 (μ n) ν) atTop (𝓝 0)) :
    ∀ F : B →ᵇ ℝ, Tendsto (fun n => ∫ x, F x ∂(μ n)) atTop (𝓝 (∫ x, F x ∂ν)) := by
  let m : ℕ → ProbabilityMeasure B := fun n => ⟨μ n, inferInstance⟩
  let m' : ProbabilityMeasure B := ⟨ν, inferInstance⟩
  have hT : Tendsto m atTop (𝓝 m') := by
    rw [tendsto_iff_forall_lipschitz_integral_tendsto]
    rintro f ⟨C, hC⟩ ⟨Lc, hLc⟩
    have hL1 : (max Lc 1) ≠ 0 := by positivity
    have hLf : LipschitzWith (max Lc 1) f := hLc.weaken (le_max_left _ _)
    have hbd : ∀ x, |f x| ≤ |f 0| + C := fun x => by
      have := hC x 0
      rw [Real.dist_eq] at this
      calc |f x| = |f 0 + (f x - f 0)| := by ring_nf
        _ ≤ |f 0| + |f x - f 0| := abs_add_le _ _
        _ ≤ |f 0| + C := by linarith
    rw [tendsto_iff_dist_tendsto_zero]
    have key : ∀ n, ENNReal.ofReal |∫ z, f z ∂(μ n) - ∫ z, f z ∂ν| ≤
        ((max Lc 1 : ℝ≥0) : ℝ≥0∞) * wassersteinE 1 (μ n) ν := fun n =>
      sa27_lip_le_w1 (μ n) ν f (max Lc 1) hL1 hLf (|f 0| + C) hbd
    have h2 : Tendsto (fun n => ((max Lc 1 : ℝ≥0) : ℝ≥0∞) * wassersteinE 1 (μ n) ν) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (a := ((max Lc 1 : ℝ≥0) : ℝ≥0∞)) h (Or.inr ENNReal.coe_ne_top)
      simpa using this
    have h3 : Tendsto (fun n => ENNReal.ofReal |∫ z, f z ∂(μ n) - ∫ z, f z ∂ν|) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun _ => zero_le) key
    have h4 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h3
    simp only [Function.comp_def, ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_zero] at h4
    refine h4.congr fun n => ?_
    simp [m, m', Real.dist_eq, ProbabilityMeasure.coe_mk]
  intro F
  have := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hT) F
  simpa [m, m'] using this

end W1

/-! ### `C_b^1` from partial derivatives -/

theorem sa27_cb1_of_partial {f : Euc d → ℝ} {B : ℝ} (hf : ContDiff ℝ 1 f)
    (h0 : ∀ x, |f x| ≤ B) (h1 : ∀ (i : Fin 1 → Fin d) (x : Euc d), |partialDeriv i f x| ≤ B) :
    MemCb 1 f ∧ cbNorm 1 f ≤ (1 + d) * B := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (h0 0)
  have hder : ∀ x, ‖fderiv ℝ f x‖ ≤ d * B := fun x => by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have hv : v = ∑ k : Fin d, v k • (EuclideanSpace.single k (1 : ℝ)) := by
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v]
      simp [EuclideanSpace.basisFun_apply]
    have hk : ∀ k : Fin d, |fderiv ℝ f x (EuclideanSpace.single k (1 : ℝ))| ≤ B := fun k => by
      have := h1 (fun _ => k) x
      simpa [partialDeriv] using this
    calc ‖fderiv ℝ f x v‖
        = ‖∑ k : Fin d, v k * fderiv ℝ f x (EuclideanSpace.single k (1 : ℝ))‖ := by
          conv_lhs => rw [hv]
          simp [map_sum]
      _ ≤ ∑ k : Fin d, ‖v k * fderiv ℝ f x (EuclideanSpace.single k (1 : ℝ))‖ := norm_sum_le _ _
      _ ≤ ∑ _k : Fin d, ‖v‖ * B := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_mul, Real.norm_eq_abs (fderiv ℝ f x _)]
          exact mul_le_mul (PiLp.norm_apply_le v k) (hk k) (abs_nonneg _) (norm_nonneg _)
      _ = d * B * ‖v‖ := by simp; ring
  have hb0 : BddAbove (Set.range fun z => ‖iteratedFDeriv ℝ 0 f z‖) :=
    ⟨B, by rintro _ ⟨z, rfl⟩; simpa [norm_iteratedFDeriv_zero] using h0 z⟩
  have hb1 : BddAbove (Set.range fun z => ‖iteratedFDeriv ℝ 1 f z‖) :=
    ⟨d * B, by rintro _ ⟨z, rfl⟩; simpa [norm_iteratedFDeriv_one] using hder z⟩
  refine ⟨⟨hf, fun j hj => ?_⟩, ?_⟩
  · interval_cases j
    · exact hb0
    · exact hb1
  · unfold cbNorm
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have e0 : ⨆ z : Euc d, ‖iteratedFDeriv ℝ 0 f z‖ ≤ B :=
      ciSup_le fun z => by simpa [norm_iteratedFDeriv_zero] using h0 z
    have e1 : ⨆ z : Euc d, ‖iteratedFDeriv ℝ 1 f z‖ ≤ d * B :=
      ciSup_le fun z => by simpa [norm_iteratedFDeriv_one] using hder z
    linarith

/-! ### The `L²` coupling bound -/

theorem sa27_var_le (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (g : Euc d → ℝ)
    (hg : Continuous g) {C : ℝ} (hb : ∀ x, |g x| ≤ C) :
    ∫ x, (g x - ∫ y, g y ∂μ) ^ 2 ∂μ ≤ ∫ x, g x ^ 2 ∂μ := by
  set c : ℝ := ∫ y, g y ∂μ with hc
  have hi : Integrable g μ :=
    Integrable.of_bound hg.measurable.aestronglyMeasurable C (ae_of_all _ fun x => by simpa using hb x)
  have hi2 : Integrable (fun x => g x ^ 2) μ :=
    Integrable.of_bound (hg.measurable.pow_const 2).aestronglyMeasurable (C ^ 2)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hb x) 2)
  have hi3 : Integrable (fun x => 2 * c * g x - c ^ 2) μ := (hi.const_mul _).sub (integrable_const _)
  have e : ∀ x, (g x - c) ^ 2 = g x ^ 2 - (2 * c * g x - c ^ 2) := fun x => by ring
  simp_rw [e]
  rw [integral_sub hi2 hi3, integral_sub (hi.const_mul _) (integrable_const _), integral_const_mul,
    ← hc]
  simp
  nlinarith [sq_nonneg c]

/-- One bridge difference: `E(a₁η(ψ₁) - a₂η(ψ₂))² ≤ ∫(a₁ψ₁ - a₂ψ₂)² dμ`. -/
theorem sa27_bridge_term (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (a₁ a₂ : ℝ)
    (ψ₁ ψ₂ : Euc d → ℝ) (hψ₁ : MemCb 1 ψ₁) (hψ₂ : MemCb 1 ψ₂)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η : Ω' → (Euc d → ℝ) → ℝ)
    (hηm : ∀ ψ : Euc d → ℝ, MemCb 1 ψ → Measurable fun ζ => η ζ ψ)
    (hη : ∀ (p : ℕ) (ψ : Fin p → Euc d → ℝ), (∀ a, MemCb 1 (ψ a)) →
      P'.map (fun ζ => (WithLp.toLp 2 fun a => η ζ (ψ a) : EuclideanSpace ℝ (Fin p))) =
        multivariateGaussian 0 (Matrix.of fun a b => iidCovW μ (ψ a) (ψ b))) :
    ∫⁻ ζ, ENNReal.ofReal ((a₁ * η ζ ψ₁ - a₂ * η ζ ψ₂) ^ 2) ∂P' ≤
      ∫⁻ x, ENNReal.ofReal ((a₁ * ψ₁ x - a₂ * ψ₂ x) ^ 2) ∂μ := by
  set g : Euc d → ℝ := fun x => a₁ * ψ₁ x - a₂ * ψ₂ x with hg
  have hgc : Continuous g :=
    (continuous_const.mul hψ₁.1.continuous).sub (continuous_const.mul hψ₂.1.continuous)
  have hψm : ∀ j : Fin 2, MemCb 1 ((![ψ₁, ψ₂] : Fin 2 → Euc d → ℝ) j) := by
    intro j
    fin_cases j
    · exact hψ₁
    · exact hψ₂
  have key := u5_bridge_sq P' μ η hηm hη (q := 2) ![ψ₁, ψ₂] hψm ![a₁, -a₂]
  have e1 : ∀ ζ, (∑ j : Fin 2, (![a₁, -a₂] : Fin 2 → ℝ) j * η ζ ((![ψ₁, ψ₂] :
      Fin 2 → Euc d → ℝ) j)) = a₁ * η ζ ψ₁ - a₂ * η ζ ψ₂ := fun ζ => by
    simp [Fin.sum_univ_two]; ring
  simp_rw [e1] at key
  rw [key]
  have hbd : ∀ x, |g x| ≤ cbNorm 1 ψ₁ * |a₁| + cbNorm 1 ψ₂ * |a₂| := fun x => by
    calc |g x| ≤ |a₁ * ψ₁ x| + |a₂ * ψ₂ x| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_mul, abs_mul]
        have h1 := u5_cb_sup hψ₁ x
        have h2 := u5_cb_sup hψ₂ x
        nlinarith [abs_nonneg a₁, abs_nonneg a₂, abs_nonneg (ψ₁ x), abs_nonneg (ψ₂ x)]
  have hi : Integrable (fun x => g x ^ 2) μ :=
    Integrable.of_bound (hgc.measurable.pow_const 2).aestronglyMeasurable
      ((cbNorm 1 ψ₁ * |a₁| + cbNorm 1 ψ₂ * |a₂|) ^ 2)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hbd x) 2)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => sq_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hc : ∫ y, g y ∂μ = a₁ * HRS.Whole.pair μ ψ₁ - a₂ * HRS.Whole.pair μ ψ₂ := by
    unfold HRS.Whole.pair
    simp only [hg]
    rw [integral_sub ((u5_cb_integrable hψ₁ μ).const_mul _)
      ((u5_cb_integrable hψ₂ μ).const_mul _), integral_const_mul, integral_const_mul]
  have e2 : ∀ x, (∑ j : Fin 2, (![a₁, -a₂] : Fin 2 → ℝ) j * ((![ψ₁, ψ₂] :
      Fin 2 → Euc d → ℝ) j x - HRS.Whole.pair μ ((![ψ₁, ψ₂] :
      Fin 2 → Euc d → ℝ) j))) = g x - ∫ y, g y ∂μ := fun x => by
    rw [hc]; simp [Fin.sum_univ_two, hg]; ring
  simp_rw [e2]
  exact sa27_var_le μ g hgc hbd

theorem sa27_coupling {Γ : ℝ} (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (a₁ a₂ B : ℝ)
    (hB0 : 0 ≤ B) (ψ₁ ψ₂ : (Euc d → ℝ) → (Euc d → ℝ))
    (hm₁ : ∀ φ, IsSobolevTest Γ φ → MemCb 1 (ψ₁ φ))
    (hm₂ : ∀ φ, IsSobolevTest Γ φ → MemCb 1 (ψ₂ φ))
    (hl₁ : ∀ (φ φ₂ : Euc d → ℝ) (c : ℝ), IsSobolevTest Γ φ → IsSobolevTest Γ φ₂ →
      ψ₁ (φ + c • φ₂) = ψ₁ φ + c • ψ₁ φ₂)
    (hl₂ : ∀ (φ φ₂ : Euc d → ℝ) (c : ℝ), IsSobolevTest Γ φ → IsSobolevTest Γ φ₂ →
      ψ₂ (φ + c • φ₂) = ψ₂ φ + c • ψ₂ φ₂)
    (hB : ∀ φ, IsSobolevTest Γ φ → ∀ x, |a₁ * ψ₁ φ x - a₂ * ψ₂ φ x| ≤ B * HRS.Whole.sobolevNorm Γ φ)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η : Ω' → (Euc d → ℝ) → ℝ)
    (hηm : ∀ ψ : Euc d → ℝ, MemCb 1 ψ → Measurable fun ζ => η ζ ψ)
    (hη : ∀ (p : ℕ) (ψ : Fin p → Euc d → ℝ), (∀ a, MemCb 1 (ψ a)) →
      P'.map (fun ζ => (WithLp.toLp 2 fun a => η ζ (ψ a) : EuclideanSpace ℝ (Fin p))) =
        multivariateGaussian 0 (Matrix.of fun a b => iidCovW μ (ψ a) (ψ b)))
    (Y₁ Y₂ : Ω' → HNeg d Γ)
    (hY₁ : ∀ φ, IsSobolevTest Γ φ → ∀ᵐ ζ ∂P', HNeg.pairing φ (Y₁ ζ) = a₁ * η ζ (ψ₁ φ))
    (hY₂ : ∀ φ, IsSobolevTest Γ φ → ∀ᵐ ζ ∂P', HNeg.pairing φ (Y₂ ζ) = a₂ * η ζ (ψ₂ φ)) :
    ∫⁻ ζ, ‖Y₁ ζ - Y₂ ζ‖ₑ ^ 2 ∂P' ≤ ENNReal.ofReal (B ^ 2) := by
  obtain ⟨e, he, hpars⟩ := hneg_parseval d Γ
  set g : ℕ → Euc d → ℝ := fun ℓ x => a₁ * ψ₁ (e ℓ) x - a₂ * ψ₂ (e ℓ) x with hg
  -- the Riesz representative of `φ ↦ a₁ ψ₁ φ x - a₂ ψ₂ φ x`
  have hriesz : ∀ x : Euc d, ∃ k : HNeg d Γ, ‖k‖ ≤ B ∧
      ∀ φ, IsSobolevTest Γ φ → HNeg.pairing φ k = a₁ * ψ₁ φ x - a₂ * ψ₂ φ x := by
    intro x
    obtain ⟨k, hk⟩ := rpk_exists_rep (Γ := Γ) (fun φ => a₁ * ψ₁ φ x - a₂ * ψ₂ φ x) B
      (fun φ φ' c hφ hφ' => by
        have h1 := hl₁ φ' φ c hφ' hφ
        have h2 := hl₂ φ' φ c hφ' hφ
        show a₁ * ψ₁ (c • φ + φ') x - a₂ * ψ₂ (c • φ + φ') x =
          c * (a₁ * ψ₁ φ x - a₂ * ψ₂ φ x) + (a₁ * ψ₁ φ' x - a₂ * ψ₂ φ' x)
        rw [add_comm (c • φ) φ', h1, h2]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring)
      (fun φ hφ => hB φ hφ x)
    refine ⟨k, hneg_norm_le_of_pairing k B hB0 fun φ hφ => ?_, hk⟩
    rw [hk φ hφ]
    exact hB φ hφ x
  have hgc : ∀ ℓ, Continuous (g ℓ) := fun ℓ =>
    ((continuous_const.mul (hm₁ _ (he ℓ)).1.continuous).sub
      (continuous_const.mul (hm₂ _ (he ℓ)).1.continuous))
  have hsum : ∀ x : Euc d, ∑' ℓ, ENNReal.ofReal (g ℓ x ^ 2) ≤ ENNReal.ofReal (B ^ 2) := by
    intro x
    obtain ⟨k, hkB, hk⟩ := hriesz x
    have hs := hpars k
    have hp : ∀ ℓ, HNeg.pairing (e ℓ) k = g ℓ x := fun ℓ => hk _ (he ℓ)
    simp_rw [hp] at hs
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs.summable, hs.tsum_eq]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hkB 2)
  have hae : ∀ᵐ ζ ∂P', ∀ ℓ, HNeg.pairing (e ℓ) (Y₁ ζ) = a₁ * η ζ (ψ₁ (e ℓ)) ∧
      HNeg.pairing (e ℓ) (Y₂ ζ) = a₂ * η ζ (ψ₂ (e ℓ)) :=
    ae_all_iff.2 fun ℓ => (hY₁ _ (he ℓ)).and (hY₂ _ (he ℓ))
  have hnorm : ∀ᵐ ζ ∂P', ‖Y₁ ζ - Y₂ ζ‖ₑ ^ 2 =
      ∑' ℓ, ENNReal.ofReal ((a₁ * η ζ (ψ₁ (e ℓ)) - a₂ * η ζ (ψ₂ (e ℓ))) ^ 2) := by
    filter_upwards [hae] with ζ hζ
    have hs := hpars (Y₁ ζ - Y₂ ζ)
    have hp : ∀ ℓ, HNeg.pairing (e ℓ) (Y₁ ζ - Y₂ ζ) =
        a₁ * η ζ (ψ₁ (e ℓ)) - a₂ * η ζ (ψ₂ (e ℓ)) := fun ℓ => by
      rw [mhn_pairing_sub (he ℓ), (hζ ℓ).1, (hζ ℓ).2]
    simp_rw [hp] at hs
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← hs.tsum_eq,
      ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs.summable]
  have hterm : ∀ ℓ, ∫⁻ ζ, ENNReal.ofReal ((a₁ * η ζ (ψ₁ (e ℓ)) - a₂ * η ζ (ψ₂ (e ℓ))) ^ 2) ∂P' ≤
      ∫⁻ x, ENNReal.ofReal (g ℓ x ^ 2) ∂μ := fun ℓ =>
    sa27_bridge_term μ a₁ a₂ _ _ (hm₁ _ (he ℓ)) (hm₂ _ (he ℓ)) P' η hηm hη
  calc ∫⁻ ζ, ‖Y₁ ζ - Y₂ ζ‖ₑ ^ 2 ∂P'
      = ∫⁻ ζ, ∑' ℓ, ENNReal.ofReal ((a₁ * η ζ (ψ₁ (e ℓ)) - a₂ * η ζ (ψ₂ (e ℓ))) ^ 2) ∂P' :=
        lintegral_congr_ae hnorm
    _ = ∑' ℓ, ∫⁻ ζ, ENNReal.ofReal ((a₁ * η ζ (ψ₁ (e ℓ)) - a₂ * η ζ (ψ₂ (e ℓ))) ^ 2) ∂P' :=
        lintegral_tsum fun ℓ =>
          ((((hηm _ (hm₁ _ (he ℓ))).const_mul a₁).sub ((hηm _ (hm₂ _ (he ℓ))).const_mul a₂)).pow_const 2
            |>.ennreal_ofReal).aemeasurable
    _ ≤ ∑' ℓ, ∫⁻ x, ENNReal.ofReal (g ℓ x ^ 2) ∂μ := ENNReal.tsum_le_tsum hterm
    _ = ∫⁻ x, ∑' ℓ, ENNReal.ofReal (g ℓ x ^ 2) ∂μ :=
        (lintegral_tsum fun ℓ => (((hgc ℓ).measurable.pow_const 2).ennreal_ofReal).aemeasurable).symm
    _ ≤ ∫⁻ _x, ENNReal.ofReal (B ^ 2) ∂μ := lintegral_mono hsum
    _ = ENNReal.ofReal (B ^ 2) := by simp

end HRS.MS.IidInit
