import HRS.Whole.Bias

/-!
# U12: proof of the conditional `weighted_remainder` (packet N1 of `docs/SUPP_WAVE1.md`, S7.7)

The statement `HRS.MS.SuppN.weighted_remainder_of_sharp_bias` is copied verbatim from `HRS/MS/SuppNSpec.lean`
(which is not imported here).  Route: under `SharpBiasConclusion` the first marginal is `μ.withDensity φ`, and
`m_N - μ - δ_N b = μ.withDensityᵥ (δ_N e_N)` with `e_N = (φ-1)/δ_N - HRS.Whole.biasDensity`, `‖e_N‖_{L²(μ)} ≤ C N^{-θ}`.
Cauchy-Schwarz gives both bounds.  `‖HRS.Whole.biasDensity‖_{L²(μ)} ≤ |2Aβ^p| M`, because the response of `ρ` is the
response of `P_μ ρ` (`HRS.Whole.convolution_susceptibility`) and `‖P_μ ρ‖_{L²(μ)} ≤ M`.  The constant is
`|C| + 2 |2Aβ^p| M`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.SuppN

open HRS.Whole

variable {d : ℕ} {s : ℝ}

/-- The first marginal with a density `φ ≥ 0` is the signed measure `μ.withDensityᵥ φ`. -/
lemma u12_toSM_withDensity (μ : Measure (Euc d)) (φ : Euc d → ℝ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hφm : Measurable φ) (mN : Measure (Euc d)) [IsFiniteMeasure mN]
    (hmN : mN = μ.withDensity fun x => ENNReal.ofReal (φ x)) :
    mN.toSignedMeasure = μ.withDensityᵥ φ := by
  have hfin : ∫⁻ x, ENNReal.ofReal (φ x) ∂μ ≠ ⊤ := by
    have h : mN Set.univ = ∫⁻ x, ENNReal.ofReal (φ x) ∂μ := by
      rw [hmN, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← h]
    exact measure_ne_top mN _
  have hW := withDensityᵥ_toReal (μ := μ) (f := fun x => ENNReal.ofReal (φ x))
    hφm.ennreal_ofReal.aemeasurable hfin
  simp only [ENNReal.toReal_ofReal, hφ0] at hW
  subst hmN
  exact hW.symm

lemma u12_toSM_one (μ : Measure (Euc d)) [IsProbabilityMeasure μ] :
    μ.toSignedMeasure = μ.withDensityᵥ 1 := by
  have h1 : Integrable (1 : Euc d → ℝ) μ := integrable_const (1 : ℝ)
  ext s hs
  rw [withDensityᵥ_apply h1 hs, Measure.toSignedMeasure_apply_measurable hs]
  simp [setIntegral_const]

/-- Total variation of a vector measure with integrable density. -/
lemma u12_tv (μ : Measure (Euc d)) (g : Euc d → ℝ) (hg : Integrable g μ) :
    SignedMeasure.totalVariation (μ.withDensityᵥ g) =
      μ.withDensity fun x => ENNReal.ofReal |g x| := by
  rw [SignedMeasure.totalVariation_eq_variation, Measure.variation_withDensityᵥ hg]
  congr 1
  funext x
  rw [Real.enorm_eq_ofReal_abs]

lemma u12_sig (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (mN : Measure (Euc d)) [IsFiniteMeasure mN]
    (φ e B : Euc d → ℝ) (δ : ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφm : Measurable φ)
    (hmN : mN = μ.withDensity fun x => ENNReal.ofReal (φ x))
    (hφe : ∀ x, φ x = δ * e x + δ * B x + 1) (hφint : Integrable φ μ)
    (he : Integrable e μ) (hB : Integrable B μ) :
    mN.toSignedMeasure - μ.toSignedMeasure - δ • μ.withDensityᵥ B =
      μ.withDensityᵥ (fun x => δ * e x) := by
  have h1 : Integrable (1 : Euc d → ℝ) μ := integrable_const (1 : ℝ)
  have hφ1 : Integrable (φ - 1) μ := hφint.sub h1
  have hδB : Integrable (δ • B) μ := hB.smul δ
  have key : (fun x => δ * e x) = φ - 1 - δ • B := by
    funext x
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply]
    rw [hφe x]
    ring
  rw [u12_toSM_withDensity μ φ hφ0 hφm mN hmN, u12_toSM_one μ, key,
    withDensityᵥ_sub hφ1 hδB, withDensityᵥ_sub hφint h1, withDensityᵥ_smul]

lemma u12_tv_diff (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (mN : Measure (Euc d)) [IsFiniteMeasure mN]
    (φ : Euc d → ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφm : Measurable φ)
    (hmN : mN = μ.withDensity fun x => ENNReal.ofReal (φ x)) (hφint : Integrable φ μ) :
    SignedMeasure.totalVariation (mN.toSignedMeasure - μ.toSignedMeasure) =
      μ.withDensity fun x => ENNReal.ofReal |(φ - 1) x| := by
  have h1 : Integrable (1 : Euc d → ℝ) μ := integrable_const (1 : ℝ)
  have hf : Integrable (φ - 1) μ := hφint.sub h1
  rw [u12_toSM_withDensity μ φ hφ0 hφm mN hmN, u12_toSM_one μ, ← withDensityᵥ_sub hφint h1,
    u12_tv μ _ hf]

lemma u12_tv_weighted (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (mN : Measure (Euc d))
    [IsFiniteMeasure mN] (φ e B : Euc d → ℝ) (δ : ℝ) (hφ0 : ∀ x, 0 ≤ φ x) (hφm : Measurable φ)
    (hmN : mN = μ.withDensity fun x => ENNReal.ofReal (φ x))
    (hφe : ∀ x, φ x = δ * e x + δ * B x + 1) (hφint : Integrable φ μ)
    (he : Integrable e μ) (hB : Integrable B μ) :
    SignedMeasure.totalVariation (mN.toSignedMeasure - μ.toSignedMeasure - δ • μ.withDensityᵥ B) =
      μ.withDensity fun x => ENNReal.ofReal |δ * e x| := by
  rw [u12_sig μ mN φ e B δ hφ0 hφm hmN hφe hφint he hB, u12_tv μ _ (he.const_mul δ)]

/-- Measurability of `x ↦ ofReal |g x|` from a.e.-strong measurability. -/
lemma u12_aemeas (μ : Measure (Euc d)) {g : Euc d → ℝ} (hg : AEStronglyMeasurable g μ) :
    AEMeasurable (fun x => ENNReal.ofReal |g x|) μ := by
  have := hg.norm.aemeasurable.ennreal_ofReal
  simpa only [Real.norm_eq_abs] using this

lemma u12_l2_nonneg (μ : Measure (Euc d)) (f : Euc d → ℝ) : 0 ≤ HRS.Whole.l2Norm μ f :=
  Real.sqrt_nonneg _

lemma u12_l2Norm_smul (μ : Measure (Euc d)) (c : ℝ) (f : Euc d → ℝ) :
    HRS.Whole.l2Norm μ (fun x => c * f x) = |c| * HRS.Whole.l2Norm μ f := by
  unfold HRS.Whole.l2Norm
  have h : (fun x => (c * f x) ^ 2) = fun x => c ^ 2 * f x ^ 2 := by
    funext x
    ring
  rw [h, integral_const_mul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- Cauchy-Schwarz in `L²(μ)`, in the form `∫⁻ f |g| ≤ ‖f‖ ‖g‖`. -/
lemma u12_cs (μ : Measure (Euc d)) {f g : Euc d → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hfn : ∀ x, 0 ≤ f x) :
    ∫⁻ x, ENNReal.ofReal (f x * |g x|) ∂μ ≤ ENNReal.ofReal (HRS.Whole.l2Norm μ f * HRS.Whole.l2Norm μ g) := by
  have hga : MemLp (fun x => |g x|) 2 μ := by
    simpa [Real.norm_eq_abs] using hg.norm
  have hint : Integrable (fun x => f x * |g x|) μ := hf.integrable_mul hga
  have hnn : 0 ≤ᵐ[μ] fun x => f x * |g x| :=
    ae_of_all _ fun x => mul_nonneg (hfn x) (abs_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  apply ENNReal.ofReal_le_ofReal
  have hf' : MemLp f (ENNReal.ofReal 2) μ := by rwa [ENNReal.ofReal_ofNat]
  have hg' : MemLp (fun x => |g x|) (ENNReal.ofReal 2) μ := by rwa [ENNReal.ofReal_ofNat]
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (ae_of_all _ hfn) (ae_of_all _ fun x => abs_nonneg (g x)) hf' hg'
  unfold HRS.Whole.l2Norm
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  simpa only [Real.rpow_two, sq_abs] using hH

/-- Cauchy-Schwarz on a measurable set: `∫_E |g| ≤ μ(E)^{1/2} ‖g‖_{L²(μ)}`. -/
lemma u12_restrict (μ : Measure (Euc d)) [IsFiniteMeasure μ] {E : Set (Euc d)} (hE : MeasurableSet E)
    {g : Euc d → ℝ} (hg : MemLp g 2 μ) :
    ∫⁻ x in E, ENNReal.ofReal |g x| ∂μ ≤
      ENNReal.ofReal (Real.sqrt (μ E).toReal * HRS.Whole.l2Norm μ g) := by
  obtain ⟨w, hw_def⟩ : ∃ w : Euc d → ℝ, w = E.indicator fun _ => (1 : ℝ) := ⟨_, rfl⟩
  have hw : MemLp w 2 μ := by
    rw [hw_def]
    exact (memLp_const (1 : ℝ)).indicator hE
  have hwn : ∀ x, 0 ≤ w x := fun x => by
    by_cases h : x ∈ E <;> simp [hw_def, h]
  have hwl : HRS.Whole.l2Norm μ w = Real.sqrt (μ E).toReal := by
    unfold HRS.Whole.l2Norm
    congr 1
    have h2 : (fun x => w x ^ 2) = E.indicator fun _ => (1 : ℝ) := by
      funext x
      by_cases h : x ∈ E <;> simp [hw_def, h]
    rw [h2, integral_indicator_const _ hE]
    simp [measureReal_def]
  have hsplit : ∫⁻ x in E, ENNReal.ofReal |g x| ∂μ = ∫⁻ x, ENNReal.ofReal (w x * |g x|) ∂μ := by
    rw [← lintegral_indicator hE]
    congr 1
    funext x
    by_cases h : x ∈ E <;> simp [hw_def, h]
  rw [hsplit]
  refine (u12_cs μ hw hg hwn).trans ?_
  rw [hwl]

lemma u12_theta_nonneg (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) : 0 ≤ HRS.Whole.biasTheta d s := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  have hp : 0 ≤ HRS.Whole.biasP d s := div_nonneg (Nat.cast_nonneg d) hs0.le
  have hp2 : HRS.Whole.biasP d s ≤ 2 := by
    unfold HRS.Whole.biasP
    rw [div_le_iff₀ hs0]
    linarith
  unfold HRS.Whole.biasTheta
  exact le_min (div_nonneg (sq_nonneg _) hp)
    (le_min (div_nonneg (by linarith) (by norm_num)) (div_nonneg (by norm_num) (by linarith)))

/-- The response to `ρ` has `L²(μ)`-norm at most `M`. -/
lemma u12_R_l2 (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) (β M : ℝ) (hβ : 0 < β)
    (ρ : Euc d → ℝ) (hρ : HRS.Whole.IsProbDensity ρ) (hM : ∀ x, ρ x ≤ M)
    [IsProbabilityMeasure (HRS.Whole.withDensityReal ρ)] :
    HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ)
      (HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β ρ) ≤ M := by
  have hM0 : 0 ≤ M := le_trans (hρ.nonneg 0) (hM 0)
  have hρL : MemLp ρ 2 (HRS.Whole.withDensityReal ρ) :=
    MemLp.of_bound hρ.measurable.aestronglyMeasurable M (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hρ.nonneg x)]
      exact hM x)
  have hρint : Integrable ρ (HRS.Whole.withDensityReal ρ) := hρL.integrable one_le_two
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ∫ x, ρ x ∂(HRS.Whole.withDensityReal ρ) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by
    rw [hc]
    exact integral_nonneg fun x => hρ.nonneg x
  have hcM : c ≤ M := by
    rw [hc]
    calc ∫ x, ρ x ∂(HRS.Whole.withDensityReal ρ)
        ≤ ∫ _x, M ∂(HRS.Whole.withDensityReal ρ) := integral_mono hρint (integrable_const M) (fun x => hM x)
      _ = M := by simp
  have hmean : ∫ x, (ρ x - c) ∂(HRS.Whole.withDensityReal ρ) = 0 := by
    rw [integral_sub hρint (integrable_const c), integral_const, ← hc]
    simp
  have hPb : ∀ x, |ρ x - c| ≤ M := fun x =>
    abs_le.2 ⟨by linarith [hρ.nonneg x, hcM], by linarith [hM x, hc0]⟩
  have hPL2 : MemLp (fun x => ρ x - c) 2 (HRS.Whole.withDensityReal ρ) :=
    MemLp.of_bound (hρ.measurable.sub measurable_const).aestronglyMeasurable M
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]
        exact hPb x)
  have hPZ : HRS.Whole.MemL2Zero (HRS.Whole.withDensityReal ρ) (fun x => ρ x - c) := by
    unfold HRS.Whole.MemL2Zero
    exact ⟨hPL2, hmean⟩
  have hproj : HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) (fun x => ρ x - c) =
      HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) ρ := by
    funext x
    simp only [HRS.Whole.projMean, HRS.Whole.pair]
    rw [hmean, ← hc]
    ring
  have hRe : HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β ρ =
      HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β (fun x => ρ x - c) := by
    unfold HRS.Whole.responseInverse HRS.Whole.IsResponse
    rw [hproj]
  have hcs := (HRS.Whole.convolution_susceptibility hd hs hsd ρ hρ M hM β hβ).2.2.2 (fun x => ρ x - c) hPZ
  have hPn : HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) (fun x => ρ x - c) ≤ M := by
    unfold HRS.Whole.l2Norm
    rw [Real.sqrt_le_left hM0]
    have h2 : ∫ x, (ρ x - c) ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤
        ∫ _x, M ^ 2 ∂(HRS.Whole.withDensityReal ρ) :=
      integral_mono hPL2.integrable_sq (integrable_const _) (fun x => by
        have h3 : |ρ x - c| * |ρ x - c| ≤ M * M :=
          mul_le_mul (hPb x) (hPb x) (abs_nonneg _) hM0
        nlinarith [abs_mul_abs_self (ρ x - c)])
    exact h2.trans (by simp)
  rw [hRe]
  exact hcs.2.2.2.2.trans hPn

theorem weighted_remainder_of_sharp_bias_proof (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) (β M : ℝ) (Λ : ℝ≥0)
    (hβ : 0 < β)
    (hSB : ∃ C : ℝ, ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) → LipschitzWith Λ ρ →
      ∀ N, 1 ≤ N → SharpBiasConclusion d s N β ρ C) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) → LipschitzWith Λ ρ →
      ∀ [IsProbabilityMeasure (HRS.Whole.withDensityReal ρ)] (N : ℕ), 1 ≤ N →
      ∀ (mN : Measure (Euc d)) [IsFiniteMeasure mN],
        mN = HRS.Whole.firstMarginal (HRS.Whole.modulatedGibbs (rieszKernel d s) N β (HRS.Whole.withDensityReal ρ)) →
        MemLp (biasDensity d s β ρ) 2 (HRS.Whole.withDensityReal ρ) ∧
        (∀ w : Euc d → ℝ, Measurable w → (∀ x, 0 ≤ w x) → MemLp w 2 (HRS.Whole.withDensityReal ρ) →
          ∫⁻ x, ENNReal.ofReal (w x) ∂(SignedMeasure.totalVariation
              (mN.toSignedMeasure - (HRS.Whole.withDensityReal ρ).toSignedMeasure -
                (deltaN d s N) • (HRS.Whole.withDensityReal ρ).withDensityᵥ (biasDensity d s β ρ))) ≤
            ENNReal.ofReal (C * deltaN d s N * (N : ℝ) ^ (-biasTheta d s) *
              l2Norm (HRS.Whole.withDensityReal ρ) w)) ∧
        ∀ E : Set (Euc d), MeasurableSet E →
          (SignedMeasure.totalVariation (mN.toSignedMeasure - (HRS.Whole.withDensityReal ρ).toSignedMeasure)) E /
              ENNReal.ofReal (deltaN d s N) +
            (SignedMeasure.totalVariation ((HRS.Whole.withDensityReal ρ).withDensityᵥ (biasDensity d s β ρ))) E ≤
          ENNReal.ofReal (C * Real.sqrt ((HRS.Whole.withDensityReal ρ E).toReal)) := by
  obtain ⟨C, hC⟩ := hSB
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = |C| + 2 * (|2 * HRS.Whole.biasConst d s * β ^ HRS.Whole.biasP d s| * M) := ⟨_, rfl⟩
  refine ⟨K, ?_⟩
  intro ρ hρ hM hΛ hPμ N hN mN hPmN hmN
  have hM0 : 0 ≤ M := le_trans (hρ.nonneg 0) (hM 0)
  have hCK : C ≤ K := by
    have hmul : 0 ≤ |2 * HRS.Whole.biasConst d s * β ^ HRS.Whole.biasP d s| * M := mul_nonneg (abs_nonneg _) hM0
    rw [hK]
    linarith [le_abs_self C]
  obtain ⟨_, hR, ⟨φ, hφm, hφ0, hφeq, hLe, hle⟩, _⟩ := hC ρ hρ hM hΛ N hN
  have hmN' : mN = (HRS.Whole.withDensityReal ρ).withDensity fun x => ENNReal.ofReal (φ x) :=
    hmN.trans hφeq
  have hδ : 0 < deltaN d s N := by
    unfold deltaN
    rw [if_neg (not_lt.mpr hs.le), if_neg hs.ne']
    exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr (by omega)) _
  have hδne : deltaN d s N ≠ 0 := hδ.ne'
  have hNθ : (N : ℝ) ^ (-HRS.Whole.biasTheta d s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by linarith [u12_theta_nonneg hd hs hsd])
  have hNθ0 : 0 ≤ (N : ℝ) ^ (-HRS.Whole.biasTheta d s) := Real.rpow_nonneg (by positivity) _
  obtain ⟨e, he_def⟩ : ∃ e : Euc d → ℝ,
      e = fun x => (φ x - 1) / deltaN d s N - HRS.Whole.biasDensity d s β ρ x := ⟨_, rfl⟩
  have heL : MemLp e 2 (HRS.Whole.withDensityReal ρ) := by
    rw [he_def]
    exact hLe
  have hle' : HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) e ≤ C * (N : ℝ) ^ (-HRS.Whole.biasTheta d s) := by
    rw [he_def]
    exact hle
  have hφe : ∀ x, φ x = deltaN d s N * e x + deltaN d s N * HRS.Whole.biasDensity d s β ρ x + 1 := by
    intro x
    have h1 : deltaN d s N * ((φ x - 1) / deltaN d s N) = φ x - 1 := by
      field_simp
    rw [he_def]
    dsimp only
    linear_combination (-1 : ℝ) * h1
  have hBL : MemLp (HRS.Whole.biasDensity d s β ρ) 2 (HRS.Whole.withDensityReal ρ) := by
    unfold HRS.Whole.biasDensity
    exact hR.const_mul _
  have hBint : Integrable (HRS.Whole.biasDensity d s β ρ) (HRS.Whole.withDensityReal ρ) :=
    hBL.integrable one_le_two
  have heint : Integrable e (HRS.Whole.withDensityReal ρ) := heL.integrable one_le_two
  have hφint : Integrable φ (HRS.Whole.withDensityReal ρ) := by
    have hfun : φ = fun x => deltaN d s N * e x + deltaN d s N * HRS.Whole.biasDensity d s β ρ x + 1 :=
      funext hφe
    rw [hfun]
    exact ((heint.const_mul _).add (hBint.const_mul _)).add (integrable_const 1)
  refine ⟨hBL, ?_, ?_⟩
  · -- weighted bound
    intro w hwm hw0 hwL
    rw [u12_tv_weighted (HRS.Whole.withDensityReal ρ) mN φ e (HRS.Whole.biasDensity d s β ρ) (deltaN d s N)
      hφ0 hφm hmN' hφe hφint heint hBint]
    have hfm : AEMeasurable (fun x => ENNReal.ofReal |deltaN d s N * e x|)
        (HRS.Whole.withDensityReal ρ) :=
      u12_aemeas _ (heL.const_mul _).aestronglyMeasurable
    have hgm : AEMeasurable (fun x => ENNReal.ofReal (w x)) (HRS.Whole.withDensityReal ρ) :=
      hwm.ennreal_ofReal.aemeasurable
    rw [lintegral_withDensity_eq_lintegral_mul₀ hfm hgm]
    have hfun : ((fun x => ENNReal.ofReal |deltaN d s N * e x|) *
        (fun x => ENNReal.ofReal (w x))) =
        fun x => ENNReal.ofReal (w x * |deltaN d s N * e x|) := by
      funext a
      simp only [Pi.mul_apply]
      rw [ENNReal.ofReal_mul (hw0 a), mul_comm]
    rw [hfun]
    refine (u12_cs _ hwL (heL.const_mul _) hw0).trans ?_
    rw [u12_l2Norm_smul, abs_of_pos hδ]
    apply ENNReal.ofReal_le_ofReal
    have hl2e : HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) e ≤ K * (N : ℝ) ^ (-HRS.Whole.biasTheta d s) :=
      le_trans hle' (mul_le_mul_of_nonneg_right hCK hNθ0)
    have h1 : deltaN d s N * HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) e ≤
        deltaN d s N * (K * (N : ℝ) ^ (-HRS.Whole.biasTheta d s)) :=
      mul_le_mul_of_nonneg_left hl2e hδ.le
    have h2 := mul_le_mul_of_nonneg_left h1 (u12_l2_nonneg (HRS.Whole.withDensityReal ρ) w)
    calc HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) w * (deltaN d s N * HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) e)
        ≤ HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) w *
            (deltaN d s N * (K * (N : ℝ) ^ (-HRS.Whole.biasTheta d s))) := h2
      _ = K * deltaN d s N * (N : ℝ) ^ (-HRS.Whole.biasTheta d s) * HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) w := by
          ring
  · -- tail bound
    intro E hE
    rw [u12_tv_diff (HRS.Whole.withDensityReal ρ) mN φ hφ0 hφm hmN' hφint,
      u12_tv (HRS.Whole.withDensityReal ρ) (HRS.Whole.biasDensity d s β ρ) hBint,
      withDensity_apply _ hE, withDensity_apply _ hE]
    have hpt : ∀ x, ENNReal.ofReal |(φ - 1) x| ≤
        ENNReal.ofReal (deltaN d s N) *
          (ENNReal.ofReal |e x| + ENNReal.ofReal |HRS.Whole.biasDensity d s β ρ x|) := by
      intro x
      rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _), ← ENNReal.ofReal_mul hδ.le]
      apply ENNReal.ofReal_le_ofReal
      have hφ1 : (φ - 1) x = deltaN d s N * e x + deltaN d s N * HRS.Whole.biasDensity d s β ρ x := by
        simp only [Pi.sub_apply, Pi.one_apply]
        linarith [hφe x]
      rw [hφ1]
      calc |deltaN d s N * e x + deltaN d s N * HRS.Whole.biasDensity d s β ρ x|
          ≤ |deltaN d s N * e x| + |deltaN d s N * HRS.Whole.biasDensity d s β ρ x| := abs_add_le _ _
        _ = deltaN d s N * (|e x| + |HRS.Whole.biasDensity d s β ρ x|) := by
          rw [abs_mul, abs_mul, abs_of_pos hδ]
          ring
    have hAe : AEMeasurable (fun x => ENNReal.ofReal |e x|)
        ((HRS.Whole.withDensityReal ρ).restrict E) :=
      (u12_aemeas _ heL.aestronglyMeasurable).restrict
    have hX : ∫⁻ x in E, ENNReal.ofReal |(φ - 1) x| ∂(HRS.Whole.withDensityReal ρ) ≤
        ENNReal.ofReal (deltaN d s N) *
          (∫⁻ x in E, ENNReal.ofReal |e x| ∂(HRS.Whole.withDensityReal ρ) +
            ∫⁻ x in E, ENNReal.ofReal |HRS.Whole.biasDensity d s β ρ x| ∂(HRS.Whole.withDensityReal ρ)) := by
      calc ∫⁻ x in E, ENNReal.ofReal |(φ - 1) x| ∂(HRS.Whole.withDensityReal ρ)
          ≤ ∫⁻ x in E, ENNReal.ofReal (deltaN d s N) *
              (ENNReal.ofReal |e x| + ENNReal.ofReal |HRS.Whole.biasDensity d s β ρ x|)
              ∂(HRS.Whole.withDensityReal ρ) := lintegral_mono fun x => hpt x
        _ = ENNReal.ofReal (deltaN d s N) *
              (∫⁻ x in E, ENNReal.ofReal |e x| ∂(HRS.Whole.withDensityReal ρ) +
                ∫⁻ x in E, ENNReal.ofReal |HRS.Whole.biasDensity d s β ρ x| ∂(HRS.Whole.withDensityReal ρ)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' hAe]
    have h1 : (∫⁻ x in E, ENNReal.ofReal |(φ - 1) x| ∂(HRS.Whole.withDensityReal ρ)) /
        ENNReal.ofReal (deltaN d s N) ≤
        ∫⁻ x in E, ENNReal.ofReal |e x| ∂(HRS.Whole.withDensityReal ρ) +
          ∫⁻ x in E, ENNReal.ofReal |HRS.Whole.biasDensity d s β ρ x| ∂(HRS.Whole.withDensityReal ρ) := by
      apply ENNReal.div_le_of_le_mul
      rw [mul_comm]
      exact hX
    have h2 := u12_restrict (HRS.Whole.withDensityReal ρ) hE heL
    have h3 := u12_restrict (HRS.Whole.withDensityReal ρ) hE hBL
    have hBn : HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) (HRS.Whole.biasDensity d s β ρ) ≤
        |2 * HRS.Whole.biasConst d s * β ^ HRS.Whole.biasP d s| * M := by
      have hB_eq : HRS.Whole.biasDensity d s β ρ = fun x =>
          (2 * HRS.Whole.biasConst d s * β ^ HRS.Whole.biasP d s) *
            HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β ρ x := rfl
      rw [hB_eq, u12_l2Norm_smul]
      exact mul_le_mul_of_nonneg_left (u12_R_l2 hd hs hsd β M hβ ρ hρ hM) (abs_nonneg _)
    have he5 : HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) e ≤ |C| := by
      have hC1 : C * (N : ℝ) ^ (-HRS.Whole.biasTheta d s) ≤ |C| :=
        le_trans (mul_le_mul_of_nonneg_right (le_abs_self C) hNθ0)
          (mul_le_of_le_one_right (abs_nonneg C) hNθ)
      exact hle'.trans hC1
    have hsq : 0 ≤ Real.sqrt ((HRS.Whole.withDensityReal ρ) E).toReal := Real.sqrt_nonneg _
    have ha : 0 ≤ Real.sqrt ((HRS.Whole.withDensityReal ρ) E).toReal *
        HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) e := mul_nonneg hsq (u12_l2_nonneg _ _)
    have hb : 0 ≤ Real.sqrt ((HRS.Whole.withDensityReal ρ) E).toReal *
        HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) (HRS.Whole.biasDensity d s β ρ) := mul_nonneg hsq (u12_l2_nonneg _ _)
    have hkey : Real.sqrt ((HRS.Whole.withDensityReal ρ) E).toReal * HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) e +
        Real.sqrt ((HRS.Whole.withDensityReal ρ) E).toReal *
          HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) (HRS.Whole.biasDensity d s β ρ) +
        Real.sqrt ((HRS.Whole.withDensityReal ρ) E).toReal *
          HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) (HRS.Whole.biasDensity d s β ρ) ≤
        K * Real.sqrt ((HRS.Whole.withDensityReal ρ) E).toReal := by
      have a1 := mul_le_mul_of_nonneg_left he5 hsq
      have a2 := mul_le_mul_of_nonneg_left hBn hsq
      calc _ ≤ Real.sqrt ((HRS.Whole.withDensityReal ρ) E).toReal * |C| +
            Real.sqrt ((HRS.Whole.withDensityReal ρ) E).toReal *
              (|2 * HRS.Whole.biasConst d s * β ^ HRS.Whole.biasP d s| * M) +
            Real.sqrt ((HRS.Whole.withDensityReal ρ) E).toReal *
              (|2 * HRS.Whole.biasConst d s * β ^ HRS.Whole.biasP d s| * M) := by linarith
        _ = K * Real.sqrt ((HRS.Whole.withDensityReal ρ) E).toReal := by
          rw [hK]
          ring
    calc (∫⁻ x in E, ENNReal.ofReal |(φ - 1) x| ∂(HRS.Whole.withDensityReal ρ)) /
          ENNReal.ofReal (deltaN d s N) +
          ∫⁻ x in E, ENNReal.ofReal |HRS.Whole.biasDensity d s β ρ x| ∂(HRS.Whole.withDensityReal ρ)
        ≤ (∫⁻ x in E, ENNReal.ofReal |e x| ∂(HRS.Whole.withDensityReal ρ) +
            ∫⁻ x in E, ENNReal.ofReal |HRS.Whole.biasDensity d s β ρ x| ∂(HRS.Whole.withDensityReal ρ)) +
          ∫⁻ x in E, ENNReal.ofReal |HRS.Whole.biasDensity d s β ρ x| ∂(HRS.Whole.withDensityReal ρ) :=
          add_le_add h1 le_rfl
      _ ≤ ENNReal.ofReal (Real.sqrt ((HRS.Whole.withDensityReal ρ) E).toReal *
              HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) e) +
            ENNReal.ofReal (Real.sqrt ((HRS.Whole.withDensityReal ρ) E).toReal *
              HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) (HRS.Whole.biasDensity d s β ρ)) +
          ENNReal.ofReal (Real.sqrt ((HRS.Whole.withDensityReal ρ) E).toReal *
              HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) (HRS.Whole.biasDensity d s β ρ)) :=
          add_le_add (add_le_add h2 h3) h3
      _ = ENNReal.ofReal (Real.sqrt ((HRS.Whole.withDensityReal ρ) E).toReal *
              HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) e +
            Real.sqrt ((HRS.Whole.withDensityReal ρ) E).toReal *
              HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) (HRS.Whole.biasDensity d s β ρ) +
            Real.sqrt ((HRS.Whole.withDensityReal ρ) E).toReal *
              HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) (HRS.Whole.biasDensity d s β ρ)) := by
          rw [← ENNReal.ofReal_add ha hb, ← ENNReal.ofReal_add (add_nonneg ha hb) hb]
      _ ≤ ENNReal.ofReal (K * Real.sqrt ((HRS.Whole.withDensityReal ρ) E).toReal) :=
          ENNReal.ofReal_le_ofReal hkey

end HRS.MS.SuppN
