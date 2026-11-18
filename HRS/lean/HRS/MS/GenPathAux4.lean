import HRS.MS.GenPathAux3

/-!
# S5.6 packet P2: the covariance error in expectation (`W:r2:trace-comparison`, S L3440-3458)

`s56_trace_moment`: `E ∫_0^T ‖C_r - C̄_r‖_{𝔖₁} dr ≤ C q w_N` with `w_N = generalLocalizationRate d E_{N,1} M₂ N`
(`inf_{R ≥ 1} {R^{d/2}(N^{-1/d} + √E_{N,1}) + (1+M₂) R^{-2}}`), from the pathwise bound `s56_trace_pathwise`, Tonelli,
Cauchy-Schwarz (`E√𝓔 ≤ √(E𝓔)`) and the infimum over `R`.  The joint measurability of the energy and of the empirical
second moment in `(r,ζ)` enters as hypotheses (`s56_energy_aemeas`, packet P4, discharges it).
Helper names carry the prefix `s56_`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.GenPath

open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

/-- `E g ≤ (E g²)^{1/2}` on a probability space. -/
theorem s56_lintegral_le_sqrt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {g : Ω → ℝ≥0∞} (hg : AEMeasurable g P) :
    ∫⁻ ζ, g ζ ∂P ≤ (∫⁻ ζ, g ζ ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two
    (f := fun _ : Ω => (1 : ℝ≥0∞)) aemeasurable_const hg
  simpa using h

/-- Infimum over `R ≥ 1` of a bound valid for every `R`. -/
theorem s56_le_iInf {X : ℝ≥0∞} {K : ℝ} (hK : 0 ≤ K) (φ : {R : ℝ // 1 ≤ R} → ℝ) (h0 : ∀ R, 0 ≤ φ R)
    (h : ∀ R, X ≤ ENNReal.ofReal (K * φ R)) : X ≤ ENNReal.ofReal (K * ⨅ R, φ R) := by
  haveI : Nonempty {R : ℝ // 1 ≤ R} := ⟨⟨1, le_rfl⟩⟩
  have hbdd : BddBelow (Set.range φ) := ⟨0, by rintro _ ⟨R, rfl⟩; exact h0 R⟩
  have hinf0 : 0 ≤ ⨅ R, φ R := le_ciInf h0
  rcases hK.eq_or_lt with rfl | hKpos
  · have := h ⟨1, le_rfl⟩
    simpa using this
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε' : (0 : ℝ) < ε / K := by positivity
    obtain ⟨R, hR⟩ := exists_lt_of_ciInf_lt (show ⨅ R, φ R < (⨅ R, φ R) + ε / K by linarith)
    refine (h R).trans ?_
    have : K * φ R ≤ K * (⨅ R, φ R) + ε := by
      have := mul_le_mul_of_nonneg_left hR.le hKpos.le
      calc K * φ R ≤ K * ((⨅ R, φ R) + ε / K) := this
        _ = K * (⨅ R, φ R) + ε := by field_simp
    calc ENNReal.ofReal (K * φ R) ≤ ENNReal.ofReal (K * (⨅ R, φ R) + ε) := ENNReal.ofReal_le_ofReal this
      _ ≤ ENNReal.ofReal (K * ⨅ R, φ R) + ENNReal.ofReal ε := ENNReal.ofReal_add_le
      _ = ENNReal.ofReal (K * ⨅ R, φ R) + (ε : ℝ≥0∞) := by rw [ENNReal.ofReal_coe_nnreal]

/-- Hölder (`p = q = 2`) for a finite measure: `∫ g ≤ μ(univ)^{1/2} (∫ g²)^{1/2}`. -/
theorem s56_lintegral_le_sqrt' {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {g : α → ℝ≥0∞} (hg : AEMeasurable g μ) :
    ∫⁻ z, g z ∂μ ≤ (μ Set.univ) ^ (1 / 2 : ℝ) * (∫⁻ z, g z ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (f := fun _ : α => (1 : ℝ≥0∞)) aemeasurable_const hg
  simpa using h

/-- The abstract moment bound: if `f ≤ c [a(n + √en) + (mm + M₂) R2]` on `[0,T]` then
`E∫_0^T f ≤ c T [a(n + √E₁) + 2 M₂ R2]` when `E ofReal(en_r) ≤ E₁` and `E ofReal(mm_r) ≤ M₂` for `r ∈ [0,T]`. -/
theorem s56_moment_core {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 ≤ T) (en mm : Ω → ℝ → ℝ)
    (hen : AEMeasurable (fun p : Ω × ℝ => en p.1 p.2) (P.prod (volume.restrict (Set.Icc 0 T))))
    (hmm : AEMeasurable (fun p : Ω × ℝ => mm p.1 p.2) (P.prod (volume.restrict (Set.Icc 0 T))))
    {E₁ : ℝ≥0∞} (hE₁ : E₁ ≠ ⊤) (hE : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫⁻ ζ, ENNReal.ofReal (en ζ r) ∂P ≤ E₁)
    {M₂ : ℝ} (hM₂ : 0 ≤ M₂)
    (hM : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫⁻ ζ, ENNReal.ofReal (mm ζ r) ∂P ≤ ENNReal.ofReal M₂)
    (hmm0 : ∀ ζ r, 0 ≤ mm ζ r) {c a n R2 : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (hn : 0 ≤ n) (hR2 : 0 ≤ R2)
    (f : Ω → ℝ → ℝ≥0∞)
    (hf : ∀ᵐ ζ ∂P, ∀ r ∈ Set.Icc (0 : ℝ) T,
      f ζ r ≤ ENNReal.ofReal (c * (a * (n + Real.sqrt (en ζ r)) + (mm ζ r + M₂) * R2))) :
    ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) T, f ζ r) ∂P ≤
      ENNReal.ofReal (c * T * (a * (n + Real.sqrt E₁.toReal) + 2 * M₂ * R2)) := by
  set μT : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμT
  set G : Ω × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (a * n) + ENNReal.ofReal a * ENNReal.ofReal (Real.sqrt (en z.1 z.2)) +
    ENNReal.ofReal R2 * ENNReal.ofReal (mm z.1 z.2) + ENNReal.ofReal (M₂ * R2) with hG
  have hμuniv : μT Set.univ = ENNReal.ofReal T := by
    rw [hμT, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
  have hρuniv : (P.prod μT) Set.univ = ENNReal.ofReal T := by
    rw [← Set.univ_prod_univ, Measure.prod_prod, measure_univ, one_mul, hμuniv]
  have hg1 : AEMeasurable (fun z : Ω × ℝ => ENNReal.ofReal (Real.sqrt (en z.1 z.2))) (P.prod μT) :=
    (Real.continuous_sqrt.measurable.comp_aemeasurable hen).ennreal_ofReal
  have hg2 : AEMeasurable (fun z : Ω × ℝ => ENNReal.ofReal (mm z.1 z.2)) (P.prod μT) := hmm.ennreal_ofReal
  have hGm : AEMeasurable G (P.prod μT) := by
    refine (((aemeasurable_const.add (hg1.const_mul _)).add (hg2.const_mul _)).add aemeasurable_const)
  -- step 1: pointwise domination
  have hstep1 : ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) T, f ζ r) ∂P ≤
      ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal c * G (ζ, r)) ∂P := by
    refine lintegral_mono_ae ?_
    filter_upwards [hf] with ζ hζ
    refine setLIntegral_mono' measurableSet_Icc fun r hr => (hζ r hr).trans (le_of_eq ?_)
    simp only [hG]
    have hs : 0 ≤ Real.sqrt (en ζ r) := Real.sqrt_nonneg _
    have hm : 0 ≤ mm ζ r := hmm0 ζ r
    have hsum : ENNReal.ofReal (a * n) + ENNReal.ofReal a * ENNReal.ofReal (Real.sqrt (en ζ r)) +
        ENNReal.ofReal R2 * ENNReal.ofReal (mm ζ r) + ENNReal.ofReal (M₂ * R2) =
        ENNReal.ofReal (a * n + a * Real.sqrt (en ζ r) + R2 * mm ζ r + M₂ * R2) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul ha (q := Real.sqrt (en ζ r)), ENNReal.ofReal_mul hR2 (q := mm ζ r)]
    have e : c * (a * (n + Real.sqrt (en ζ r)) + (mm ζ r + M₂) * R2) =
        c * (a * n + a * Real.sqrt (en ζ r) + R2 * mm ζ r + M₂ * R2) := by ring
    rw [e, ENNReal.ofReal_mul hc, hsum]
  refine hstep1.trans ?_
  set ρ : Measure (Ω × ℝ) := P.prod μT with hρ
  -- step 2: pull out the constant and pass to the product measure
  have h2 : ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal c * G (ζ, r)) ∂P =
      ENNReal.ofReal c * ∫⁻ z, G z ∂ρ := by
    simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    rw [hρ, lintegral_prod _ hGm]
  rw [h2]
  -- step 3: the three integrals
  have hpt : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫⁻ ζ, ENNReal.ofReal (Real.sqrt (en ζ r)) ^ (2 : ℝ) ∂P ≤ E₁ := by
    intro r hr
    refine le_trans (lintegral_mono fun ζ => ?_) (hE r hr)
    by_cases h : 0 ≤ en ζ r
    · rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.sq_sqrt h]
    · rw [Real.sqrt_eq_zero_of_nonpos (not_le.1 h).le]
      simp
  have hint1 : ∫⁻ z, ENNReal.ofReal (Real.sqrt (en z.1 z.2)) ∂ρ ≤
      ENNReal.ofReal T * E₁ ^ (1 / 2 : ℝ) := by
    refine (s56_lintegral_le_sqrt' ρ hg1).trans ?_
    rw [hρuniv]
    have hsw : ∫⁻ z, ENNReal.ofReal (Real.sqrt (en z.1 z.2)) ^ (2 : ℝ) ∂ρ ≤ E₁ * ENNReal.ofReal T := by
      rw [hρ, lintegral_prod_symm _ (hg1.pow_const _)]
      simp only
      calc ∫⁻ r, ∫⁻ ζ, ENNReal.ofReal (Real.sqrt (en ζ r)) ^ (2 : ℝ) ∂P ∂μT
          ≤ ∫⁻ r, E₁ ∂μT := by
            rw [hμT]
            exact setLIntegral_mono' measurableSet_Icc hpt
        _ = E₁ * ENNReal.ofReal T := by rw [lintegral_const, hμuniv]
    calc ENNReal.ofReal T ^ (1 / 2 : ℝ) * (∫⁻ z, ENNReal.ofReal (Real.sqrt (en z.1 z.2)) ^ (2 : ℝ) ∂ρ) ^ (1 / 2 : ℝ)
        ≤ ENNReal.ofReal T ^ (1 / 2 : ℝ) * (E₁ * ENNReal.ofReal T) ^ (1 / 2 : ℝ) := by
          gcongr
      _ = ENNReal.ofReal T * E₁ ^ (1 / 2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          have : ENNReal.ofReal T ^ (1 / 2 : ℝ) * ENNReal.ofReal T ^ (1 / 2 : ℝ) = ENNReal.ofReal T := by
            rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
            norm_num
          calc ENNReal.ofReal T ^ (1 / 2 : ℝ) * (E₁ ^ (1 / 2 : ℝ) * ENNReal.ofReal T ^ (1 / 2 : ℝ))
              = (ENNReal.ofReal T ^ (1 / 2 : ℝ) * ENNReal.ofReal T ^ (1 / 2 : ℝ)) * E₁ ^ (1 / 2 : ℝ) := by ring
            _ = _ := by rw [this]
  have hint2 : ∫⁻ z, ENNReal.ofReal (mm z.1 z.2) ∂ρ ≤ ENNReal.ofReal M₂ * ENNReal.ofReal T := by
    rw [hρ, lintegral_prod_symm _ hg2]
    simp only
    calc ∫⁻ r, ∫⁻ ζ, ENNReal.ofReal (mm ζ r) ∂P ∂μT ≤ ∫⁻ r, ENNReal.ofReal M₂ ∂μT := by
          rw [hμT]
          exact setLIntegral_mono' measurableSet_Icc hM
      _ = ENNReal.ofReal M₂ * ENNReal.ofReal T := by rw [lintegral_const, hμuniv]
  have hGint : ∫⁻ z, G z ∂ρ =
      ENNReal.ofReal (a * n) * ENNReal.ofReal T + ENNReal.ofReal a * ∫⁻ z, ENNReal.ofReal (Real.sqrt (en z.1 z.2)) ∂ρ +
      ENNReal.ofReal R2 * ∫⁻ z, ENNReal.ofReal (mm z.1 z.2) ∂ρ + ENNReal.ofReal (M₂ * R2) * ENNReal.ofReal T := by
    simp only [hG]
    have hA : AEMeasurable (fun z : Ω × ℝ => ENNReal.ofReal (a * n) +
        ENNReal.ofReal a * ENNReal.ofReal (Real.sqrt (en z.1 z.2)) +
        ENNReal.ofReal R2 * ENNReal.ofReal (mm z.1 z.2)) ρ :=
      (aemeasurable_const.add (hg1.const_mul _)).add (hg2.const_mul _)
    have hB : AEMeasurable (fun z : Ω × ℝ => ENNReal.ofReal (a * n) +
        ENNReal.ofReal a * ENNReal.ofReal (Real.sqrt (en z.1 z.2))) ρ :=
      aemeasurable_const.add (hg1.const_mul _)
    rw [lintegral_add_left' hA (fun _ => ENNReal.ofReal (M₂ * R2)), lintegral_add_left' hB
      (fun z : Ω × ℝ => ENNReal.ofReal R2 * ENNReal.ofReal (mm z.1 z.2)),
      lintegral_add_left' (aemeasurable_const (b := ENNReal.ofReal (a * n)))
        (fun z : Ω × ℝ => ENNReal.ofReal a * ENNReal.ofReal (Real.sqrt (en z.1 z.2))),
      lintegral_const, lintegral_const, lintegral_const_mul'' _ hg1, lintegral_const_mul'' _ hg2, hρuniv]
  have hbound : ∫⁻ z, G z ∂ρ ≤ ENNReal.ofReal (a * n) * ENNReal.ofReal T +
      ENNReal.ofReal a * (ENNReal.ofReal T * E₁ ^ (1 / 2 : ℝ)) +
      ENNReal.ofReal R2 * (ENNReal.ofReal M₂ * ENNReal.ofReal T) + ENNReal.ofReal (M₂ * R2) * ENNReal.ofReal T := by
    rw [hGint]
    gcongr
  have hE₁r : E₁ ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt E₁.toReal) := by
    conv_lhs => rw [← ENNReal.ofReal_toReal hE₁]
    rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num), Real.sqrt_eq_rpow]
  rw [hE₁r] at hbound
  have hse : 0 ≤ Real.sqrt E₁.toReal := Real.sqrt_nonneg _
  refine (mul_le_mul' le_rfl hbound).trans (le_of_eq ?_)
  have e1 : c * T * (a * (n + Real.sqrt E₁.toReal) + 2 * M₂ * R2) =
      c * (a * n * T + a * (T * Real.sqrt E₁.toReal) + R2 * (M₂ * T) + M₂ * R2 * T) := by ring
  rw [e1, ENNReal.ofReal_mul hc, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by positivity : 0 ≤ a * n), ENNReal.ofReal_mul ha (q := T * Real.sqrt E₁.toReal),
    ENNReal.ofReal_mul hT (q := Real.sqrt E₁.toReal), ENNReal.ofReal_mul hR2 (q := M₂ * T),
    ENNReal.ofReal_mul hM₂ (q := T), ENNReal.ofReal_mul (by positivity : 0 ≤ M₂ * R2) (q := T)]


theorem s56_trace_moment (b₀ : WholeBounds d) (hb : b₀.Valid) :
    ∃ C₀min : ℝ, ∀ b : WholeBounds d, b = { b₀ with C₀ := b.C₀ } → C₀min ≤ b.C₀ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : WholeSetup b, ∀ N : ℕ, 2 ≤ N → ∀ q : ℝ, 0 ≤ q → ∀ M₂ : ℝ, 0 ≤ M₂ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : ℝ≥0 → Ω → EucConfig d N),
      (∀ᵐ ζ ∂P, ∀ t ∈ Set.Icc (0 : ℝ) b.T, Function.Injective (X (Real.toNNReal t) ζ)) →
      AEMeasurable (fun p : Ω × ℝ => rieszModulatedEnergy d b.s (X (Real.toNNReal p.2) p.1)
        (HRS.Whole.withDensityReal (S.ρ N p.2)) + HRS.oN d b.s b.C₀ N)
        (P.prod (volume.restrict (Set.Icc 0 b.T))) →
      AEMeasurable (fun p : Ω × ℝ => secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal p.2) p.1)))
        (P.prod (volume.restrict (Set.Icc 0 b.T))) →
      (∀ t ∈ Set.Icc (0 : ℝ) b.T,
        ∫⁻ ζ, ENNReal.ofReal (secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal t) ζ))) ∂P ≤
          ENNReal.ofReal M₂ ∧
        ENNReal.ofReal (secondMomentOf (HRS.Whole.withDensityReal (S.ρ N t))) ≤ ENNReal.ofReal M₂) →
      S.energyMomentE N 1 P X ≠ ⊤ →
      ∀ (B₁ : ℝ → Ω → KSpace d b.m b.T →L[ℝ] KSpace d b.m b.T →L[ℝ] ℝ)
        (B₂ : ℝ → KSpace d b.m b.T →L[ℝ] KSpace d b.m b.T →L[ℝ] ℝ),
      (∀ r ∈ Set.Icc (0 : ℝ) b.T, ∀ ζ u v, B₁ r ζ u v = featureForm b.m b.T q
        (fun a => gradFeature (S.coeff N) b.m b.T a r) (HRS.Whole.empirical (X (Real.toNNReal r) ζ)) u v) →
      (∀ r ∈ Set.Icc (0 : ℝ) b.T, ∀ u v, B₂ r u v = featureForm b.m b.T q
        (fun a => gradFeature (S.coeff N) b.m b.T a r) (HRS.Whole.withDensityReal (S.ρ N r)) u v) →
      ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) b.T, ENNReal.ofReal (HRS.traceNormForm (B₁ r ζ - B₂ r))) ∂P ≤
        ENNReal.ofReal (C * q * generalLocalizationRate d (S.energyMomentE N 1 P X).toReal M₂ N) := by
  obtain ⟨C₀min, hC⟩ := s56_trace_pathwise b₀ hb
  refine ⟨C₀min, fun b hbeq hC0 => ?_⟩
  obtain ⟨C₁, hC₁0, hpw⟩ := hC b hbeq hC0
  have hbv : b.Valid := s56_valid_of_eq hb hbeq
  have hT0 : 0 ≤ b.T := hbv.hT.le
  have hd1 : 1 ≤ d := by have := hbv.hd; omega
  refine ⟨2 * C₁ * b.T, by positivity, fun S N hN q hq M₂ hM₂ Ω _ P _ X hinj hen hmm hM hE B₁ B₂ h1 h2 => ?_⟩
  set E₁ := S.energyMomentE N 1 P X with hE₁def
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have hEr : ∀ r ∈ Set.Icc (0 : ℝ) b.T, ∫⁻ ζ, ENNReal.ofReal (rieszModulatedEnergy d b.s
      (X (Real.toNNReal r) ζ) (HRS.Whole.withDensityReal (S.ρ N r)) + HRS.oN d b.s b.C₀ N) ∂P ≤ E₁ := by
    intro r hr
    have h := le_iSup (fun t : Set.Icc (0 : ℝ) b.T => (∫⁻ ζ, ENNReal.ofReal |rieszModulatedEnergy d b.s
        (X (Real.toNNReal t) ζ) (HRS.Whole.withDensityReal (S.ρ N t)) + HRS.oN d b.s b.C₀ N| ^ (1 : ℝ) ∂P) ^
        (1 / (1 : ℝ))) ⟨r, hr⟩
    refine le_trans ?_ h
    simp only [ENNReal.rpow_one, div_one]
    exact lintegral_mono fun ζ => ENNReal.ofReal_le_ofReal (le_abs_self _)
  -- the bound for each `R ≥ 1`
  have hR : ∀ R : {R : ℝ // 1 ≤ R}, ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) b.T,
      ENNReal.ofReal (HRS.traceNormForm (B₁ r ζ - B₂ r))) ∂P ≤
      ENNReal.ofReal (2 * C₁ * b.T * q * (R.1 ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 / (d : ℝ))) +
        Real.sqrt E₁.toReal) + (1 + M₂) * R.1 ^ (-(2 : ℝ)))) := by
    intro R
    have hRpos : 0 < R.1 := by linarith [R.2]
    have hcore := s56_moment_core P hT0
      (fun ζ r => rieszModulatedEnergy d b.s (X (Real.toNNReal r) ζ)
        (HRS.Whole.withDensityReal (S.ρ N r)) + HRS.oN d b.s b.C₀ N)
      (fun ζ r => secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal r) ζ))) hen hmm hE hEr hM₂
      (fun r hr => (hM r hr).1) (fun ζ r => s56_secondMoment_nonneg _)
      (c := C₁ * q) (a := R.1 ^ ((d : ℝ) / 2)) (n := (N : ℝ) ^ (-(1 / (d : ℝ)))) (R2 := 1 / R.1 ^ 2)
      (by positivity) (by positivity) (by positivity) (by positivity)
      (fun ζ r => ENNReal.ofReal (HRS.traceNormForm (B₁ r ζ - B₂ r))) (by
        filter_upwards [hinj] with ζ hζ r hr
        have hpwr := hpw S N hN q hq r hr (X (Real.toNNReal r) ζ) (hζ r hr) R.1 R.2 (B₁ r ζ) (B₂ r)
          (h1 r hr ζ) (h2 r hr)
        refine ENNReal.ofReal_le_ofReal (hpwr.trans ?_)
        have hm' : secondMomentOf (HRS.Whole.withDensityReal (S.ρ N r)) ≤ M₂ :=
          (ENNReal.ofReal_le_ofReal_iff hM₂).1 (hM r hr).2
        have : -(1 : ℝ) / d = -(1 / (d : ℝ)) := by ring
        rw [this]
        have hmm0 := s56_secondMoment_nonneg (HRS.Whole.empirical (X (Real.toNNReal r) ζ))
        have hpos : 0 ≤ C₁ * q := by positivity
        have hdiv : (secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal r) ζ)) +
            secondMomentOf (HRS.Whole.withDensityReal (S.ρ N r))) / R.1 ^ 2 ≤
            (secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal r) ζ)) + M₂) * (1 / R.1 ^ 2) := by
          rw [mul_one_div]
          gcongr
        calc C₁ * q * (R.1 ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 / (d : ℝ))) + Real.sqrt (rieszModulatedEnergy d b.s
              (X (Real.toNNReal r) ζ) (HRS.Whole.withDensityReal (S.ρ N r)) + HRS.oN d b.s b.C₀ N)) +
              (secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal r) ζ)) +
                secondMomentOf (HRS.Whole.withDensityReal (S.ρ N r))) / R.1 ^ 2)
            ≤ C₁ * q * (R.1 ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 / (d : ℝ))) + Real.sqrt (rieszModulatedEnergy d b.s
              (X (Real.toNNReal r) ζ) (HRS.Whole.withDensityReal (S.ρ N r)) + HRS.oN d b.s b.C₀ N)) +
              (secondMomentOf (HRS.Whole.empirical (X (Real.toNNReal r) ζ)) + M₂) * (1 / R.1 ^ 2)) := by
              gcongr
          _ = _ := rfl)
    refine hcore.trans (ENNReal.ofReal_le_ofReal ?_)
    have hrneg : R.1 ^ (-(2 : ℝ)) = 1 / R.1 ^ 2 := by
      rw [Real.rpow_neg hRpos.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
    rw [hrneg]
    have h1' : 0 ≤ C₁ * q * b.T := by positivity
    have h2' : 0 ≤ R.1 ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 / (d : ℝ))) + Real.sqrt E₁.toReal) := by positivity
    have h3' : 0 ≤ M₂ * (1 / R.1 ^ 2) := by positivity
    have hR2 : 0 ≤ 1 / R.1 ^ 2 := by positivity
    nlinarith [mul_nonneg h1' h2', mul_nonneg h1' h3', mul_nonneg h1' hR2]
  refine s56_le_iInf (K := 2 * C₁ * b.T * q) (by positivity) (fun R : {R : ℝ // 1 ≤ R} =>
    R.1 ^ ((d : ℝ) / 2) * ((N : ℝ) ^ (-(1 / (d : ℝ))) + Real.sqrt E₁.toReal) +
      (1 + M₂) * R.1 ^ (-(2 : ℝ))) (fun R : {R : ℝ // 1 ≤ R} => by
      have : 0 < R.1 := by linarith [R.2]
      positivity) hR |>.trans (le_of_eq ?_)
  unfold generalLocalizationRate
  rfl

end HRS.MS.GenPath
