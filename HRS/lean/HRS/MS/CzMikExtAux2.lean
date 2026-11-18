import HRS.MS.CzMikExtAux1

/-!
# MIK-2, part 2: the `L^p` extension and commutation with `L^1` convolutions

Continuation of `CzMikExtAux1.lean` (`mik2_T m u = 𝓕⁻(m 𝓕 u)`, `mikhlin_Lp_schwartz`).

* `mik2_memLp`: for a Schwartz `u` the function `mik2_T m u` (continuous and bounded) lies in `L^p`.
* `mikhlin_Lp_extend`: for a Mikhlin symbol `m` with constant `A` there is a continuous linear map
  `T : L^p → L^p` of norm `≤ C A` (`C = C(d,p)`) with `T [u] = [mik2_T m u]` for every Schwartz `u`
  (`[·]` = class in `L^p`).  The statement carries the instance `Fact (1 ≤ ENNReal.ofReal p)` needed for the
  normed structure of `Lp`; `mik2_fact` produces it from `1 < p`.  `mikhlin_Lp_extend_unique`: such a `T` is
  unique (density of Schwartz functions in `L^p`).
* `mikhlin_comm_conv`: for every continuous linear `T : L^p → L^p` agreeing with `mik2_T m` on Schwartz
  functions (so for the extension above), every `k ∈ L^1` and Schwartz `u`: with `k ⋆ u ∈ L^p` (automatic,
  `mik2_memLp_cv`), `T [k ⋆ u] = k ⋆ (mik2_T m u)` a.e.  Here `k ⋆ g = cv k g`, `(k ⋆ g)(x) = ∫ k(y) g(x-y) dy`
  (Bochner integral; for `g` bounded and `k` integrable the integrand is integrable for every `x`, so no junk
  value occurs).

Proof of the commutation: `k` is approximated in `L^1` by Schwartz functions `κ_j`; for those `κ_j ⋆ u` is the
Schwartz function `𝓕⁻(𝓕κ_j 𝓕u)` and `mik2_T m (κ_j ⋆ u) = κ_j ⋆ mik2_T m u` follows from the identity
`k ⋆ 𝓕⁻G = 𝓕⁻(𝓕k · G)` (`k, G ∈ L^1`, the multiplication formula for the Fourier transform); the limit
`j → ∞` is taken in `L^p` by Young's inequality and continuity of `T`.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section
namespace HRS.CZ.Mik
open HRS.Commutator.Whole HRS.Commutator.Whole.XLI HRS.Commutator.Whole.XNRS HRS.Commutator.Whole.XBB
variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma mik2_fact {p : ℝ} (hp : 1 < p) : Fact (1 ≤ ENNReal.ofReal p) :=
  ⟨by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le⟩

/-! ### The Fourier integral `mik2_T m u` is a bounded continuous function, linear in `u` -/

lemma mik2_exp_integrable {g : 𝔼 → ℂ} (hg : Integrable g) (x : 𝔼) :
    Integrable (fun ξ : 𝔼 => Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) • g ξ) := by
  have hexp : Continuous (fun ξ : 𝔼 =>
      Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I)) := by fun_prop
  simpa only [smul_eq_mul] using hg.bdd_mul (c := 1) hexp.aestronglyMeasurable
    (Eventually.of_forall fun ξ => by rw [Complex.norm_exp_ofReal_mul_I])

lemma mik2_T_apply (m : 𝔼 → ℂ) (u : 𝓢(𝔼, ℂ)) (x : 𝔼) :
    mik2_T m u x = ∫ ξ : 𝔼, Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) •
      (m ξ * 𝓕 (⇑u) ξ) := by
  unfold mik2_T; rw [Real.fourierInv_eq']

lemma mik2_fourier_add (u v : 𝓢(𝔼, ℂ)) (ξ : 𝔼) : 𝓕 (⇑(u + v)) ξ = 𝓕 (⇑u) ξ + 𝓕 (⇑v) ξ := by
  have h : (𝓕 (u + v) : 𝓢(𝔼, ℂ)) = 𝓕 u + 𝓕 v := by
    have := (SchwartzMap.fourierTransformCLM ℂ (E := ℂ) (V := 𝔼)).map_add u v
    simpa only [SchwartzMap.fourierTransformCLM_apply] using this
  rw [← SchwartzMap.fourier_coe, h, SchwartzMap.add_apply, SchwartzMap.fourier_coe,
    SchwartzMap.fourier_coe]

lemma mik2_fourier_smul (c : ℂ) (u : 𝓢(𝔼, ℂ)) (ξ : 𝔼) : 𝓕 (⇑(c • u)) ξ = c * 𝓕 (⇑u) ξ := by
  have h : (𝓕 (c • u) : 𝓢(𝔼, ℂ)) = c • 𝓕 u := by
    have := (SchwartzMap.fourierTransformCLM ℂ (E := ℂ) (V := 𝔼)).map_smul c u
    simpa only [SchwartzMap.fourierTransformCLM_apply] using this
  rw [← SchwartzMap.fourier_coe, h, SchwartzMap.smul_apply, smul_eq_mul, SchwartzMap.fourier_coe]

lemma mik2_T_add (hd : 1 ≤ d) {A : ℝ} {m : 𝔼 → ℂ} (hm : mik1_IsMikhlin d A m) (u v : 𝓢(𝔼, ℂ)) :
    mik2_T m (u + v) = mik2_T m u + mik2_T m v := by
  funext x
  simp only [Pi.add_apply, mik2_T_apply]
  rw [← integral_add (mik2_exp_integrable (mik2_integrable hd hm u) x)
    (mik2_exp_integrable (mik2_integrable hd hm v) x)]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [mik2_fourier_add, mul_add, smul_add]

lemma mik2_T_smul (hd : 1 ≤ d) {A : ℝ} {m : 𝔼 → ℂ} (hm : mik1_IsMikhlin d A m) (c : ℂ)
    (u : 𝓢(𝔼, ℂ)) : mik2_T m (c • u) = c • mik2_T m u := by
  funext x
  simp only [Pi.smul_apply, mik2_T_apply]
  rw [← integral_smul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [mik2_fourier_smul, smul_eq_mul]
  ring

lemma mik2_T_continuous (hd : 1 ≤ d) {A : ℝ} {m : 𝔼 → ℂ} (hm : mik1_IsMikhlin d A m) (u : 𝓢(𝔼, ℂ)) :
    Continuous (mik2_T m u) := by
  have h : mik2_T m u = fun x => 𝓕 (fun ξ => m ξ * 𝓕 (⇑u) ξ) (-x) := by
    funext x; exact Real.fourierInv_eq_fourier_neg _ _
  rw [h]
  exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by exact continuous_inner) (mik2_integrable hd hm u)).comp continuous_neg

lemma mik2_T_bdd (hd : 1 ≤ d) {A : ℝ} {m : 𝔼 → ℂ} (hm : mik1_IsMikhlin d A m) (u : 𝓢(𝔼, ℂ)) :
    ∃ L : ℝ, ∀ x, ‖mik2_T m u x‖ ≤ L := by
  refine ⟨∫ ξ, ‖m ξ * 𝓕 (⇑u) ξ‖, fun x => ?_⟩
  rw [mik2_T_apply]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-! ### `L^p` norm of `mik2_T m u` -/

lemma mik2_eLpNorm_eq {p : ℝ} (hp : 0 < p) {f : 𝔼 → ℂ} (hf : AEStronglyMeasurable f volume) :
    eLpNorm f (ENNReal.ofReal p) volume = (∫⁻ x, ‖f x‖ₑ ^ p) ^ (1 / p) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le]

lemma mik2_eLpNorm_T_le (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (A : ℝ) (m : 𝔼 → ℂ), 0 ≤ A → mik1_IsMikhlin d A m →
      ∀ u : 𝓢(𝔼, ℂ), eLpNorm (mik2_T m u) (ENNReal.ofReal p) volume ≤
        C * ENNReal.ofReal A * eLpNorm (⇑u) (ENNReal.ofReal p) volume := by
  obtain ⟨C0, hC0, hmain⟩ := mikhlin_Lp_schwartz hd hp
  have hp0 : 0 < p := by linarith
  have hinv : 0 ≤ 1 / p := by positivity
  refine ⟨C0 ^ (1 / p), ENNReal.rpow_ne_top_of_nonneg hinv hC0, ?_⟩
  intro A m hA hm u
  rw [mik2_eLpNorm_eq hp0 (mik2_T_continuous hd hm u).aestronglyMeasurable,
    mik2_eLpNorm_eq hp0 u.continuous.aestronglyMeasurable]
  calc (∫⁻ x, ‖mik2_T m u x‖ₑ ^ p) ^ (1 / p)
      ≤ (C0 * ENNReal.ofReal A ^ p * ∫⁻ x, ‖u x‖ₑ ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (hmain A m hA hm u) hinv
    _ = C0 ^ (1 / p) * ENNReal.ofReal A * (∫⁻ x, ‖u x‖ₑ ^ p) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hinv, ENNReal.mul_rpow_of_nonneg _ _ hinv,
          ← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

lemma mik2_memLp (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) {A : ℝ} {m : 𝔼 → ℂ} (hA : 0 ≤ A)
    (hm : mik1_IsMikhlin d A m) (u : 𝓢(𝔼, ℂ)) :
    MemLp (mik2_T m u) (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hb⟩ := mik2_eLpNorm_T_le hd hp
  exact
    (hb A m hA hm u).trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top hC.lt_top ENNReal.ofReal_lt_top)
      (u.memLp (ENNReal.ofReal p) volume).eLpNorm_lt_top)

/-! ### The `L^p` extension -/

/-- **`mikhlin_Lp_extend`** (MIK-2, `L^p` extension of the Mikhlin theorem): for `d ≥ 1`, `1 < p` there is
`C ≥ 0` (depending on `d, p` only) such that for every Mikhlin symbol `m` of constant `A ≥ 0` there is a
continuous linear map `T : L^p → L^p` with `‖T‖ ≤ C A` and `T [u] = [mik2_T m u]` a.e. for every Schwartz
`u` (where `[u]` is the class of `u` in `L^p`, `SchwartzMap.toLp`). -/
theorem mikhlin_Lp_extend (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ) (m : 𝔼 → ℂ), 0 ≤ A → mik1_IsMikhlin d A m →
      ∃ T : Lp ℂ (ENNReal.ofReal p) (volume : Measure 𝔼) →L[ℂ]
          Lp ℂ (ENNReal.ofReal p) (volume : Measure 𝔼),
        ‖T‖ ≤ C * A ∧
        ∀ u : 𝓢(𝔼, ℂ), T (u.toLp (ENNReal.ofReal p) volume) =ᵐ[volume] mik2_T m u := by
  obtain ⟨C0, hC0, hb⟩ := mik2_eLpNorm_T_le hd hp
  refine ⟨C0.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro A m hA hm
  let f : 𝓢(𝔼, ℂ) →ₗ[ℂ] Lp ℂ (ENNReal.ofReal p) (volume : Measure 𝔼) :=
    { toFun := fun u => (mik2_memLp hd hp hA hm u).toLp (mik2_T m u)
      map_add' := fun u v => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => congrFun (mik2_T_add hd hm u v) x)
      map_smul' := fun c u => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul c (mik2_memLp hd hp hA hm u)]
        exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => congrFun (mik2_T_smul hd hm c u) x) }
  let e : 𝓢(𝔼, ℂ) →ₗ[ℂ] Lp ℂ (ENNReal.ofReal p) (volume : Measure 𝔼) :=
    (SchwartzMap.toLpCLM ℂ ℂ (ENNReal.ofReal p) volume).toLinearMap
  have hdense : DenseRange e :=
    SchwartzMap.denseRange_toLpCLM (E := 𝔼) (F := ℂ) (p := ENNReal.ofReal p) ENNReal.ofReal_ne_top
  have hnorm : ∀ u : 𝓢(𝔼, ℂ), ‖f u‖ ≤ (C0.toReal * A) * ‖e u‖ := by
    intro u
    have h1 : ‖f u‖ = (eLpNorm (mik2_T m u) (ENNReal.ofReal p) volume).toReal :=
      Lp.norm_toLp (mik2_T m u) (mik2_memLp hd hp hA hm u)
    have h2 : ‖e u‖ = (eLpNorm (⇑u) (ENNReal.ofReal p) volume).toReal := SchwartzMap.norm_toLp
    rw [h1, h2]
    have hfin : C0 * ENNReal.ofReal A * eLpNorm (⇑u) (ENNReal.ofReal p) volume ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top hC0 ENNReal.ofReal_ne_top)
        (u.memLp (ENNReal.ofReal p) volume).eLpNorm_ne_top
    have h3 := ENNReal.toReal_mono hfin (hb A m hA hm u)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hA] at h3
  refine ⟨f.extendOfNorm e, ?_, ?_⟩
  · exact LinearMap.opNorm_extendOfNorm_le hdense (mul_nonneg ENNReal.toReal_nonneg hA) hnorm
  · intro u
    have h := LinearMap.extendOfNorm_eq hdense ⟨_, hnorm⟩ u
    have e1 : u.toLp (ENNReal.ofReal p) volume = e u := rfl
    rw [e1, h]
    exact MemLp.coeFn_toLp (mik2_memLp hd hp hA hm u)

/-- the extension is unique: continuous linear maps `L^p → L^p` agreeing on Schwartz functions are equal -/
lemma mikhlin_Lp_extend_unique {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    {T T' : Lp ℂ (ENNReal.ofReal p) (volume : Measure 𝔼) →L[ℂ] Lp ℂ (ENNReal.ofReal p) (volume : Measure 𝔼)}
    (h : ∀ u : 𝓢(𝔼, ℂ), T (u.toLp (ENNReal.ofReal p) volume) = T' (u.toLp (ENNReal.ofReal p) volume)) :
    T = T' := by
  have hdense : DenseRange (SchwartzMap.toLpCLM ℂ ℂ (ENNReal.ofReal p) (volume : Measure 𝔼)) :=
    SchwartzMap.denseRange_toLpCLM (E := 𝔼) (F := ℂ) (p := ENNReal.ofReal p) ENNReal.ofReal_ne_top
  ext1 f
  exact hdense.induction_on f (isClosed_eq T.continuous T'.continuous) (fun u => h u)

/-! ### Convolution with `L^1` kernels -/

lemma mik2_exists_rep {K : 𝔼 → ℂ} (hK : Integrable K) :
    ∃ K₀ : 𝔼 → ℂ, Measurable K₀ ∧ Integrable K₀ ∧ ∫⁻ z, ‖K₀ z‖ₑ = ∫⁻ z, ‖K z‖ₑ ∧
      ∀ g, cv K g = cv K₀ g := by
  refine ⟨hK.1.mk K, hK.1.stronglyMeasurable_mk.measurable, hK.congr hK.1.ae_eq_mk, ?_, fun g => ?_⟩
  · refine lintegral_congr_ae ?_
    filter_upwards [hK.1.ae_eq_mk] with y hy
    rw [hy]
  · funext x
    simp only [cv_apply]
    refine integral_congr_ae ?_
    filter_upwards [hK.1.ae_eq_mk] with y hy
    rw [hy]

/-- Young's inequality in `eLpNorm` form: `‖K ⋆ g‖_p ≤ ‖K‖₁ ‖g‖_p` for `K ∈ L^1` and measurable `g` -/
lemma mik2_eLpNorm_cv_le {K g : 𝔼 → ℂ} (hK : Integrable K) (hg : Measurable g) {p : ℝ} (hp : 1 < p) :
    eLpNorm (cv K g) (ENNReal.ofReal p) volume ≤
      (∫⁻ z, ‖K z‖ₑ) * eLpNorm g (ENNReal.ofReal p) volume := by
  obtain ⟨K₀, hK₀m, -, hn, hc⟩ := mik2_exists_rep hK
  have hp0 : 0 < p := by linarith
  rw [hc g, ← hn]
  have haes : AEStronglyMeasurable (cv K₀ g) volume :=
    AEStronglyMeasurable.convolution (L := ContinuousLinearMap.mul ℂ ℂ) hK₀m.aestronglyMeasurable
      hg.aestronglyMeasurable
  rw [mik2_eLpNorm_eq hp0 haes, mik2_eLpNorm_eq hp0 hg.aestronglyMeasurable]
  calc (∫⁻ x, ‖cv K₀ g x‖ₑ ^ p) ^ (1 / p)
      ≤ (((∫⁻ z, ‖K₀ z‖ₑ) ^ p) * ∫⁻ x, ‖g x‖ₑ ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (mik2_young hK₀m hg hp.le) (by positivity)
    _ = (∫⁻ z, ‖K₀ z‖ₑ) * (∫⁻ x, ‖g x‖ₑ ^ p) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

lemma mik2_memLp_cv {K g : 𝔼 → ℂ} (hK : Integrable K) (hg : Measurable g) {p : ℝ} (hp : 1 < p)
    (hgL : MemLp g (ENNReal.ofReal p) volume) : MemLp (cv K g) (ENNReal.ofReal p) volume :=
  (mik2_eLpNorm_cv_le hK hg hp).trans_lt (ENNReal.mul_lt_top hK.hasFiniteIntegral hgL)

/-- `k ⋆ u ∈ L^p` for `k ∈ L^1` and Schwartz `u` (so the hypothesis `hku` of `mikhlin_comm_conv` is
automatic) -/
lemma mik2_memLp_cv_schwartz {k : 𝔼 → ℂ} (hk : Integrable k) {p : ℝ} (hp : 1 < p) (u : 𝓢(𝔼, ℂ)) :
    MemLp (cv k u) (ENNReal.ofReal p) volume :=
  mik2_memLp_cv hk u.continuous.measurable hp (u.memLp _ _)

lemma mik2_approx_L1 {k : 𝔼 → ℂ} (hk : Integrable k) :
    ∃ κ : ℕ → 𝓢(𝔼, ℂ), ∀ j : ℕ, ∫⁻ y, ‖k y - κ j y‖ₑ ≤ ENNReal.ofReal (1 / ((j : ℝ) + 1)) := by
  have h : ∀ j : ℕ, ∃ s : 𝓢(𝔼, ℂ), ∫⁻ y, ‖k y - s y‖ₑ ≤ ENNReal.ofReal (1 / ((j : ℝ) + 1)) := by
    intro j
    obtain ⟨g, hgc, hgs, hg⟩ := (memLp_one_iff_integrable.2 hk).exist_eLpNorm_sub_le
      ENNReal.one_ne_top le_rfl (ε := 1 / ((j : ℝ) + 1)) (by positivity)
    refine ⟨hgc.toSchwartzMap hgs, ?_⟩
    rw [eLpNorm_one_eq_lintegral_enorm (hk.1.sub hgs.continuous.aestronglyMeasurable)] at hg
    exact hg
  choose s hs using h
  exact ⟨s, hs⟩

/-- the multiplication formula: `k ⋆ 𝓕⁻G = 𝓕⁻(𝓕k · G)` for `k, G ∈ L^1` -/
lemma mik2_cv_fourierInv {k G : 𝔼 → ℂ} (hk : Integrable k) (hG : Integrable G) (x : 𝔼) :
    cv k (𝓕⁻ G) x = 𝓕⁻ (fun ξ => 𝓕 k ξ * G ξ) x := by
  set g : 𝔼 → ℂ := fun ξ => Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I) * G ξ
    with hgdef
  have hg : Integrable g := by simpa only [smul_eq_mul] using mik2_exp_integrable hG x
  have key := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := Real.fourierChar)
    (μ := (volume : Measure 𝔼)) (ν := (volume : Measure 𝔼)) (L := innerₗ 𝔼)
    Real.continuous_fourierChar (by exact continuous_inner) hk hg
  have hL : ∀ ξ, VectorFourier.fourierIntegral 𝐞 volume (innerₗ 𝔼) k ξ = 𝓕 k ξ := fun ξ => by
    rw [Real.fourier_eq]; rfl
  have hR : ∀ y, VectorFourier.fourierIntegral 𝐞 volume (innerₗ 𝔼).flip g y = 𝓕⁻ G (x - y) := by
    intro y
    rw [Real.fourierInv_eq']
    unfold VectorFourier.fourierIntegral
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [LinearMap.flip_apply, innerₗ_apply_apply, hgdef, smul_eq_mul,
      inner_sub_right, real_inner_comm ξ y]
    rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
    congr 3
    push_cast
    ring
  simp only [hL] at key
  simp only [hR] at key
  rw [cv_apply, Real.fourierInv_eq']
  simp only [smul_eq_mul] at key ⊢
  rw [← key]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [hgdef]
  ring

/-- the convolution of two Schwartz functions is the Fourier multiplier `𝓕⁻(𝓕κ 𝓕u)` -/
lemma mik2_cv_eq_mulS (κ u : 𝓢(𝔼, ℂ)) :
    cv ⇑κ ⇑u = ⇑(mulS (⇑(𝓕 κ : 𝓢(𝔼, ℂ))) (𝓕 κ : 𝓢(𝔼, ℂ)).hasTemperateGrowth u) := by
  funext x
  rw [mulS_apply]
  set C := cv ⇑κ ⇑u with hC
  have hCi : Integrable C :=
    Integrable.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) κ.integrable u.integrable
  have hF : 𝓕 C = fun ξ => (𝓕 κ : 𝓢(𝔼, ℂ)) ξ * 𝓕 (⇑u) ξ := by
    funext ξ
    have := Real.fourier_mul_convolution_eq κ.integrable u.integrable ξ
    rw [hC]
    show 𝓕 (⇑κ ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] ⇑u) ξ = _
    rw [this, SchwartzMap.fourier_coe]
  have hFint : Integrable (𝓕 C) := by
    rw [hF]
    obtain ⟨B, -, hB⟩ := (𝓕 κ : 𝓢(𝔼, ℂ)).decay 0 0
    exact (mik2_fourier_integrable u).bdd_mul (c := B) ((𝓕 κ : 𝓢(𝔼, ℂ)).continuous.aestronglyMeasurable)
      (Eventually.of_forall fun ξ => by simpa using hB ξ)
  have hcont : Continuous C := by
    refine BddAbove.continuous_convolution_right_of_integrable (ContinuousLinearMap.mul ℂ ℂ) ?_
      κ.integrable u.continuous
    obtain ⟨B, -, hB⟩ := u.decay 0 0
    exact ⟨B, by rintro _ ⟨y, rfl⟩; simpa using hB y⟩
  have := Integrable.fourierInv_fourier_eq hCi hFint hcont.continuousAt (v := x)
  rw [hF] at this
  exact this.symm

lemma mik2_T_mulS (hd : 1 ≤ d) {A : ℝ} {m : 𝔼 → ℂ} (hm : mik1_IsMikhlin d A m) (κ u : 𝓢(𝔼, ℂ)) :
    mik2_T m (mulS (⇑(𝓕 κ : 𝓢(𝔼, ℂ))) (𝓕 κ : 𝓢(𝔼, ℂ)).hasTemperateGrowth u) = cv ⇑κ (mik2_T m u) := by
  funext x
  have h1 : mik2_T m u = 𝓕⁻ (fun ξ => m ξ * 𝓕 (⇑u) ξ) := rfl
  rw [h1, mik2_cv_fourierInv κ.integrable (mik2_integrable hd hm u) x]
  unfold mik2_T
  have e : (fun ξ => m ξ * 𝓕 (⇑(mulS (⇑(𝓕 κ : 𝓢(𝔼, ℂ))) (𝓕 κ : 𝓢(𝔼, ℂ)).hasTemperateGrowth u)) ξ) =
      fun ξ => 𝓕 (⇑κ) ξ * (m ξ * 𝓕 (⇑u) ξ) := by
    funext ξ
    rw [fourier_mulS, SchwartzMap.fourier_coe]
    ring
  rw [e]

/-- generic `L^p` convergence of convolutions with an `L^1`-convergent family of kernels -/
lemma mik2_tendsto_cv {p : ℝ} (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)] {k : 𝔼 → ℂ}
    (hk : Integrable k) {κ : ℕ → 𝔼 → ℂ} (hκ : ∀ j, Integrable (κ j))
    (hκ0 : Tendsto (fun j => ∫⁻ y, ‖k y - κ j y‖ₑ) atTop (𝓝 0)) {h : 𝔼 → ℂ}
    (hh : Measurable h) {L : ℝ} (hb : ∀ x, ‖h x‖ ≤ L) (hL : MemLp h (ENNReal.ofReal p) volume)
    (hmem : ∀ j, MemLp (cv (κ j) h) (ENNReal.ofReal p) volume)
    (hmemk : MemLp (cv k h) (ENNReal.ofReal p) volume) :
    Tendsto (fun j => (hmem j).toLp (cv (κ j) h)) atTop (𝓝 (hmemk.toLp (cv k h))) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hfin : ∀ j, (∫⁻ y, ‖k y - κ j y‖ₑ) ≠ ⊤ := fun j =>
    (hk.sub (hκ j)).hasFiniteIntegral.ne
  have hbound : ∀ j, dist ((hmem j).toLp (cv (κ j) h)) (hmemk.toLp (cv k h)) ≤
      (∫⁻ y, ‖k y - κ j y‖ₑ).toReal * (eLpNorm h (ENNReal.ofReal p) volume).toReal := by
    intro j
    rw [dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp]
    have hsub : (cv (κ j) h - cv k h) = cv (fun y => κ j y - k y) h := by
      funext x
      rw [xbb_cv_sub (hκ j) hk hh.aestronglyMeasurable hb x]
      rfl
    rw [hsub, ← ENNReal.toReal_mul]
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top (hfin j) hL.eLpNorm_ne_top) ?_
    refine (mik2_eLpNorm_cv_le ((hκ j).sub hk) hh hp).trans ?_
    refine le_of_eq ?_
    congr 1
    refine lintegral_congr fun y => ?_
    exact enorm_sub_rev _ _
  refine squeeze_zero (fun j => dist_nonneg) hbound ?_
  have h0 : Tendsto (fun j => (∫⁻ y, ‖k y - κ j y‖ₑ).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hκ0
    rwa [ENNReal.toReal_zero] at this
  simpa using h0.mul_const (eLpNorm h (ENNReal.ofReal p) volume).toReal

/-- **`mikhlin_comm_conv`** (MIK-2, commutation of the Mikhlin multiplier with `L^1` convolutions): let
`T : L^p → L^p` be continuous linear with `T [u] = [mik2_T m u]` for every Schwartz `u` (e.g. the extension
of `mikhlin_Lp_extend`; by `mikhlin_Lp_extend_unique` it is determined by this property).  Then for every
`k ∈ L^1` and Schwartz `u` (with `k ⋆ u ∈ L^p`, automatic by `mik2_memLp_cv_schwartz`),
`T [k ⋆ u] = k ⋆ (mik2_T m u)` almost everywhere.  Here `k ⋆ g = cv k g`. -/
theorem mikhlin_comm_conv (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)]
    {A : ℝ} {m : 𝔼 → ℂ} (hA : 0 ≤ A) (hm : mik1_IsMikhlin d A m)
    (T : Lp ℂ (ENNReal.ofReal p) (volume : Measure 𝔼) →L[ℂ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure 𝔼))
    (hT : ∀ u : 𝓢(𝔼, ℂ), T (u.toLp (ENNReal.ofReal p) volume) =ᵐ[volume] mik2_T m u)
    {k : 𝔼 → ℂ} (hk : Integrable k) (u : 𝓢(𝔼, ℂ))
    (hku : MemLp (cv k u) (ENNReal.ofReal p) volume) :
    T (hku.toLp (cv k u)) =ᵐ[volume] cv k (mik2_T m u) := by
  obtain ⟨κ, hκ⟩ := mik2_approx_L1 hk
  set P := ENNReal.ofReal p with hP
  set g := mik2_T m u with hg
  have hgc : Continuous g := mik2_T_continuous hd hm u
  obtain ⟨Lg, hLg⟩ := mik2_T_bdd hd hm u
  obtain ⟨Lu, hLu⟩ := mik2_schwartz_bdd u
  have hgL : MemLp g P volume := mik2_memLp hd hp hA hm u
  have hκi : ∀ j, Integrable (⇑(κ j)) := fun j => (κ j).integrable
  have hκ0 : Tendsto (fun j : ℕ => ∫⁻ y, ‖k y - κ j y‖ₑ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le) hκ
    have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using this
  have hmemu : ∀ j, MemLp (cv (⇑(κ j)) ⇑u) P volume := fun j =>
    mik2_memLp_cv_schwartz (hκi j) hp u
  have hmemg : ∀ j, MemLp (cv (⇑(κ j)) g) P volume := fun j =>
    mik2_memLp_cv (hκi j) hgc.measurable hp hgL
  have hmemgk : MemLp (cv k g) P volume := mik2_memLp_cv hk hgc.measurable hp hgL
  have t1 := mik2_tendsto_cv hp hk hκi hκ0 u.continuous.measurable hLu (u.memLp P volume) hmemu hku
  have t2 := mik2_tendsto_cv hp hk hκi hκ0 hgc.measurable hLg hgL hmemg hmemgk
  have hid : ∀ j, T ((hmemu j).toLp (cv (⇑(κ j)) ⇑u)) = (hmemg j).toLp (cv (⇑(κ j)) g) := by
    intro j
    set S := mulS (⇑(𝓕 (κ j) : 𝓢(𝔼, ℂ))) (𝓕 (κ j) : 𝓢(𝔼, ℂ)).hasTemperateGrowth u with hS
    have hcvS : cv ⇑(κ j) ⇑u = ⇑S := mik2_cv_eq_mulS (κ j) u
    have e1 : (hmemu j).toLp (cv (⇑(κ j)) ⇑u) = S.toLp P volume := by
      refine Lp.ext ?_
      filter_upwards [(hmemu j).coeFn_toLp, S.coeFn_toLp P volume] with x h1 h2
      rw [h1, h2, hcvS]
    rw [e1]
    refine Lp.ext ?_
    filter_upwards [hT S, (hmemg j).coeFn_toLp] with x h1 h2
    rw [h1, h2]
    exact congrFun (mik2_T_mulS hd hm (κ j) u) x
  have t3 : Tendsto (fun j => (hmemg j).toLp (cv (⇑(κ j)) g)) atTop
      (𝓝 (T (hku.toLp (cv k u)))) := by
    have := (T.continuous.tendsto _).comp t1
    exact this.congr (fun j => hid j)
  have hunique := tendsto_nhds_unique t3 t2
  rw [hunique]
  exact hmemgk.coeFn_toLp

/-- the three statements together (consumer form): the `L^p` extension of `T_m` commutes with convolution
against every `k ∈ L^1` on Schwartz data -/
theorem mikhlin_Lp_extend_comm (hd : 1 ≤ d) {p : ℝ} (hp : 1 < p) [Fact (1 ≤ ENNReal.ofReal p)] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ) (m : 𝔼 → ℂ), 0 ≤ A → mik1_IsMikhlin d A m →
      ∃ T : Lp ℂ (ENNReal.ofReal p) (volume : Measure 𝔼) →L[ℂ]
          Lp ℂ (ENNReal.ofReal p) (volume : Measure 𝔼),
        ‖T‖ ≤ C * A ∧
        (∀ u : 𝓢(𝔼, ℂ), T (u.toLp (ENNReal.ofReal p) volume) =ᵐ[volume] mik2_T m u) ∧
        ∀ (k : 𝔼 → ℂ) (hk : Integrable k) (u : 𝓢(𝔼, ℂ)),
          T ((mik2_memLp_cv_schwartz hk hp u).toLp (cv k u)) =ᵐ[volume] cv k (mik2_T m u) := by
  obtain ⟨C, hC, hmain⟩ := mikhlin_Lp_extend hd hp
  refine ⟨C, hC, fun A m hA hm => ?_⟩
  obtain ⟨T, hTn, hT⟩ := hmain A m hA hm
  exact ⟨T, hTn, hT, fun k hk u => mikhlin_comm_conv hd hp hA hm T hT hk u _⟩

end HRS.CZ.Mik
