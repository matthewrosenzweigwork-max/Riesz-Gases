import HRS.MS.S111TermAux7
import HRS.MS.ProClosureS111InitialTestsApprox
import HRS.MS.R26T6CD03

/-!
# The physical Gaussian feature endpoint on every oscillator test

The accepted G01 construction records only Hermite-coordinate laws. This
module retains its common Gaussian series and continuous modification, but
uses the accepted vector-series law before restricting its functionals.
The resulting finite-dimensional law holds for arbitrary continuous linear
observations. A bounded linear physical feature map is then identified on
all oscillator tests by convergent Hermite sections.

The Hilbert feature data are explicit inputs here. The physical construction
must supply them before this module yields SharedThermalLaw.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.S111T HRS.MS.S111X1
open HRS.MS.R26T6

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- G01 with every continuous linear observation retained. The stochastic
series and Kolmogorov construction are the accepted producers. -/
theorem gaussian_paths_full_linear_law (d : ℕ) (m H : ℝ) (hH : 0 < H)
    (e : HilbertBasis ℕ ℝ E) (F : Fin 2 → ℝ → MultiIndex d → E)
    (hF : ∀ i, ∀ t ∈ Set.Icc 0 H, Summable (fun α => ‖F i t α‖ ^ 2))
    (L : ℝ) (hL : 0 ≤ L)
    (hinc : ∀ i, ∀ t v : ℝ, t ∈ Set.Icc 0 H → v ∈ Set.Icc 0 H →
      Summable (fun α => ‖F i t α - F i v α‖ ^ 2) ∧
        (∑' α, ‖F i t α - F i v α‖ ^ 2) ≤ L * |t - v|) :
    ∃ P : Measure (PathPair d m H), IsProbabilityMeasure P ∧
      ∀ n : ℕ, ∀ side : Fin n → Fin 2, ∀ ts : Fin n → ℝ,
      ∀ ell : Fin n → OscDual d m →L[ℝ] ℝ, (∀ j, ts j ∈ Set.Icc 0 H) →
        P.map (fun w => (WithLp.toLp 2 fun j =>
          ell j (pairedProcess d m H hH.le (side j) (ts j) w) :
            EuclideanSpace ℝ (Fin n))) =
          multivariateGaussian 0 (Matrix.of fun j k =>
            ∑' l, ell j (s111t_vec m e (F (side j) (ts j)) l) *
              ell k (s111t_vec m e (F (side k) (ts k)) l)) := by
  set Fc : Fin 2 → ℝ → MultiIndex d → E := fun i t => F i (max 0 (min t H)) with hFc_def
  have hFc : ∀ i t, Summable fun α => ‖Fc i t α‖ ^ 2 := fun i t => hF i _ (s111t_clip_mem hH.le t)
  have hincc : ∀ i t v, Summable (fun α => ‖Fc i t α - Fc i v α‖ ^ 2) ∧
      (∑' α, ‖Fc i t α - Fc i v α‖ ^ 2) ≤ L * |t - v| := by
    intro i t v
    obtain ⟨h1, h2⟩ := hinc i _ _ (s111t_clip_mem hH.le t) (s111t_clip_mem hH.le v)
    exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_left (s111t_clip_lip H t v) hL)⟩
  obtain ⟨Ω, mΩ, P0, hP0, g, X, hg, hind, hXm, hXg, hmom⟩ := s111t_family m e Fc hFc L hL hincc
  obtain ⟨r, q, hr0, hr1, hq0, hq1, hqr⟩ := HRS.MP.KC.mkc_consts (β := 1) (p := 4) one_pos (by norm_num)
  have hmom' : ∀ i, ∀ s ∈ Set.Icc (0 : ℝ) H, ∀ t ∈ Set.Icc (0 : ℝ) H,
      ∫⁻ ζ, ‖X i t ζ - X i s ζ‖ₑ ^ (4 : ℝ) ∂P0 ≤ ENNReal.ofReal (3 * L ^ 2 * |t - s| ^ ((1 : ℝ) + 1)) :=
    fun i s _ t _ => hmom i s t
  set Z : Fin 2 → ℝ → Ω → OscDual d m := fun i => HRS.MP.KC.mkc_Zc (X i) H r with hZ
  have hZc : ∀ i ω, Continuous fun t : Set.Icc (0 : ℝ) H => Z i t ω := fun i ω =>
    HRS.MP.KC.mkc_continuous (X i) H r hH hr0.le hr1 ω
  have hZm : ∀ i t, Measurable (Z i t) := fun i t =>
    HRS.MP.KC.mkc_Zc_meas (X i) H r hH hr0.le hr1 (hXm i) t
  have hZae : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) H, Z i t =ᵐ[P0] X i t := fun i t ht =>
    HRS.MP.KC.mkc_Zc_ae_eq (X i) H r P0 (hXm i) hH (p := 4) (β := 1) (C := 3 * L ^ 2) (q := q)
      (by norm_num) one_pos (hmom' i) hr0 hr1 hq0 hq1 hqr ht
  set path : Fin 2 → Ω → OscPath d m H := fun i ω =>
    (HRS.Whole.AppendixALemmas.contPathOf H (fun t => Z i t ω) : C(Set.Icc (0 : ℝ) H, OscDual d m)) with hpath
  have hpath_at : ∀ i ω (s : Set.Icc (0 : ℝ) H), OscPath.at' (path i ω) s = Z i s ω := fun i ω s =>
    HRS.MP.KC.mkc_contPathOf_apply (X i) hH hr0.le hr1 ω s
  have hpath_meas : ∀ i, Measurable (path i) := by
    intro i
    refine ContinuousMap.measurable_iff_eval.2 fun s => ?_
    have : (fun ω => (show C(Set.Icc (0 : ℝ) H, OscDual d m) from path i ω) s) = fun ω => Z i s ω := by
      funext ω; exact hpath_at i ω s
    rw [this]
    exact hZm i s
  set Φ : Ω → PathPair d m H := fun ω => (path 0 ω, path 1 ω) with hΦ
  have hΦm : Measurable Φ := (hpath_meas 0).prodMk (hpath_meas 1)
  refine ⟨P0.map Φ, inferInstance, ?_⟩
  intro n side ts ell hts
  set Ψ : PathPair d m H → EuclideanSpace ℝ (Fin n) := fun w =>
    WithLp.toLp 2 fun j => ell j (pairedProcess d m H hH.le (side j) (ts j) w) with hΨ
  have hevm : ∀ (i : Fin 2) (τ : Set.Icc (0 : ℝ) H),
      Measurable fun w : PathPair d m H => OscPath.at' (if i = 0 then w.1 else w.2) τ := by
    intro i τ
    have h1 : Measurable fun w : C(Set.Icc (0 : ℝ) H, OscDual d m) => w τ :=
      ContinuousMap.measurable_eval τ
    have h2 : Measurable fun w : PathPair d m H => (if i = 0 then w.1 else w.2) := by
      by_cases hi : i = 0
      · simpa [hi] using measurable_fst
      · simpa [hi] using measurable_snd
    exact h1.comp h2
  have hΨm : Measurable Ψ := by
    refine (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp (measurable_pi_iff.2 fun j => ?_)
    exact (ell j).continuous.measurable.comp (hevm (side j) _)
  rw [Measure.map_map hΨm hΦm]
  have hpt : ∀ ω, (Ψ ∘ Φ) ω = WithLp.toLp 2 fun j => ell j (Z (side j) (ts j) ω) := by
    intro ω
    simp only [Function.comp, hΨ]
    congr 1; funext j
    congr 1
    have hc : clippedTime H hH.le (ts j) = ⟨ts j, hts j⟩ := Subtype.ext (s111t_clip_of_mem (hts j))
    have hif : (if side j = 0 then (Φ ω).1 else (Φ ω).2) = path (side j) ω := by
      generalize side j = i
      fin_cases i <;> simp [hΦ]
    simp only [pairedProcess, hc, hif]
    exact hpath_at (side j) ω ⟨ts j, hts j⟩
  have hae : (Ψ ∘ Φ) =ᵐ[P0] fun ω => (WithLp.toLp 2 fun j => ell j (X (side j) (ts j) ω) :
      EuclideanSpace ℝ (Fin n)) := by
    have hall : ∀ᵐ ω ∂P0, ∀ j, Z (side j) (ts j) ω = X (side j) (ts j) ω :=
      ae_all_iff.2 fun j => hZae (side j) (ts j) (hts j)
    filter_upwards [hall] with ω hω
    rw [hpt]
    congr 1; funext j
    rw [hω j]
  rw [Measure.map_congr hae]
  have hFcF : ∀ j, Fc (side j) (ts j) = F (side j) (ts j) := fun j => by
    funext α
    simp only [hFc_def, s111t_clip_of_mem (hts j)]
  have hlaw := s111t_vector_law (P := P0) (ι := Fin n) hg hind
    (fun j => X (side j) (ts j)) (fun j k => s111t_vec m e (Fc (side j) (ts j)) k)
    (fun j => hXg (side j) (ts j))
    (fun j => (s111t_vec_norm_sq_summable e (Fc (side j) (ts j)) (hFc _ _)).1)
    ell
  simpa only [hFcF] using hlaw

variable {d : ℕ} {m : ℝ}

/-- The original oscillator evaluation as a continuous linear map. -/
def gaussianOscEval (phi : oscSub d m) : OscDual d m →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ (OscSpace.ofFun m (phi : Euc d → ℝ))).comp
    (OscDual.toDual (d := d) (m := m)).toContinuousLinearEquiv.toContinuousLinearMap

theorem gaussianOscEval_apply (phi : oscSub d m) (z : OscDual d m) :
    gaussianOscEval phi z = OscDual.eval z (phi : Euc d → ℝ) := by
  unfold gaussianOscEval
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.apply_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe]
  exact OscDual.toDual_ofFun z _ phi.property.2

/-- Oscillator continuity of the actual linear feature map suffices for the
Hermite extension; no probabilistic null set over all tests is used. -/
theorem linear_feature_section_tendsto (G : oscSub d m →ₗ[ℝ] E)
    (hG : ∃ B : ℝ, 0 ≤ B ∧ ∀ phi : oscSub d m,
      ‖G phi‖ ≤ B * oscNorm m (phi : Euc d → ℝ)) (phi : oscSub d m) :
    Tendsto (fun n => G (initialTestSection phi n)) atTop (𝓝 (G phi)) := by
  obtain ⟨B, hB, hbound⟩ := hG
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hlim : Tendsto (fun n => B * oscNorm m
      ((phi - initialTestSection phi n : oscSub d m) : Euc d → ℝ))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (initialTestSection_tail phi).const_mul B
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
  rw [norm_sub_rev, ← map_sub]
  exact hbound (phi - initialTestSection phi n)

/-- The Fourier vector's evaluation is the corresponding physical feature
coordinate on every oscillator test. -/
theorem eval_linear_feature_vector (e : HilbertBasis ℕ ℝ E)
    (G : oscSub d m →ₗ[ℝ] E)
    (hG : ∃ B : ℝ, 0 ≤ B ∧ ∀ phi : oscSub d m,
      ‖G phi‖ ≤ B * oscNorm m (phi : Euc d → ℝ))
    (hs : Summable fun alpha : MultiIndex d =>
      ‖G (initialTestBasis m alpha)‖ ^ 2)
    (phi : oscSub d m) (k : ℕ) :
    OscDual.eval (s111t_vec m e (fun alpha => G (initialTestBasis m alpha)) k)
      (phi : Euc d → ℝ) = inner ℝ (G phi) (e k) := by
  let v := s111t_vec m e (fun alpha => G (initialTestBasis m alpha)) k
  have hsection : ∀ n,
      OscDual.eval v (initialTestSection phi n : Euc d → ℝ) =
        inner ℝ (G (initialTestSection phi n)) (e k) := by
    intro n
    rw [initialTestSection_eval]
    simp only [initialTestSection, map_sum, map_smul, sum_inner, real_inner_smul_left]
    refine Finset.sum_congr rfl fun alpha _ => ?_
    rw [show OscDual.coord v alpha =
      inner ℝ (G (initialTestBasis m alpha)) (e k) from
        s111t_coord_vec e _ hs k alpha]
  have hleft := initialTestSection_eval_tendsto phi v
  have hc : Continuous (fun z : E => inner ℝ z (e k)) := by fun_prop
  have hright := (hc.tendsto (G phi)).comp (linear_feature_section_tendsto G hG phi)
  exact tendsto_nhds_unique (hleft.congr hsection) hright

/-- A continuous Gaussian path pair with the exact mixed Gram law on all
original oscillator tests. The physical map will supply G and its bounds. -/
theorem gaussian_paths_of_linear_features (d : ℕ) (m H : ℝ) (hH : 0 < H)
    (e : HilbertBasis ℕ ℝ E) (G : Fin 2 → ℝ → oscSub d m →ₗ[ℝ] E)
    (hG : ∀ i, ∀ t ∈ Set.Icc 0 H, ∃ B : ℝ, 0 ≤ B ∧
      ∀ phi : oscSub d m, ‖G i t phi‖ ≤ B * oscNorm m (phi : Euc d → ℝ))
    (hF : ∀ i, ∀ t ∈ Set.Icc 0 H, Summable (fun alpha : MultiIndex d =>
      ‖G i t (initialTestBasis m alpha)‖ ^ 2))
    (L : ℝ) (hL : 0 ≤ L)
    (hinc : ∀ i, ∀ t v : ℝ, t ∈ Set.Icc 0 H → v ∈ Set.Icc 0 H →
      Summable (fun alpha : MultiIndex d =>
        ‖G i t (initialTestBasis m alpha) - G i v (initialTestBasis m alpha)‖ ^ 2) ∧
      (∑' alpha : MultiIndex d,
        ‖G i t (initialTestBasis m alpha) - G i v (initialTestBasis m alpha)‖ ^ 2)
          ≤ L * |t - v|) :
    ∃ P : Measure (PathPair d m H), IsProbabilityMeasure P ∧
      ∀ n : ℕ, ∀ side : Fin n → Fin 2, ∀ ts : Fin n → ℝ,
      ∀ phi : Fin n → oscSub d m, (∀ j, ts j ∈ Set.Icc 0 H) →
        P.map (fun w => (WithLp.toLp 2 fun j =>
          OscDual.eval (pairedProcess d m H hH.le (side j) (ts j) w)
            (phi j : Euc d → ℝ) : EuclideanSpace ℝ (Fin n))) =
          multivariateGaussian 0 (Matrix.of fun j k =>
            inner ℝ (G (side j) (ts j) (phi j)) (G (side k) (ts k) (phi k))) := by
  let F : Fin 2 → ℝ → MultiIndex d → E :=
    fun i t alpha => G i t (initialTestBasis m alpha)
  obtain ⟨P, hP, hlaw⟩ :=
    gaussian_paths_full_linear_law d m H hH e F hF L hL hinc
  refine ⟨P, hP, fun n side ts phi hts => ?_⟩
  have h := hlaw n side ts (fun j => gaussianOscEval (phi j)) hts
  have he : ∀ j k,
      gaussianOscEval (phi j) (s111t_vec m e (F (side j) (ts j)) k) =
        inner ℝ (G (side j) (ts j) (phi j)) (e k) := by
    intro j k
    rw [gaussianOscEval_apply]
    exact eval_linear_feature_vector e (G (side j) (ts j))
      (hG (side j) (ts j) (hts j)) (hF (side j) (ts j) (hts j)) (phi j) k
  have hmat : (Matrix.of fun j k => ∑' l,
      gaussianOscEval (phi j) (s111t_vec m e (F (side j) (ts j)) l) *
      gaussianOscEval (phi k) (s111t_vec m e (F (side k) (ts k)) l) :
        Matrix (Fin n) (Fin n) ℝ) =
      Matrix.of fun j k =>
        inner ℝ (G (side j) (ts j) (phi j)) (G (side k) (ts k) (phi k)) := by
    ext j k
    simp only [Matrix.of_apply, he]
    rw [← e.tsum_inner_mul_inner
      (G (side j) (ts j) (phi j)) (G (side k) (ts k) (phi k))]
    refine tsum_congr fun l => ?_
    rw [real_inner_comm (G (side k) (ts k) (phi k)) (e l)]
  rw [hmat] at h
  simpa only [gaussianOscEval_apply] using h

/-- The actual path pair already supplies continuity and measurability; the
feature Gram identity supplies precisely the original shared-law covariance.
All feature assumptions are explicit and are discharged by the physical
feature construction, not by adding a premise to a frozen theorem. -/
theorem shared_thermal_law_of_linear_features (d : ℕ) (s a beta gamma H : ℝ)
    (rho : Euc d → ℝ) (hH : 0 < H) (e : HilbertBasis ℕ ℝ E)
    (G : Fin 2 → ℝ → oscSub d (wholeSpaceIndex d) →ₗ[ℝ] E)
    (hG : ∀ i, ∀ t ∈ Set.Icc 0 H, ∃ B : ℝ, 0 ≤ B ∧
      ∀ phi : oscSub d (wholeSpaceIndex d),
        ‖G i t phi‖ ≤ B * oscNorm (wholeSpaceIndex d) (phi : Euc d → ℝ))
    (hF : ∀ i, ∀ t ∈ Set.Icc 0 H, Summable (fun alpha : MultiIndex d =>
      ‖G i t (initialTestBasis (wholeSpaceIndex d) alpha)‖ ^ 2))
    (L : ℝ) (hL : 0 ≤ L)
    (hinc : ∀ i, ∀ t v : ℝ, t ∈ Set.Icc 0 H → v ∈ Set.Icc 0 H →
      Summable (fun alpha : MultiIndex d =>
        ‖G i t (initialTestBasis (wholeSpaceIndex d) alpha) -
          G i v (initialTestBasis (wholeSpaceIndex d) alpha)‖ ^ 2) ∧
      (∑' alpha : MultiIndex d,
        ‖G i t (initialTestBasis (wholeSpaceIndex d) alpha) -
          G i v (initialTestBasis (wholeSpaceIndex d) alpha)‖ ^ 2) ≤ L * |t - v|)
    (hGram : ∀ i j, ∀ t v : ℝ, t ∈ Set.Icc 0 H → v ∈ Set.Icc 0 H →
      ∀ phi psi : oscSub d (wholeSpaceIndex d),
      inner ℝ (G i t phi) (G j v psi) =
        (if i = j then
          HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal rho)
            (r26t6_preparation beta gamma i)
            (propagatorW (r26t6_thermalCoeff d s a beta rho) 0 t (phi : Euc d → ℝ))
            (propagatorW (r26t6_thermalCoeff d s a beta rho) 0 v (psi : Euc d → ℝ))
        else 0) + noiseCovW (r26t6_thermalCoeff d s a beta rho) beta⁻¹
          t v (phi : Euc d → ℝ) (psi : Euc d → ℝ)) :
    ∃ P : Measure (PathPair d (wholeSpaceIndex d) H), IsProbabilityMeasure P ∧
      r26t6_SharedThermalLaw P s a beta gamma H rho
        (pairedProcess d (wholeSpaceIndex d) H hH.le) := by
  obtain ⟨P, hP, hlaw⟩ :=
    gaussian_paths_of_linear_features d (wholeSpaceIndex d) H hH e G hG hF L hL hinc
  letI := hP
  have hcont : ∀ i w, Continuous
      (fun t => pairedProcess d (wholeSpaceIndex d) H hH.le i t w) := by
    intro i w
    let p : OscPath d (wholeSpaceIndex d) H := if i = 0 then w.1 else w.2
    have hc : Continuous (fun t : ℝ => clippedTime H hH.le t) := by
      unfold clippedTime
      fun_prop
    exact (show C(Set.Icc (0 : ℝ) H, OscDual d (wholeSpaceIndex d)) from p).continuous.comp hc
  have hmeas : ∀ i t, Measurable
      (pairedProcess d (wholeSpaceIndex d) H hH.le i t) := by
    intro i t
    have hp : Measurable (fun w : PathPair d (wholeSpaceIndex d) H =>
        if i = 0 then w.1 else w.2) := by
      by_cases hi : i = 0
      · simpa only [if_pos hi] using measurable_fst
      · simpa only [if_neg hi] using measurable_snd
    exact (ContinuousMap.measurable_eval (clippedTime H hH.le t)).comp hp
  have hjoint : ∀ n : ℕ, ∀ side : Fin n → Fin 2, ∀ ts : Fin n → ℝ,
      ∀ phi : Fin n → Euc d → ℝ,
      (∀ j, ts j ∈ Set.Icc 0 H) →
      (∀ j, IsOscTest (wholeSpaceIndex d) (phi j)) →
      P.map (fun w => (WithLp.toLp 2 fun j =>
        OscDual.eval (pairedProcess d (wholeSpaceIndex d) H hH.le
          (side j) (ts j) w) (phi j) : EuclideanSpace ℝ (Fin n))) =
        multivariateGaussian 0 (Matrix.of fun j k =>
          (if side j = side k then
            HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal rho)
              (r26t6_preparation beta gamma (side j))
              (propagatorW (r26t6_thermalCoeff d s a beta rho) 0 (ts j) (phi j))
              (propagatorW (r26t6_thermalCoeff d s a beta rho) 0 (ts k) (phi k))
          else 0) + noiseCovW (r26t6_thermalCoeff d s a beta rho) beta⁻¹
            (ts j) (ts k) (phi j) (phi k)) := by
    intro n side ts phi hts hphi
    have h := hlaw n side ts (fun j => ⟨phi j, hphi j⟩) hts
    have hmat : (Matrix.of fun j k =>
        inner ℝ (G (side j) (ts j) ⟨phi j, hphi j⟩)
          (G (side k) (ts k) ⟨phi k, hphi k⟩) : Matrix (Fin n) (Fin n) ℝ) =
        Matrix.of fun j k =>
          (if side j = side k then
            HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal rho)
              (r26t6_preparation beta gamma (side j))
              (propagatorW (r26t6_thermalCoeff d s a beta rho) 0 (ts j) (phi j))
              (propagatorW (r26t6_thermalCoeff d s a beta rho) 0 (ts k) (phi k))
          else 0) + noiseCovW (r26t6_thermalCoeff d s a beta rho) beta⁻¹
            (ts j) (ts k) (phi j) (phi k) := by
      ext j k
      exact hGram (side j) (side k) (ts j) (ts k) (hts j) (hts k) _ _
    rw [hmat] at h
    exact h
  refine ⟨P, hP, ⟨fun i => ?_, hjoint⟩⟩
  refine ⟨Filter.Eventually.of_forall (fun w => (hcont i w).continuousOn), hmeas i, ?_⟩
  intro n ts phi hts hphi
  simpa only [HRS.law, if_pos rfl, if_true] using
    hjoint n (fun _ => i) ts phi hts hphi

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.gaussian_paths_full_linear_law
#print axioms HRS.MS.ProClosureS111.gaussian_paths_of_linear_features
#print axioms HRS.MS.ProClosureS111.shared_thermal_law_of_linear_features
