import HRS.MD.EQ29Vocab
import HRS.MD.EQLawFlow
import HRS.MD.Stat
import HRS.Main.EqMargFinal
import HRS.Energy.StaticLimitBasic

/-!
# EQ-INIT assembly (chunk D): `eq_init_assembly_proof`

`equilibrium_initial_law` from `equilibrium_paths_direct` (frozen statement, hypothesis), the existence of a horizon-`0` flow
(`eq_flow_exists_proof`) and `equilibrium_marginal_L2_proof`.  At `T = 0`, `u = 0` the window path is the constant path
`Cst (ζ_N^0)`, the evaluation `ev₀` is a contraction (`smoothDist_map_clm_le`, `wassersteinE_map_clm_le`), and
`η_N^0 = ζ_N^0 + √N(m_N - μ_β)` (`eta_eq_zeta_add`, `meanEmpirical_eq_firstMarginal`) with
`‖√N(m_N - μ_β)‖_{E_m} ≤ K √N δ_N` from the `L²(μ_β)` bound on `dm_N/dμ_β - 1`; translation by `c` costs `‖c‖` in `d_2` and `W_2`.
The tie against `HRS.MD.EQ29.eq_init_assembly` is `HRS/MD/EQAsmInitTie.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace MD

namespace EQAsmInit

open HRS.Main HRS.MD.EQ29

variable {d : ℕ}

/-! ### The path space for `T = 0` -/

/-- The only time of `[0,0]`. -/
def eqiT0 : Set.Icc (0 : ℝ) 0 := ⟨0, le_rfl, le_rfl⟩

theorem eqi_subsingleton (t : Set.Icc (0 : ℝ) 0) : t = eqiT0 :=
  Subtype.ext (le_antisymm t.2.2 t.2.1)

/-- Evaluation at time `0` of a path on `[0,0]`. -/
def eqiEv (m : ℝ) : PathSpace d m 0 →L[ℝ] NegSobolev d m :=
  ContinuousMap.evalCLM ℝ eqiT0

theorem eqiEv_apply (m : ℝ) (w : PathSpace d m 0) : eqiEv m w = PathSpace.at' w eqiT0 := rfl

theorem eqiEv_norm_le (m : ℝ) : ‖(eqiEv m : PathSpace d m 0 →L[ℝ] NegSobolev d m)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
    rw [one_mul]; exact ContinuousMap.norm_coe_le_norm w eqiT0

/-- The constant path. -/
def eqiCst (m : ℝ) : NegSobolev d m →L[ℝ] PathSpace d m 0 :=
  LinearMap.mkContinuous
    { toFun := fun e => (ContinuousMap.const (Set.Icc (0 : ℝ) 0) e : C(Set.Icc (0 : ℝ) 0, NegSobolev d m))
      map_add' := fun a b => ContinuousMap.ext fun t => rfl
      map_smul' := fun c a => ContinuousMap.ext fun t => rfl } 1
    (fun e => by
      rw [one_mul]
      exact (ContinuousMap.norm_le _ (norm_nonneg e)).2 fun t => le_rfl)

theorem eqiEv_cst (m : ℝ) (e : NegSobolev d m) : eqiEv m (eqiCst m e) = e := rfl

open Classical in
theorem eqi_dite (m : ℝ) (f : Set.Icc (0 : ℝ) 0 → NegSobolev d m) :
    (if h : Continuous f then (⟨f, h⟩ : PathSpace d m 0) else 0) = eqiCst m (f eqiT0) := by
  have hf : f = fun _ => f eqiT0 := funext fun t => by rw [eqi_subsingleton t]
  rw [dif_pos (by rw [hf]; exact continuous_const)]
  exact ContinuousMap.ext fun t => by
    show f t = f eqiT0
    rw [eqi_subsingleton t]

theorem eqi_windowPath (m : ℝ) {Ω : Type*} (Z : ℝ → Ω → NegSobolev d m) (ω : Ω) :
    Main.windowPath m 0 0 Z ω = eqiCst m (Z 0 ω) := by
  unfold Main.windowPath HRS.toPath
  refine (eqi_dite m (fun t : Set.Icc (0 : ℝ) 0 => Z (0 + (t : ℝ)) ω)).trans ?_
  simp [eqiT0]
  rfl

theorem eqi_windowZeta (m : ℝ) {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω)
    (X : ℝ≥0 → Ω → Config d N) (ω : Ω) :
    Main.windowZeta m 0 0 P X ω = eqiCst m (zetaE m (P.map (X 0)) (X 0 ω)) := by
  unfold Main.windowZeta
  refine (eqi_dite m (fun t : Set.Icc (0 : ℝ) 0 =>
    zetaE m (P.map (X (Real.toNNReal (0 + (t : ℝ))))) (X (Real.toNNReal (0 + (t : ℝ))) ω))).trans ?_
  simp [eqiT0]
  rfl

/-! ### Translation costs at most `‖c‖` -/

theorem eqi_smooth_translate {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → B) (hX : AEMeasurable X P) (c : B) :
    smoothDist 2 (law P (fun ω => X ω + c)) (law P X) ≤ ‖c‖ := by
  refine Real.iSup_le (fun Φ => ?_) (norm_nonneg c)
  have hΦc : Continuous Φ.1 := Φ.2.1.continuous
  have hΦ1 : Φ.1 ∈ CbUnitBall B 1 := cbUnitBall_anti (by norm_num : 1 ≤ 2) Φ.2
  have hX' : AEMeasurable (fun ω => X ω + c) P := hX.add_const c
  rw [integral_map hX' hΦc.aestronglyMeasurable, integral_map hX hΦc.aestronglyMeasurable]
  have hb : ∀ z, ‖Φ.1 z‖ ≤ 1 := fun z => by simpa using abs_apply_le_of_mem Φ.2 z
  have i1 : Integrable (fun ω => Φ.1 (X ω + c)) P :=
    Integrable.of_bound (hΦc.aestronglyMeasurable.comp_aemeasurable hX') 1
      (Filter.Eventually.of_forall fun ω => hb _)
  have i2 : Integrable (fun ω => Φ.1 (X ω)) P :=
    Integrable.of_bound (hΦc.aestronglyMeasurable.comp_aemeasurable hX) 1
      (Filter.Eventually.of_forall fun ω => hb _)
  rw [← integral_sub i1 i2, ← Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le_const (μ := P) (f := fun ω => Φ.1 (X ω + c) - Φ.1 (X ω)) (C := ‖c‖)
    (Filter.Eventually.of_forall fun ω => by
      have := norm_sub_le_of_mem_one hΦ1 (X ω + c) (X ω)
      simpa using this)
  simpa using this

/-! ### The `E_m` norm of `m_N - μ` from the `L²(μ)` bound on the density -/

/-- the bias bound: `|∫ g dm - ∫ g dμ| ≤ B ‖dm/dμ - 1‖_{L²(μ)}` (as in `HRS.MD.EQTrace.eqtrace_bias_le`). -/
theorem eqi_bias_le {m μ : Measure (Torus d)} [IsProbabilityMeasure m] [IsProbabilityMeasure μ]
    (hmμ : m ≪ μ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hL2 : eLpNorm (fun y => (m.rnDeriv μ y).toReal - 1) 2 μ ≤ ENNReal.ofReal δ)
    {g : Torus d → ℝ} (hgm : Measurable g) {B : ℝ} (hB : ∀ x, |g x| ≤ B) :
    |∫ x, g x ∂m - ∫ x, g x ∂μ| ≤ B * δ := by
  set r : Torus d → ℝ := fun y => (m.rnDeriv μ y).toReal with hr
  have hrm : Measurable r := (Measure.measurable_rnDeriv m μ).ennreal_toReal
  have hri : Integrable r μ := Measure.integrable_toReal_rnDeriv
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hgb : ∀ x, ‖g x‖ ≤ B := fun x => by rw [Real.norm_eq_abs]; exact hB x
  have hgi : Integrable g μ :=
    Integrable.of_bound hgm.aestronglyMeasurable B (Filter.Eventually.of_forall hgb)
  have hrg : Integrable (fun x => r x * g x) μ :=
    hri.mul_bdd hgm.aestronglyMeasurable (Filter.Eventually.of_forall hgb)
  have hmg : ∫ x, g x ∂m = ∫ x, r x * g x ∂μ := (integral_toReal_rnDeriv_mul hmμ).symm
  have h1 : ∫ x, g x ∂m - ∫ x, g x ∂μ = ∫ x, (r x - 1) * g x ∂μ := by
    rw [hmg, ← integral_sub hrg hgi]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only []; ring)
  have hf1 : Integrable (fun x => r x - 1) μ := hri.sub (integrable_const _)
  have hfm : AEStronglyMeasurable (fun x => r x - 1) μ := (hrm.sub measurable_const).aestronglyMeasurable
  have h2 : ∫ x, ‖r x - 1‖ ∂μ ≤ δ := by
    rw [integral_norm_eq_lintegral_enorm hfm]
    have e1 : ∫⁻ x, ‖r x - 1‖ₑ ∂μ = eLpNorm (fun x => r x - 1) 1 μ :=
      (eLpNorm_one_eq_lintegral_enorm hfm).symm
    have e2 : eLpNorm (fun x => r x - 1) 1 μ ≤ ENNReal.ofReal δ :=
      (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)).trans hL2
    rw [e1]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top e2).trans (le_of_eq (ENNReal.toReal_ofReal hδ))
  rw [h1]
  calc |∫ x, (r x - 1) * g x ∂μ| = ‖∫ x, (r x - 1) * g x ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x, ‖(r x - 1) * g x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, B * ‖r x - 1‖ ∂μ := by
        refine integral_mono (hf1.mul_bdd hgm.aestronglyMeasurable
          (Filter.Eventually.of_forall hgb)).norm (hf1.norm.const_mul B) fun x => ?_
        simp only [norm_mul]
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (hgb x) (norm_nonneg _)
    _ = B * ∫ x, ‖r x - 1‖ ∂μ := integral_const_mul _ _
    _ ≤ B * δ := mul_le_mul_of_nonneg_left h2 hB0

/-- The lattice-sum constant `√(2 ∑_k ⟨k⟩^{-2m})`. -/
def eqiK (d : ℕ) (m : ℝ) : ℝ := Real.sqrt (2 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)))

theorem eqi_norm_le {m : ℝ} (hm : (d : ℝ) < 2 * m) {μ ν : Measure (Torus d)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hνμ : ν ≪ μ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hL2 : eLpNorm (fun y => (ν.rnDeriv μ y).toReal - 1) 2 μ ≤ ENNReal.ofReal δ) :
    ‖NegSobolev.ofMeasureDiff m ν μ‖ ≤ eqiK d m * δ := by
  unfold eqiK
  set F := NegSobolev.ofMeasureDiff m ν μ
  obtain ⟨hs2, hn⟩ := NegSobolev.coord_sq F
  have hs := summable_jp_rpow (d := d) m hm
  have hb : ∀ k : NonzeroLattice d, NegSobolev.coord F k ^ 2 ≤
      2 * δ ^ 2 * Lattice.jp k.1 ^ (-(2 * m)) := by
    intro k
    rw [show NegSobolev.coord F k = _ from HRS.coord_ofMeasureDiff hm ν μ k, mul_pow, Torus.jp_rpow_sq,
      show 2 * -m = -(2 * m) by ring]
    have h1 : |Torus.measureRealCoeff ν k - Torus.measureRealCoeff μ k| ≤ Real.sqrt 2 * δ :=
      eqi_bias_le hνμ hδ hL2 (Torus.continuous_realMode k).measurable
        (fun x => Torus.abs_realMode_le k x)
    have h4 : (Torus.measureRealCoeff ν k - Torus.measureRealCoeff μ k) ^ 2 ≤ 2 * δ ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [sq_abs, mul_pow, Real.sq_sqrt (by norm_num)] at this
      exact this
    have hj : 0 ≤ Lattice.jp k.1 ^ (-(2 * m)) := Real.rpow_nonneg (Torus.jp_pos _).le _
    nlinarith
  have hsum : ‖F‖ ^ 2 ≤ 2 * δ ^ 2 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)) := by
    rw [hn, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hb hs2 (hs.mul_left _)
  have hS0 : 0 ≤ ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)) :=
    tsum_nonneg fun k => Real.rpow_nonneg (Torus.jp_pos _).le _
  have hsq : Real.sqrt (2 * δ ^ 2 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) =
      Real.sqrt (2 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) * δ := by
    rw [show 2 * δ ^ 2 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)) =
      (2 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) * δ ^ 2 by ring,
      Real.sqrt_mul (mul_nonneg (by norm_num) hS0), Real.sqrt_sq hδ]
  calc ‖F‖ = Real.sqrt (‖F‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (2 * δ ^ 2 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) :=
        Real.sqrt_le_sqrt hsum
    _ = _ := hsq


theorem eqi_sqrt_le {s : ℝ} (hs0 : 0 ≤ s) {N : ℕ} (hN : 1 ≤ N) :
    Real.sqrt (deltaN d s N) ≤ Real.sqrt N * deltaN d s N := by
  have h1 := one_le_mul_deltaN' (d := d) hs0 hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hδ : 0 ≤ deltaN d s N := by
    by_contra hneg
    push_neg at hneg
    nlinarith
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt hN0.le]
  nlinarith

theorem eq_init_assembly_proof (hd : 2 ≤ d)
    (hdirect : type_of% (@HRS.Main.equilibrium_paths_direct d))
    (hflow : type_of% (@HRS.MD.EQLawFlow.eq_flow_exists_proof d))
    (hmarg : type_of% (@HRS.Main.equilibrium_marginal_L2_proof d)) :
    type_of% (@HRS.Main.equilibrium_initial_law d) := by
  intro _ s hs0 hsd V hV βm βp hβm hββ m hm
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hmd : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m := max_lt (by linarith) (by linarith)
  have hm2 : (d : ℝ) < 2 * m := by linarith
  obtain ⟨C1, hC1, H1⟩ := hdirect hd hs0 hsd V hV βm βp hβm hββ m hmd 0 le_rfl
  obtain ⟨C2, hC2, H2⟩ := hmarg hd hs0 hsd V hV βm βp hβm hββ
  have hK0 : 0 ≤ eqiK d m := Real.sqrt_nonneg _
  have hKC : 0 ≤ eqiK d m * C2 := mul_nonneg hK0 hC2.le
  refine ⟨C1 + eqiK d m * C2, by linarith, ?_⟩
  intro β hβ ρβ hρ N hN Ω' _ P' _ Z hZ
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hN1 : 1 ≤ N := by omega
  -- the Gibbs measure
  obtain ⟨hpos, hsm⟩ := Q41.q41_thermal_regular hd hs0 hsd hβ0 hV hρ
  have hρs : SmoothPosDensity ρβ := ⟨hρ.1, hsm, hpos⟩
  have hP : canonicalGibbs (periodicRiesz d s) V N β =
      modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρβ) := by
    obtain ⟨Λ, hΛ0, hΛ'⟩ := PoleCavityAux.exists_density_bound hρs
    refine canonicalGibbs_eq_modulatedGibbs (periodicRiesz d s) V β ρβ hρ
      (fun x => periodicRiesz_neg x) ?_
    intro x
    exact (CoercAux.J_bounds (by omega : 1 ≤ d) hs0 hsd one_pos hρs.density hΛ0.le hΛ' x).1
  haveI hGp : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) :=
    HRS.MD.EQLawFlow.eqlaw_gibbs_prob hd hs0 hsd hV hβ0 hN1
  have hex : IsExchangeable (canonicalGibbs (periodicRiesz d s) V N β) := by
    rw [hP]; exact modulatedGibbs_isExchangeable _ _ _ (fun x => periodicRiesz_neg x)
  haveI hμp : IsProbabilityMeasure (withDensityReal ρβ) := isProb_withDensityReal hρs.density
  haveI := InitialDataAux.negSobolev_secondCountable d m
  -- a flow on the horizon `0`
  obtain ⟨Ω, _, P, _, X₀, W, X, hX⟩ := hflow hd hs0 hsd V hV hβ0 hN ((0 : ℝ) + 0) (by norm_num)
  obtain ⟨hdir1, hdir2⟩ := H1 β hβ ρβ hρ 0 le_rfl N hN P X₀ W X hX P' Z hZ
  have hstat : P.map (X 0) = canonicalGibbs (periodicRiesz d s) V N β :=
    HRS.MD.Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ0 ((0 : ℝ) + 0) hN P X₀ W X hX
      0 (by simp)
  have hstr : IsStrongSolution P (PDE.mfData d s hs0 hsd V β hβ0) ((0 : ℝ) + 0) X₀ W X := by
    rcases hX.flow.flow with ⟨h, _⟩ | ⟨h1, _⟩
    · exact h
    · exfalso; omega
  have hX0 : Measurable (X 0) := hstr.adapted 0
  -- the centered field at time zero
  have hζm : Measurable (zetaE m (canonicalGibbs (periodicRiesz d s) V N β) :
      Config d N → NegSobolev d m) := by
    haveI := isProbabilityMeasure_meanEmpirical (canonicalGibbs (periodicRiesz d s) V N β) hN1
    exact (continuous_const_smul (Real.sqrt N)).measurable.comp
      (measurable_ofMeasureDiff_empirical hm2 (meanEmpirical (canonicalGibbs (periodicRiesz d s) V N β)) hN1)
  have key1 : (law P (Main.windowZeta m 0 0 P X)).map (eqiEv m) =
      law (canonicalGibbs (periodicRiesz d s) V N β) (zetaE m (canonicalGibbs (periodicRiesz d s) V N β)) := by
    have hfun : Main.windowZeta m 0 0 P X =
        fun ω => eqiCst m (zetaE m (canonicalGibbs (periodicRiesz d s) V N β) (X 0 ω)) :=
      funext fun ω => by rw [eqi_windowZeta, hstat]
    have hmeas : Measurable (fun ω => eqiCst m (zetaE m (canonicalGibbs (periodicRiesz d s) V N β) (X 0 ω))) :=
      (eqiCst m).continuous.measurable.comp (hζm.comp hX0)
    rw [hfun, Measure.map_map (eqiEv m).continuous.measurable hmeas]
    have : (eqiEv m) ∘ (fun ω => eqiCst m (zetaE m (canonicalGibbs (periodicRiesz d s) V N β) (X 0 ω))) =
        (zetaE m (canonicalGibbs (periodicRiesz d s) V N β)) ∘ X 0 := funext fun ω => rfl
    rw [this, ← Measure.map_map hζm hX0, hstat]
  have key2 : (law P' (Main.windowPath m 0 0 Z)).map (eqiEv m) = law P' (Z 0) := by
    have hfun : Main.windowPath m 0 0 Z = fun ω => eqiCst m (Z 0 ω) :=
      funext fun ω => eqi_windowPath m Z ω
    have hmeas : Measurable (fun ω => eqiCst m (Z 0 ω)) := (eqiCst m).continuous.measurable.comp (hZ.meas 0)
    rw [hfun, Measure.map_map (eqiEv m).continuous.measurable hmeas]
    rfl
  have hev1 : max 1 (‖(eqiEv m : PathSpace d m 0 →L[ℝ] NegSobolev d m)‖ ^ 2) = 1 := by
    refine max_eq_left ?_
    have h0 := norm_nonneg (eqiEv m : PathSpace d m 0 →L[ℝ] NegSobolev d m)
    nlinarith [eqiEv_norm_le (d := d) m]
  have hs1 := smoothDist_map_clm_le (eqiEv m) 2 (law P (Main.windowZeta m 0 0 P X))
    (law P' (Main.windowPath m 0 0 Z))
  rw [key1, key2, hev1, one_mul] at hs1
  have hw1 := wassersteinE_map_clm_le (eqiEv m) 2 (by norm_num) (law P (Main.windowZeta m 0 0 P X))
    (law P' (Main.windowPath m 0 0 Z))
  rw [key1, key2] at hw1
  have hw1' : wassersteinE 2 (law (canonicalGibbs (periodicRiesz d s) V N β)
        (zetaE m (canonicalGibbs (periodicRiesz d s) V N β))) (law P' (Z 0)) ≤
      wassersteinE 2 (law P (Main.windowZeta m 0 0 P X)) (law P' (Main.windowPath m 0 0 Z)) := by
    refine hw1.trans ?_
    have : ENNReal.ofReal ‖(eqiEv m : PathSpace d m 0 →L[ℝ] NegSobolev d m)‖ ≤ 1 := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (eqiEv_norm_le m)
    exact (mul_le_mul' this le_rfl).trans (le_of_eq (one_mul _))
  -- the deterministic shift
  obtain ⟨hac, hL2⟩ := H2 β hβ ρβ hρ N hN
  have hδ0 : 0 ≤ deltaN d s N := by
    have h1 := one_le_mul_deltaN' (d := d) hs0 hN1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    by_contra hneg
    push_neg at hneg
    nlinarith
  haveI hmp : IsProbabilityMeasure (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) := by
    rw [← meanEmpirical_eq_firstMarginal _ hex hN1]
    exact isProbabilityMeasure_meanEmpirical _ hN1
  have hnorm := eqi_norm_le hm2 hac (mul_nonneg hC2.le hδ0) hL2
  set c : NegSobolev d m := Real.sqrt N • NegSobolev.ofMeasureDiff m
    (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) (withDensityReal ρβ) with hc
  have hcn : ‖c‖ ≤ Real.sqrt N * (eqiK d m * (C2 * deltaN d s N)) := by
    rw [hc, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)
  have heta : (fun X : Config d N => etaE m X (withDensityReal ρβ)) =
      fun X => zetaE m (canonicalGibbs (periodicRiesz d s) V N β) X + c := funext fun X => by
    rw [eta_eq_zeta_add m hm2 (canonicalGibbs (periodicRiesz d s) V N β) (withDensityReal ρβ) X hN1,
      meanEmpirical_eq_firstMarginal _ hex hN1]
  have hsq := eqi_sqrt_le (d := d) hs0 hN1
  have hrN : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hcb : ‖c‖ ≤ eqiK d m * C2 * (Real.sqrt N * deltaN d s N) := by
    refine hcn.trans (le_of_eq ?_); ring
  rw [heta]
  constructor
  · -- smooth distance
    have h1 := eqi_smooth_translate (canonicalGibbs (periodicRiesz d s) V N β)
      (zetaE m (canonicalGibbs (periodicRiesz d s) V N β)) hζm.aemeasurable c
    have h2 := smoothDist_triangle 2
      (law (canonicalGibbs (periodicRiesz d s) V N β)
        (fun X => zetaE m (canonicalGibbs (periodicRiesz d s) V N β) X + c))
      (law (canonicalGibbs (periodicRiesz d s) V N β) (zetaE m (canonicalGibbs (periodicRiesz d s) V N β)))
      (law P' (Z 0))
    have hmul : C1 * Real.sqrt (deltaN d s N) ≤ C1 * (Real.sqrt N * deltaN d s N) :=
      mul_le_mul_of_nonneg_left hsq hC1.le
    calc _ ≤ _ := h2
      _ ≤ ‖c‖ + C1 * Real.sqrt (deltaN d s N) := add_le_add h1 (hs1.trans hdir1)
      _ ≤ _ := by nlinarith
  · -- Wasserstein distance
    have h1 := wassersteinE_translate (canonicalGibbs (periodicRiesz d s) V N β) 2 (by norm_num)
      (zetaE m (canonicalGibbs (periodicRiesz d s) V N β)) hζm.aemeasurable c 0
    simp only [add_zero, sub_zero] at h1
    have h2 := wassersteinE_triangle 2 (by norm_num)
      (law (canonicalGibbs (periodicRiesz d s) V N β)
        (fun X => zetaE m (canonicalGibbs (periodicRiesz d s) V N β) X + c))
      (law (canonicalGibbs (periodicRiesz d s) V N β) (zetaE m (canonicalGibbs (periodicRiesz d s) V N β)))
      (law P' (Z 0))
    refine h2.trans ?_
    refine (add_le_add h1 (hw1'.trans hdir2)).trans ?_
    have ha : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hs0' : 0 ≤ Real.sqrt (deltaN d s N) := Real.sqrt_nonneg _
    rw [← ENNReal.ofReal_add (norm_nonneg _) (mul_nonneg hC1.le (add_nonneg ha hs0'))]
    refine ENNReal.ofReal_le_ofReal ?_
    have hmul : C1 * Real.sqrt (deltaN d s N) ≤ C1 * (Real.sqrt N * deltaN d s N) :=
      mul_le_mul_of_nonneg_left hsq hC1.le
    nlinarith [mul_nonneg hKC (add_nonneg ha hs0'), mul_nonneg hKC ha, mul_nonneg hKC hs0']

-- Inline check: the conclusion is the frozen statement once `equilibrium_paths_direct` is supplied as an argument.
example (hd : 2 ≤ d) (hdirect : type_of% (@HRS.Main.equilibrium_paths_direct d)) :
    type_of% (@HRS.Main.equilibrium_initial_law d) :=
  @eq_init_assembly_proof d hd hdirect (@HRS.MD.EQLawFlow.eq_flow_exists_proof d)
    (@HRS.Main.equilibrium_marginal_L2_proof d)

end EQAsmInit

end MD

end HRS
