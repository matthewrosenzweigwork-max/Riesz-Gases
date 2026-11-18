import HRS.MD.EQBurnDefs
import HRS.MD.EQAsmInit
import HRS.MD.EQLawPath
import HRS.MD.EQLawFlow
import HRS.MD.EQInitGauss
import HRS.Sections.Q41Aux21
import HRS.Main.A9Aux29
import HRS.Main.GFB4Aux6
import HRS.Main.A33Aux2
import HRS.Uniform.Q54cAux11

/-!
# Packet EQ-BURN P6 (chunk D): `eq_static_clt_of_burn_proof`

Relocated proof of `HRS.MD.EQBurn.eq_static_clt_of_burn` (frozen with its `sorry` in `HRS/MD/EQBurnSpec.lean`; the tie
`HRS/MD/EQBurnCltTie.lean` checks that the statements agree).  Route: the fixed-`β` burn-in at `T = 0` and `u = 0` gives
`d₂(law ζ_N^0, law Z^0) ≤ C √δ_N` (as in `eq_direct_assembly_proof` and `eq_init_assembly_proof`, with `a → ∞` at fixed `N` through
`eq_path_stationary_proof` and `eq_flow_exists_proof`); the continuous functional `z ↦ z(φ)` is a linear map into `ℝ¹`, and
`a9_fd_converges` transfers the convergence of `smoothDist` to the one-dimensional marginals; finally
`⟨ζ_N^0, φ⟩ = linCoord` and `⟨Z^0, φ⟩ ~ N(0, C_β(φ,φ))`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

namespace HRS.MD.EQBurnClt

open HRS HRS.LZ HRS.Uniform HRS.Main HRS.MD.EQAsmInit HRS.MD.EQ29 HRS.MD.EQBurn

variable {d : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

/-! ### The pairing of `ζ_N` with a smooth test function -/

theorem eqclt_eval_zeta {m : ℝ} (hm : (d : ℝ) < 2 * m) {N : ℕ} (hN : 1 ≤ N)
    (P : Measure (Config d N)) [IsProbabilityMeasure P] (hex : IsExchangeable P)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (X : Config d N) :
    NegSobolev.eval (zetaE m P X) φ = linCoord (firstMarginal P) φ X := by
  haveI := empirical_isProbabilityMeasure (Nat.pos_of_ne_zero (by omega)) X
  haveI := isProbabilityMeasure_meanEmpirical P hN
  unfold zetaE
  rw [HRS.Uniform.Q54c.eval_smul, NegSobolev.eval_ofMeasureDiff hm _ _ φ hφ, pair_empirical (by omega) X φ,
    meanEmpirical_eq_firstMarginal P hex hN]
  unfold linCoord
  rw [one_div]

theorem eqclt_linCoord_meas {N : ℕ} (μ : Measure (Torus d)) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Measurable (fun X : Config d N => linCoord μ φ X) := by
  have hc : Continuous φ := by
    have := hφ
    unfold Torus.IsSmooth Torus.IsCk at this
    exact Torus.continuous_of_continuous_lift (this.continuous)
  unfold linCoord
  have hm : ∀ i : Fin N, Measurable (fun X : Config d N => φ (X i)) := fun i =>
    hc.measurable.comp (measurable_pi_apply i)
  exact measurable_const.mul (((Finset.measurable_sum _ (fun i _ => hm i)).const_mul _).sub_const _)

/-! ### The one-dimensional Gaussian law -/

theorem eqclt_gauss_law (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) {m : ℝ}
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m) (hZ : IsStationaryGaussianField P' s β hs0 hsd hβ V ρβ m Z)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    P'.map (fun ω => NegSobolev.eval (Z 0 ω) φ) =
      gaussianLaw (susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β φ φ) := by
  obtain ⟨hpos, hsm⟩ := Q41.q41_thermal_regular hd hs0 hsd hβ hV hρβ
  haveI : IsProbabilityMeasure (withDensityReal ρβ) := isProb_withDensityReal hρβ.1
  have hlaw := hZ.gaussian 1 (fun _ => 0) (fun _ => φ) (fun _ => le_rfl) (fun _ => hφ)
  have hpsd := Q41.q41_lagcov_psd hd hs0 hsd hβ hV hρβ
    (PoleCavityAux.continuous_of_smoothPos ⟨hρβ.1, hsm, hpos⟩) hpos (fun _ : Fin 1 => (0 : ℝ))
    (fun _ => le_rfl) (fun _ => φ) (fun _ => hφ)
  have h0 := (PDE.equilibriumSemigroup_generator (by omega) s hs0 hsd β hβ V hV ρβ hρβ hsm hpos
    φ hφ).1
  have hS : PDE.stationaryLagCov d s β (PDE.mfData d s hs0 hsd V β hβ) ρβ
      (fun _ : Fin 1 => (0 : ℝ)) (fun _ => φ) =
      Matrix.of fun _ _ => susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β φ φ := by
    ext a b
    simp only [PDE.stationaryLagCov, Matrix.of_apply, le_refl, if_true, sub_self, h0]
    unfold susceptibilityCov
    rw [HRS.MD.EQInit.eqinit_responseInverse_projMean]
  rw [hS] at hlaw hpsd
  have hmeas : Measurable (fun ω => NegSobolev.eval (Z 0 ω) φ) := by
    have hm : MemSobolev m φ := HRS.A33.a33_memSob m hφ
    have : (fun z : NegSobolev d m => NegSobolev.eval z φ) = HRS.GF.gfb4_ell m φ :=
      funext fun z => (HRS.GF.gfb4_ell_apply hm z).symm
    have hc : Continuous (fun z : NegSobolev d m => NegSobolev.eval z φ) := by
      rw [this]; exact (HRS.GF.gfb4_ell m φ).continuous
    exact hc.measurable.comp (hZ.meas 0)
  have hWm : Measurable (fun ω => (WithLp.toLp 2 fun _ : Fin 1 => NegSobolev.eval (Z 0 ω) φ :
      EuclideanSpace ℝ (Fin 1))) :=
    (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).measurable.comp (measurable_pi_iff.2 fun _ => hmeas)
  have hmp := (measurePreserving_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin 1)))
    (i := (0 : Fin 1)) hpsd).map_eq
  have e1 : (fun ω => NegSobolev.eval (Z 0 ω) φ) =
      (fun x : EuclideanSpace ℝ (Fin 1) => x 0) ∘ (fun ω => (WithLp.toLp 2 fun _ : Fin 1 =>
        NegSobolev.eval (Z 0 ω) φ : EuclideanSpace ℝ (Fin 1))) := rfl
  rw [e1, ← Measure.map_map (by fun_prop) hWm]
  have hlaw' : P'.map (fun ω => (WithLp.toLp 2 fun _ : Fin 1 => NegSobolev.eval (Z 0 ω) φ :
      EuclideanSpace ℝ (Fin 1))) = _ := hlaw
  rw [hlaw', hmp]
  simp [gaussianLaw]

/-! ### The Gibbs measure -/

theorem eqclt_gibbs (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) {N : ℕ} (hN : 2 ≤ N) :
    IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) ∧
      IsExchangeable (canonicalGibbs (periodicRiesz d s) V N β) := by
  obtain ⟨hpos, hsm⟩ := Q41.q41_thermal_regular hd hs0 hsd hβ hV hρβ
  have hρs : SmoothPosDensity ρβ := ⟨hρβ.1, hsm, hpos⟩
  have hP : canonicalGibbs (periodicRiesz d s) V N β =
      modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρβ) := by
    obtain ⟨Λ, hΛ0, hΛ'⟩ := PoleCavityAux.exists_density_bound hρs
    refine canonicalGibbs_eq_modulatedGibbs (periodicRiesz d s) V β ρβ hρβ
      (fun x => periodicRiesz_neg x) ?_
    intro x
    exact (CoercAux.J_bounds (by omega : 1 ≤ d) hs0 hsd one_pos hρs.density hΛ0.le hΛ' x).1
  refine ⟨HRS.MD.EQLawFlow.eqlaw_gibbs_prob hd hs0 hsd hV hβ (by omega), ?_⟩
  rw [hP]
  exact modulatedGibbs_isExchangeable _ _ _ (fun x => periodicRiesz_neg x)

theorem eqclt_zeta_meas {m : ℝ} (hm2 : (d : ℝ) < 2 * m) {N : ℕ} (hN : 1 ≤ N)
    (P : Measure (Config d N)) [IsProbabilityMeasure P] :
    Measurable (zetaE m P : Config d N → NegSobolev d m) := by
  haveI := isProbabilityMeasure_meanEmpirical P hN
  exact (continuous_const_smul (Real.sqrt N)).measurable.comp
    (measurable_ofMeasureDiff_empirical hm2 (meanEmpirical P) hN)

/-! ### The distance bound at time `0` from the fixed-`β` burn-in -/

theorem eqclt_dist_bound (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (m : ℝ)
    (hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m)
    (hburn : BurninConcl d s hs0 hsd V β β hβ m 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → NegSobolev d m),
        IsStationaryGaussianField P' s β hs0 hsd hβ V ρβ m Z →
        smoothDist 2 (law (canonicalGibbs (periodicRiesz d s) V N β)
            (zetaE m (canonicalGibbs (periodicRiesz d s) V N β))) (law P' (Z 0)) ≤
          C * Real.sqrt (deltaN d s N) := by
  obtain ⟨C, c, hC, hc, h⟩ := hburn
  refine ⟨C, hC, ?_⟩
  intro N hN Ω' _ P' _ Z hZ
  have hmd : (d : ℝ) / 2 < m := by
    have h1 : (d : ℝ) / 2 + 2 < m := lt_of_le_of_lt (le_max_right _ _) hm
    linarith
  have hm2 : (d : ℝ) < 2 * m := by
    have h1 : (d : ℝ) + 1 < m := lt_of_le_of_lt (le_max_left _ _) hm
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hN1 : 1 ≤ N := by omega
  obtain ⟨hGp, hex⟩ := eqclt_gibbs hd hs0 hsd V hV hβ ρβ hρβ hN
  haveI := InitialDataAux.negSobolev_secondCountable d m
  -- the flow on the horizon `0`
  obtain ⟨Ω, _, P, _, X₀, W, X, hX⟩ := HRS.MD.EQLawFlow.eq_flow_exists_proof hd hs0 hsd V hV hβ hN
    ((0 : ℝ) + 0) (by norm_num)
  have key : ∀ a : ℝ, 0 ≤ a →
      smoothDist 2 (law P (Main.windowZeta m 0 0 P X)) (law P' (Main.windowPath m 0 0 Z)) ≤
        C * (Real.exp (-c * a) + Real.sqrt (deltaN d s N)) := by
    intro a ha
    obtain ⟨Ω'', _, P'', _, X₀', W', X', hX'⟩ :=
      HRS.MD.EQLawFlow.eq_flow_exists_proof hd hs0 hsd V hV hβ hN (a + 0) (by linarith)
    have hlaw := HRS.MD.EQLawPath.eq_path_stationary_proof hd hs0 hsd V hV hβ m hmd 0 le_rfl hN
      P X₀ W X 0 le_rfl hX P'' X₀' W' X' a ha hX'
    rw [hlaw]
    exact (h β ⟨le_rfl, le_rfl⟩ ρβ hρβ a ha N hN P'' X₀' W' X' hX' P' Z hZ).1
  have hdir : smoothDist 2 (law P (Main.windowZeta m 0 0 P X)) (law P' (Main.windowPath m 0 0 Z)) ≤
      C * Real.sqrt (deltaN d s N) := by
    have hlim : Tendsto (fun a : ℝ => C * (Real.exp (-c * a) + Real.sqrt (deltaN d s N))) atTop
        (𝓝 (C * (0 + Real.sqrt (deltaN d s N)))) := by
      have h1 : Tendsto (fun a : ℝ => Real.exp (-c * a)) atTop (𝓝 0) := by
        have h2 : Tendsto (fun a : ℝ => -c * a) atTop atBot :=
          tendsto_id.const_mul_atTop_of_neg (by linarith)
        exact Real.tendsto_exp_atBot.comp h2
      exact ((h1.add_const _).const_mul C)
    have := ge_of_tendsto hlim (eventually_atTop.2 ⟨0, fun a ha => key a ha⟩)
    simpa using this
  -- evaluation at time `0`
  have hstat : P.map (X 0) = canonicalGibbs (periodicRiesz d s) V N β :=
    HRS.MD.Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ ((0 : ℝ) + 0) hN P X₀ W X hX
      0 (by simp)
  have hstr : IsStrongSolution P (PDE.mfData d s hs0 hsd V β hβ) ((0 : ℝ) + 0) X₀ W X := by
    rcases hX.flow.flow with ⟨h, _⟩ | ⟨h1, _⟩
    · exact h
    · exfalso; omega
  have hX0 : Measurable (X 0) := hstr.adapted 0
  have hζm := eqclt_zeta_meas hm2 hN1 (canonicalGibbs (periodicRiesz d s) V N β)
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
  exact hs1.trans hdir

/-! ### The theorem -/

theorem eq_static_clt_of_burn_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (φ : Torus d → ℝ)
    (hφ : Torus.IsSmooth φ)
    (hburn : BurninConcl d s hs0 hsd V β β hβ ((d : ℝ) + 2) 0) :
    ConvergesInLaw
      (fun N : ℕ => law (canonicalGibbs (periodicRiesz d s) V N β)
        (linCoord (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) φ))
      (gaussianLaw (susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β φ φ)) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set m : ℝ := (d : ℝ) + 2 with hmdef
  have hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m :=
    max_lt (by linarith) (by linarith)
  have hm2 : (d : ℝ) < 2 * m := by linarith
  have hmq : (d : ℝ) + 2 < 2 * m := by linarith
  obtain ⟨C, hC, hdist⟩ := eqclt_dist_bound hd hs0 hsd V hV hβ ρβ hρβ m hm hburn
  obtain ⟨Ω', _, P', _, Z, hZ⟩ := Q41.q41_field_exists hd hs0 hsd hβ V hV ρβ hρβ m hmq
  haveI := InitialDataAux.negSobolev_secondCountable d m
  have hmφ : MemSobolev m φ := HRS.A33.a33_memSob m hφ
  set ell : NegSobolev d m →L[ℝ] ℝ := HRS.GF.gfb4_ell m φ with hell
  have hellap : ∀ z, ell z = NegSobolev.eval z φ := fun z => HRS.GF.gfb4_ell_apply hmφ z
  -- the linear map into `ℝ¹`
  set T : NegSobolev d m →L[ℝ] ℝ^1 :=
    ell.smulRight (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) with hT
  have hT0 : ∀ z, T z 0 = NegSobolev.eval z φ := fun z => by
    simp [hT, hellap]
  -- the measures
  intro f
  refine (tendsto_add_atTop_iff_nat 2).1 ?_
  set μ : ℕ → Measure (NegSobolev d m) := fun n =>
    law (canonicalGibbs (periodicRiesz d s) V (n + 2) β) (zetaE m (canonicalGibbs (periodicRiesz d s) V (n + 2) β))
    with hμ
  have hGp : ∀ n : ℕ, IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V (n + 2) β) := fun n =>
    (eqclt_gibbs hd hs0 hsd V hV hβ ρβ hρβ (by omega : 2 ≤ n + 2)).1
  have hζm : ∀ n : ℕ, Measurable (zetaE m (canonicalGibbs (periodicRiesz d s) V (n + 2) β) :
      Config d (n + 2) → NegSobolev d m) := fun n => by
    haveI := hGp n
    exact eqclt_zeta_meas hm2 (by omega) _
  haveI hμp : ∀ n, IsProbabilityMeasure (μ n) := fun n => by
    haveI := hGp n
    exact inferInstance
  set lam₀ : Measure (NegSobolev d m) := law P' (Z 0) with hlam₀
  haveI : IsProbabilityMeasure lam₀ := inferInstance
  have hlc : ConvergesInLaw (fun _ : ℕ => lam₀) lam₀ := fun g => tendsto_const_nhds
  have hsd0 : Tendsto (fun n : ℕ => smoothDist 2 (μ n) ((fun _ : ℕ => lam₀) n)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => C * Real.sqrt (deltaN d s (n + 2))) atTop (𝓝 (C * Real.sqrt 0)) := by
      have := (HRS.MarginalAux.tendsto_deltaN hs0 hsd (by omega : 1 ≤ d)).comp
        (tendsto_add_atTop_nat 2)
      exact ((Real.continuous_sqrt.tendsto 0).comp this).const_mul C
    rw [Real.sqrt_zero, mul_zero] at h1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1
      (fun n => smoothDist_nonneg 2 _ _) (fun n => ?_)
    haveI := hGp n
    exact hdist (n + 2) (by omega) P' Z hZ
  haveI : ∀ n, IsProbabilityMeasure ((fun _ : ℕ => lam₀) n) := fun n => inferInstance
  let g : (ℝ^1) →ᵇ ℝ := f.compContinuous
    (⟨fun x : ℝ^1 => x 0, (EuclideanSpace.proj (0 : Fin 1)).continuous⟩ : C(ℝ^1, ℝ))
  have hconv := HRS.Main.A9.a9_fd_converges T μ (fun _ => lam₀) lam₀ hlc hsd0 g
  have hgT : ∀ z, g (T z) = f (NegSobolev.eval z φ) := fun z => by
    show f ((T z) 0) = _
    rw [hT0]
  have hgTc : Continuous fun z : NegSobolev d m => g (T z) := g.continuous.comp T.continuous
  have hcont : Continuous fun z : NegSobolev d m => f (NegSobolev.eval z φ) := by
    have : (fun z : NegSobolev d m => f (NegSobolev.eval z φ)) = fun z => f (ell z) :=
      funext fun z => by rw [hellap]
    rw [this]; exact f.continuous.comp ell.continuous
  -- left side
  have hleft : ∀ n : ℕ, ∫ x, g (T x) ∂(μ n) = ∫ x, f x ∂(law (canonicalGibbs (periodicRiesz d s) V (n + 2) β)
      (linCoord (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) φ)) := by
    intro n
    haveI := hGp n
    obtain ⟨-, hex⟩ := eqclt_gibbs hd hs0 hsd V hV hβ ρβ hρβ (by omega : 2 ≤ n + 2)
    have hlm := eqclt_linCoord_meas (N := n + 2) (firstMarginal (canonicalGibbs (periodicRiesz d s) V (n + 2) β)) hφ
    rw [integral_map hlm.aemeasurable f.continuous.aestronglyMeasurable]
    have hμn : μ n = Measure.map (zetaE m (canonicalGibbs (periodicRiesz d s) V (n + 2) β))
        (canonicalGibbs (periodicRiesz d s) V (n + 2) β) := rfl
    rw [hμn, integral_map (f := fun x => g (T x)) (hζm n).aemeasurable hgTc.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only [hgT]
    rw [eqclt_eval_zeta hm2 (by omega) _ hex hφ X]
  have hright : ∫ x, g (T x) ∂lam₀ =
      ∫ x, f x ∂(gaussianLaw (susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β φ φ)) := by
    rw [← eqclt_gauss_law hd hs0 hsd V hV hβ ρβ hρβ P' Z hZ hφ]
    have hme : Measurable (fun ω => NegSobolev.eval (Z 0 ω) φ) := by
      have : (fun ω => NegSobolev.eval (Z 0 ω) φ) = fun ω => ell (Z 0 ω) :=
        funext fun ω => (hellap _).symm
      rw [this]; exact ell.continuous.measurable.comp (hZ.meas 0)
    rw [integral_map hme.aemeasurable f.continuous.aestronglyMeasurable]
    have hl0 : lam₀ = Measure.map (Z 0) P' := rfl
    rw [hl0, integral_map (f := fun x => g (T x)) (hZ.meas 0).aemeasurable hgTc.aestronglyMeasurable]
    simp only [hgT]
  rw [← hright]
  exact hconv.congr (fun n => hleft n)

end HRS.MD.EQBurnClt
