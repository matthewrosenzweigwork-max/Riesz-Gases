import HRS.Main.HeadlineEquilibrium
import HRS.MD.EQTransShift
import HRS.MD.EQInterpWin

/-!
# `HRS.Main.mean_field_centering_lower_bound`: statement-only packet specification (Session A, Mfcl)

Frozen theorem: `HRS/Main/HeadlineEquilibrium.lean:384` (TeX L1104-1148, L1117-1121, L1138-1141).

## Proof architecture (first-moment lower bound, no new analysis)

Fix `φ = ρβ` (smooth and positive by `Q41.q41_thermal_regular`, `HRS/Sections/Q41Aux14.lean:131`) and let
`ℓ : 𝒳_{m,T} →L ℝ` be the time-zero pairing `w ↦ ⟨w^0, ρβ⟩` (packet `exists_pathEval`).  Then

* `W₁(A, B) ≥ |E ℓ(A) - E ℓ(B)| / (‖ℓ‖ + 1)` (packets `wassersteinE_one_real_ge_abs_mean_diff`,
  `wassersteinE_one_ge_clm_mean_diff`; the second uses `HRS.Main.wassersteinE_map_clm_le`, `HRS/Main/Headline.lean:409`);
* `ℓ(windowFluc) = linCoord μβ ρβ (X^u)` a.s. (packets `windowFluc_at'_ae`, `windowFluc_aemeasurable`,
  `pathEval_windowFluc_ae`), whose law is the image of the canonical Gibbs law by `linCoord` (stationarity,
  `HRS.MD.EQInterp.flow_facts`, `HRS/MD/EQInterpWin.lean:57`), with mean `centerShift` (packet `integral_linCoord_gibbs`);
* `ℓ(window of Z) = Z^0(ρβ) ∼ N(0,v)` has mean `0` (packet `gauss_pathEval`);
* `centerShift = √N (m_N - μβ)(ρβ) ≥ c₁ √N δ_N` for large `N` (packets `centerShift_ratio_tendsto`, `centerShift_lower`),
  by the proved bias expansion and `supercriticalBias_pos_proof`.

Remark on hypotheses: `s < 2d/3` (`hs2`) is not used by the proof; the lower bound holds for every `d/2 < s < d`
(the statement is the sharp one for `s < 2d/3`, where `√N δ_N → 0`).  Similarly `m > max(d+1, d/2+2)` is used only
through `d < 2m`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.Mfcl

open HRS HRS.Main HRS.LZ HRS.MD.EQ29

variable {d : ℕ}

/-! ### A. Soft functional analysis -/

/-- **A1** (size S, about 50 lines).  The time-zero pairing with a smooth test function is a continuous linear
functional on path space.  Route: copy `HRS.ME.FamV.rateEval` (`HRS/ME/FamVC.lean:141`) with `Torus.cosMode k` replaced by `φ`:
`fourierVec d m φ hs` (`FamVC.lean:107`, `memℓp_fourierVec` :99) with the summability `hs` from
`(HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hφ m).2` (`HRS/PDE/MeanFieldSemigroup.lean:207`, as in `summable_cosMode` :113);
`F ↦ eval F φ = ⟪F, fourierVec⟫` is `eval_eq_inner_cos` (:123) with `cosMode k` generalised (same proof: `lp.inner_eq_tsum`);
`ℓ = (innerSL ℝ v).comp (ContinuousMap.evalCLM ℝ t0)`.  (`FamVC` is not imported here; copy the three lemmas.) -/
theorem exists_pathEval (m T : ℝ) (hT : 0 ≤ T) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ) :
    ∃ ℓ : PathSpace d m T →L[ℝ] ℝ, ∀ w : PathSpace d m T,
      ℓ w = NegSobolev.eval (w.at' ⟨0, Set.left_mem_Icc.2 hT⟩) φ := by
  sorry

/-- **A2** (size S, about 60 lines).  On `ℝ`, `W₁` dominates the difference of the means.  Route: `le_iInf`; for a coupling `π`
(`π.map fst = μ`, `π.map snd = ν`, so `π` is a probability measure by `IsCoupling.isProbabilityMeasure`,
`HRS/Prob/Metrics.lean:183`) the functions `z.1`, `z.2` are `π`-integrable by `integrable_map_measure`; then
`|∫ x dμ - ∫ y dν| = |∫ (z.1 - z.2) dπ| ≤ ∫ ‖z.1 - z.2‖ dπ`, and `ofReal_integral_eq_lintegral_ofReal`; same pattern as
`smoothDist_one_le_wasserstein` (`HRS/Prob/Metrics.lean:362`; the case `∫⁻ = ⊤` is trivial). -/
theorem wassersteinE_one_real_ge_abs_mean_diff (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : Integrable (fun x : ℝ => x) μ) (hν : Integrable (fun x : ℝ => x) ν) :
    ENNReal.ofReal |∫ x, x ∂μ - ∫ x, x ∂ν| ≤ wassersteinE 1 μ ν := by
  sorry

/-- **A3** (size S, about 40 lines).  Transfer along a continuous linear functional.  Route: `A2` applied to
`P.map ℓ`, `Q.map ℓ` (probability measures by `Measure.isProbabilityMeasure_map` with `ℓ.continuous.measurable`),
`wassersteinE_map_clm_le ℓ 1 le_rfl P Q` (`HRS/Main/Headline.lean:409`), then
`ofReal a ≤ ofReal ‖ℓ‖ * W ≤ ofReal (‖ℓ‖ + 1) * W` and division by `‖ℓ‖ + 1 > 0` (if `W = ⊤` the claim is trivial). -/
theorem wassersteinE_one_ge_clm_mean_diff {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [MeasurableSpace B] [BorelSpace B] (ℓ : B →L[ℝ] ℝ) (P Q : Measure B) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hP : Integrable (fun x : ℝ => x) (P.map ℓ))
    (hQ : Integrable (fun x : ℝ => x) (Q.map ℓ)) :
    ENNReal.ofReal (|∫ x, x ∂(P.map ℓ) - ∫ x, x ∂(Q.map ℓ)| / (‖ℓ‖ + 1)) ≤ wassersteinE 1 P Q := by
  sorry

/-! ### B. The window of the fluctuation path -/

/-- **A4** (size M, about 80 lines).  Almost surely the window `windowFluc` is the honest (continuous) path: `flucPath` is the junk
`0` path off the continuity event, so this packet records continuity and the pointwise value.  Route: from
`HRS.MD.EQInterp.flow_facts` (`HRS/MD/EQInterpWin.lean:57`) the paths `t ↦ X t ω i` are a.s. continuous and `X t` is measurable;
`HRS.MD.EQLawPath.eqlaw_continuous_ofMeasureDiff_empirical` (`HRS/MD/EQLawZeta.lean:69`) gives continuity of `x ↦ ofMeasureDiff m (empirical x) ν` on `Config d N` for `ν` a probability measure
(here `withDensityReal ρβ`, `isProb_withDensityReal`, `HRS/Energy/Modulated.lean:2169`); compose with `τ ↦ X (toNNReal u + toNNReal τ) ω`
and `Real.toNNReal` continuity; then `flucPath` is `dif_pos` (as `adjkg_flucPath_at`, `HRS/Sections/AdjKGlueAux7.lean:46`, which can be
imported instead of re-proved). -/
theorem windowFluc_at'_ae (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 2 ≤ N) {u T : ℝ} (hu : 0 ≤ u) (hT : 0 ≤ T)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : IsStationaryGibbsFlow P s hs0 hsd V β hβ (u + T) X₀ W X) {m : ℝ} (hm : (d : ℝ) < 2 * m)
    (ρβ : Torus d → ℝ) (hρβ : IsProbDensity ρβ) (σ : ℝ) :
    ∀ᵐ ω ∂P, ∀ τ : Set.Icc (0 : ℝ) T,
      (windowFluc m T u σ X (fun _ => ρβ) ω).at' τ =
        σ • NegSobolev.ofMeasureDiff m
          (empirical (X (Real.toNNReal u + Real.toNNReal (τ : ℝ)) ω)) (withDensityReal ρβ) := by
  sorry

/-- **A5** (size S, about 50 lines).  Measurability of the window (needed so that `law P (windowFluc ..)` is a probability measure).
Route: `windowFluc = fun ω => HRS.MD.EQLawPath.eqlaw_pathOf d m T (fun τ => σ • ofMeasureDiff m (empirical (X (toNNReal u + toNNReal τ) ω)) ν)`
definitionally (as `windowZeta`, see `HRS.ME.Ret.aemeasurable_windowPath_Icc`, `HRS/ME/RetProj.lean:221`, for the pattern);
`HRS.MD.EQLawPath.eqlaw_aemeasurable_pathOf` (`HRS/MD/EQLawZeta.lean:107`) needs measurability of each time slice (continuous
`eqlaw_continuous_ofMeasureDiff_empirical` composed with the measurable `X t`) and a.s. continuity (`A4`). -/
theorem windowFluc_aemeasurable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 2 ≤ N) {u T : ℝ} (hu : 0 ≤ u) (hT : 0 ≤ T)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : IsStationaryGibbsFlow P s hs0 hsd V β hβ (u + T) X₀ W X) {m : ℝ} (hm : (d : ℝ) < 2 * m)
    (ρβ : Torus d → ℝ) (hρβ : IsProbDensity ρβ) (σ : ℝ) :
    AEMeasurable (windowFluc m T u σ X (fun _ => ρβ)) P := by
  sorry

/-- **A6** (size S, about 60 lines).  The time-zero pairing of the window is the linear statistic `linCoord` of `X^u`.
Route: `A4` at `τ = 0` (note `toNNReal u + toNNReal 0 = toNNReal u`), `ℓ w = eval (w.at' 0) ρβ` (`hℓ`),
`NegSobolev.eval_ofMeasureDiff` (`HRS/Torus/Sobolev.lean:894`, needs `d < 2m`, `Torus.IsSmooth ρβ`, both measures probability:
`empirical_isProbabilityMeasure`, `HRS/Torus/Basic.lean:799`), `eval (σ • F) φ = σ * eval F φ` (via `abs`-free linearity of the `tsum`, or
`eval_eq_inner` as in `FamVC`), `pair_empirical` (`HRS/Torus/Basic.lean:806`) and `linCoord` unfolded
(`HRS/Equilibrium/StaticLimits.lean:167`).  Copy of the pointwise part of `HRS.ME.FamV.rate_zeta_law` (`HRS/ME/FamVC.lean:188`). -/
theorem pathEval_windowFluc_ae (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 2 ≤ N) {u T : ℝ} (hu : 0 ≤ u) (hT : 0 ≤ T)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : IsStationaryGibbsFlow P s hs0 hsd V β hβ (u + T) X₀ W X) {m : ℝ} (hm : (d : ℝ) < 2 * m)
    (ρβ : Torus d → ℝ) (hρβ : IsProbDensity ρβ) (hρs : Torus.IsSmooth ρβ)
    (ℓ : PathSpace d m T →L[ℝ] ℝ)
    (hℓ : ∀ w : PathSpace d m T, ℓ w = NegSobolev.eval (w.at' ⟨0, Set.left_mem_Icc.2 hT⟩) ρβ) :
    ∀ᵐ ω ∂P, ℓ (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ) ω) =
      linCoord (withDensityReal ρβ) ρβ (X (Real.toNNReal u) ω) := by
  sorry

/-- **A7** (size S, about 50 lines).  The law of the pairing of the window is the image of the Gibbs law.  Route: `A5` and `A6`:
`(P.map W).map ℓ = P.map (ℓ ∘ W)` (`AEMeasurable.map_map_of_aemeasurable`), `Measure.map_congr` with `A6`, then
`Measure.map_map` with the stationarity `P.map (X t) = canonicalGibbs ..` from `HRS.MD.EQInterp.flow_facts` (`HRS/MD/EQInterpWin.lean:57`),
exactly the `calc` of `HRS.ME.FamV.rate_zeta_law` (`HRS/ME/FamVC.lean:188-218`); measurability of `linCoord` is continuity of a finite sum. -/
theorem law_pathEval_windowFluc (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 2 ≤ N) {u T : ℝ} (hu : 0 ≤ u) (hT : 0 ≤ T)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : IsStationaryGibbsFlow P s hs0 hsd V β hβ (u + T) X₀ W X) {m : ℝ} (hm : (d : ℝ) < 2 * m)
    (ρβ : Torus d → ℝ) (hρβ : IsProbDensity ρβ) (hρs : Torus.IsSmooth ρβ)
    (ℓ : PathSpace d m T →L[ℝ] ℝ)
    (hℓ : ∀ w : PathSpace d m T, ℓ w = NegSobolev.eval (w.at' ⟨0, Set.left_mem_Icc.2 hT⟩) ρβ) :
    (law P (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ))).map ℓ =
      (canonicalGibbs (periodicRiesz d s) V N β).map (linCoord (withDensityReal ρβ) ρβ) := by
  sorry

/-! ### C. The mean of the linear statistic under the Gibbs law -/

/-- **A8** (size M, about 90 lines).  Integrability and mean of `linCoord (μβ) ρβ` under the canonical Gibbs law:
the mean is `centerShift = √N (m_N(ρβ) - μβ(ρβ))`.  Route: `linCoord` is bounded by `√N (‖ρβ‖∞ + ‖ρβ‖∞)` (smooth hence continuous,
`HRS.MD.EQTransShift.et_smooth_bound`, `HRS/MD/EQTransShift.lean:81`) and continuous, so integrable under the probability measure
`et_gibbs_prob` (:57); `integral_map`; `∫ N⁻¹ ∑ ρβ(X i) dP = ∫ ρβ d(meanEmpirical P)` is `HRS.integral_meanEmpirical`
(`HRS/Energy/Modulated.lean:1737`), and `meanEmpirical_eq_firstMarginal` (:959) with exchangeability
`HRS.ME.FamV.canonicalGibbs_isExchangeable` (`HRS/ME/FamVC.lean:81`, hypothesis `periodicRiesz_neg`) gives `pair (firstMarginal ..) ρβ`;
`centerShift` is `HRS/MD/EQ29Vocab.lean:120`.  (`FamVC` is not imported; its exchangeability lemma and the two before it, about
60 lines, are copied, or import `HRS.ME.FamVC` in the proof file.) -/
theorem integral_linCoord_gibbs (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρs : Torus.IsSmooth ρβ) {N : ℕ} (hN : 2 ≤ N) :
    Integrable (fun x : ℝ => x)
        ((canonicalGibbs (periodicRiesz d s) V N β).map (linCoord (withDensityReal ρβ) ρβ)) ∧
      ∫ x, x ∂((canonicalGibbs (periodicRiesz d s) V N β).map (linCoord (withDensityReal ρβ) ρβ)) =
        centerShift d s V β ρβ ρβ N := by
  sorry

/-! ### D. The Gaussian side -/

/-- **A9** (size S, about 60 lines).  The time-zero pairing of the Gaussian window is `N(0, v)`, a centred Gaussian, and the window is
measurable.  Route: copy of `HRS.ME.FamV.rate_gauss_law` (`HRS/ME/FamVD.lean:29`) with `cosMode k` replaced by `ρβ`: `eqgw_fidi ... .1`
(`HRS/MD/EQGaussWindow.lean:212`) for `AEMeasurable`, `eqgw_windowPath_at` (:198) with `hZ.cont` for the a.s. identity
`ℓ (windowPath m T 0 Z ω) = eval (Z 0 ω) ρβ`, and `HRS.MD.EQBurnClt.eqclt_gauss_law` (`HRS/MD/EQBurnClt.lean:63`) for the law of
`ω ↦ eval (Z 0 ω) ρβ`.  The mean part is `integral_id_gaussianReal` / `IsGaussian.integrable_id` (`gaussianLaw v = gaussianReal 0 v.toNNReal`,
`HRS/Prob/CLT.lean:56`). -/
theorem gauss_pathEval (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρs : Torus.IsSmooth ρβ) {m T : ℝ} (hT : 0 ≤ T)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m) (hZ : IsStationaryGaussianField P' s β hs0 hsd hβ V ρβ m Z)
    (ℓ : PathSpace d m T →L[ℝ] ℝ)
    (hℓ : ∀ w : PathSpace d m T, ℓ w = NegSobolev.eval (w.at' ⟨0, Set.left_mem_Icc.2 hT⟩) ρβ) :
    AEMeasurable (windowPath m T 0 Z) P' ∧
      Integrable (fun x : ℝ => x) ((law P' (windowPath m T 0 Z)).map ℓ) ∧
      ∫ x, x ∂((law P' (windowPath m T 0 Z)).map ℓ) = 0 := by
  sorry

/-! ### E. The deterministic bias -/

/-- **A10** (size M, about 80 lines).  `centerShift / (√N N^{1-d/s}) → b(φ)` for `d/2 < s < d` and smooth `φ`.  Route: this is the local
`have hbias` inside `HRS.MD.EQTransShift.eq_shift_limit_proof` (`HRS/MD/EQTransShift.lean:292-306`, `have hbias`): extract it verbatim
(`et_smooth_bound` :81, `et_bias_pair_tendsto` :192, `equilibrium_marginal_L2_proof`/`equilibrium_bias_expansion_proof`
(`HRS/Main/EqBiasFinal.lean:44`), `et_centerShift_eq` :111, `Tendsto.congr'`, `field_simp`). -/
theorem centerShift_ratio_tendsto (hd : 2 ≤ d) {s : ℝ} (hs1 : (d : ℝ) / 2 < s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (φ : Torus d → ℝ) (hφ : Torus.IsSmooth φ) :
    Tendsto (fun N : ℕ => centerShift d s V β ρβ φ N /
        (Real.sqrt N * (N : ℝ) ^ (1 - (d : ℝ) / s))) atTop (𝓝 (supercriticalBias d s β ρβ φ)) := by
  sorry

/-- **A11** (size S, about 50 lines).  The shift is bounded below by `c₁ √N δ_N`.  Route: `A10` with `φ = ρβ` and the limit
`b = supercriticalBias d s β ρβ ρβ > 0` (`HRS.Main.supercriticalBias_pos_proof`, `HRS/Main/EqBiasFinal.lean:22`; `hnc`); eventually the
ratio exceeds `b/2` (`Tendsto.eventually_gt` / `eventually_gt_of_tendsto_gt`), `deltaN d s N = N^{1-d/s}` for `s > d/2`
(unfold `deltaN`, `if_neg` twice; as in `et_sqrt_mul_deltaN_tendsto`, `HRS/MD/EQTransShift.lean:140`), `√N N^{1-d/s} > 0`;
`c₁ = b/2` and `N₀` from the eventual statement together with `2`. -/
theorem centerShift_lower (hd : 2 ≤ d) {s : ℝ} (hs1 : (d : ℝ) / 2 < s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hnc : ∃ x y, ρβ x ≠ ρβ y) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      c₁ * (Real.sqrt N * deltaN d s N) ≤ centerShift d s V β ρβ ρβ N := by
  sorry

/-! ### F. Assembly -/

/-- **A12** (size M, about 100 lines): the frozen theorem `HRS.Main.mean_field_centering_lower_bound`, verbatim.  Route:
`hρs := (Q41.q41_thermal_regular hd hs0 hsd hβ hV hρβ).2`; `hm2 : d < 2m` from `hm` (`d/2 + 2 < m` and `0 ≤ d`);
`hT0 : 0 ≤ T`; `ℓ := exists_pathEval m T hT0.le ρβ hρs` (`A1`); `c₁, N₀` from `A11`; `c := c₁ / (‖ℓ‖ + 1)`; `N₀` is raised to `max N₀ 2`.
Given the data, package `⟨hflow, hfilt, hinit⟩ : IsStationaryGibbsFlow P s hs0 hsd V β hβ (u + T) X₀ W X`.  Probability measures:
`law P (windowFluc ..)` by `A5` and `Measure.isProbabilityMeasure_map`, `law P' (windowPath ..)` by `A9`.  Means: `A7` rewrites
`(law P windowFluc).map ℓ` to the Gibbs image, `A8` gives integrability and mean `centerShift`, `A9` gives mean `0`.  Then
`A3` yields `ofReal (|centerShift - 0| / (‖ℓ‖ + 1)) ≤ wassersteinE 1 ..`, and
`ofReal (c * (√N δ_N)) ≤ ofReal (centerShift / (‖ℓ‖+1))` (`A11`, `centerShift ≥ 0` there since `c₁ √N δ_N ≥ 0`; `deltaN ≥ 0` from
`HRS.MD.EQTransShift.et_deltaN_nonneg`, :29) via `ENNReal.ofReal_le_ofReal` and `div_le_div_of_nonneg_right`. -/
theorem mean_field_centering_lower_bound_core (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (hs1 : (d : ℝ) / 2 < s)
    (hs2 : s < 2 * (d : ℝ) / 3) (β : ℝ) (hβ : 0 < β)
    (ρβ : Torus d → ℝ) (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    (hnc : ∃ x y, ρβ x ≠ ρβ y) (m : ℝ) (hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m) (T : ℝ)
    (hT : 0 < T) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ u : ℝ, 0 ≤ u →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P (PDE.mfData d s hs0 hsd V β hβ) (u + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        law P X₀ = canonicalGibbs (periodicRiesz d s) V N β →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → NegSobolev d m), IsStationaryGaussianField P' s β hs0 hsd hβ V ρβ m Z →
        ENNReal.ofReal (c * (Real.sqrt N * deltaN d s N)) ≤
          wassersteinE 1 (law P (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ)))
            (law P' (windowPath m T 0 Z)) := by
  sorry

example : type_of% @HRS.Main.mean_field_centering_lower_bound := @mean_field_centering_lower_bound_core

end HRS.MH.Mfcl
