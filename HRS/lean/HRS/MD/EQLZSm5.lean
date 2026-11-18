import HRS.MD.EQLZSm4

/-!
# EQ-LZ packet SM, part 5: `eqlz_smooth_proof` (`SmoothMaximal`)

Relocated proof of `HRS.MD.EQLZ.eqlz_smooth` (the statement is copied verbatim; the tie `EQLZSmTie.lean` checks it
against the sorried spec).  Assembly: dyadic grids (`sm_dyadic_le`, continuity of `t ↦ F(X_t)`), monotone
convergence over the dyadic levels, the grid inequality of `sm_grid_true` (`LevelMaximal`, Fatou, `Z_n/Z`), the
elementary bound `|F(X_t) - πF|² ≤ 2|F(X_t) - F(X_a)|² + 2|F(X_a) - πF|²` and the stationarity of `X_a` (MARG).
The constant is `C = 80`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal
open HRS.MD.EQLZ

namespace HRS

namespace MD

namespace EQLZSm

variable {d N : ℕ}

/-- (SM, `eqlz_smooth`.)  Statement copied verbatim from `HRS.MD.EQLZ.eqlz_smooth`. -/
theorem eqlz_smooth_proof (hlevel : LevelMaximal) (hmarg : type_of% @HRS.MD.EQLZMarg.eqlz_marg_proof) :
    SmoothMaximal := by
  refine ⟨80, by norm_num, ?_⟩
  intro d N hd hN s hs0 hsd V hV β hβ T a hT ha Ω _ P _ X₀ W X h F hF
  set μ := canonicalGibbs (periodicRiesz d s) V N β with hμ
  set c0 := ∫ Y, F Y ∂μ with hc0
  set Var := ∫ Y, (F Y - c0) ^ 2 ∂μ with hVar
  set E := ∫ Y, LZ.configGradSq F Y ∂μ with hE
  have hS : IsStrongSolution P (PDE.mfData d s hs0 hsd V β hβ) (a + T) X₀ W X := by
    rcases h.flow.flow with hh | ⟨hd1, -⟩
    · exact hh.1
    · omega
  have hmarg_a : law P (X a.toNNReal) = μ :=
    hmarg d N hd hN s hs0 hsd V hV β hβ (a + T) P X₀ W X h a ha (by linarith)
  have hXm : ∀ t, Measurable (X t) := hS.adapted
  have hΦc : Continuous (fun x : Torus (N * d) => F ((d1_configEquiv d N).symm x)) :=
    b15_continuous_of_isCk (sm_isCk_of_smooth hF 2)
  have hFc : Continuous F := by
    have h2 := hΦc.comp (d1_configEquiv_continuous d N)
    have h3 : ((fun x : Torus (N * d) => F ((d1_configEquiv d N).symm x)) ∘ d1_configEquiv d N) = F := by
      funext X; simp
    rwa [h3] at h2
  have hFm : Measurable F := hFc.measurable
  haveI : IsProbabilityMeasure μ := by
    rw [← hmarg_a]; unfold law; infer_instance
  -- the dyadic level functions
  set S : ℕ → Ω → ℝ≥0∞ := fun i ω =>
    smGrid (fun t => ENNReal.ofReal ((F (X t.toNNReal ω) - F (X a.toNNReal ω)) ^ 2)) a T (2 ^ i) with hSdef
  have hSm : ∀ i, Measurable (S i) := fun i =>
    Measurable.iSup fun j => ENNReal.measurable_ofReal.comp
      (((hFm.comp (hXm _)).sub (hFm.comp (hXm _))).pow_const 2)
  have hSmono : Monotone S := fun i j hij ω =>
    smGrid_mono (fun t => ENNReal.ofReal ((F (X t.toNNReal ω) - F (X a.toNNReal ω)) ^ 2)) a T hij
  have hSbound : ∀ i, ∫⁻ ω, S i ω ∂P ≤ ENNReal.ofReal (40 * T * β⁻¹ * E) := fun i =>
    sm_grid_true hlevel hd hN s hs0 hsd V hV β hβ T a hT ha P X₀ W X h F hF (2 ^ i) Nat.one_le_two_pow
  have hmax : ∫⁻ ω, ⨆ i, S i ω ∂P ≤ ENNReal.ofReal (40 * T * β⁻¹ * E) := by
    rw [lintegral_iSup hSm hSmono]
    exact iSup_le hSbound
  -- the variance term
  have hint : Integrable (fun Y => (F Y - c0) ^ 2) μ :=
    ((hFc.sub continuous_const).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hvar : ∫⁻ ω, ENNReal.ofReal ((F (X a.toNNReal ω) - c0) ^ 2) ∂P = ENNReal.ofReal Var := by
    have h1 : ∫⁻ ω, ENNReal.ofReal ((F (X a.toNNReal ω) - c0) ^ 2) ∂P =
        ∫⁻ Y, ENNReal.ofReal ((F Y - c0) ^ 2) ∂(P.map (X a.toNNReal)) := by
      rw [lintegral_map _ (hXm _)]
      exact ENNReal.measurable_ofReal.comp ((hFm.sub measurable_const).pow_const 2)
    have h2 : P.map (X a.toNNReal) = μ := hmarg_a
    rw [h1, h2, hVar, ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun Y => sq_nonneg _)]
  -- the pointwise bound
  have hpt : ∀ᵐ ω ∂P, (⨆ t ∈ LZ.ratTimes a T, ENNReal.ofReal ((F (X t.toNNReal ω) - c0) ^ 2)) ≤
      2 * (⨆ i, S i ω) + 2 * ENNReal.ofReal ((F (X a.toNNReal ω) - c0) ^ 2) := by
    filter_upwards [hS.cont] with ω hcont
    refine iSup₂_le fun t ht => ?_
    have hfc : ContinuousOn (fun t : ℝ => F (X t.toNNReal ω)) (Set.Icc a (a + T)) :=
      (hFc.comp (continuous_pi fun i => (hcont i).comp continuous_real_toNNReal)).continuousOn
    have hdy := sm_dyadic_le (fun t : ℝ => F (X t.toNNReal ω)) a T hT hfc ht.1
    have h2 : ENNReal.ofReal ((F (X t.toNNReal ω) - c0) ^ 2) ≤
        2 * ENNReal.ofReal ((F (X t.toNNReal ω) - F (X a.toNNReal ω)) ^ 2) +
          2 * ENNReal.ofReal ((F (X a.toNNReal ω) - c0) ^ 2) := by
      calc ENNReal.ofReal ((F (X t.toNNReal ω) - c0) ^ 2)
          ≤ ENNReal.ofReal (2 * (F (X t.toNNReal ω) - F (X a.toNNReal ω)) ^ 2 +
              2 * (F (X a.toNNReal ω) - c0) ^ 2) :=
            ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (F (X t.toNNReal ω) - 2 * F (X a.toNNReal ω) + c0)])
        _ = _ := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
              ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    refine h2.trans ?_
    gcongr
  -- integrate
  have hA : Measurable fun ω => 2 * (⨆ i, S i ω) :=
    (Measurable.iSup hSm).const_mul 2
  calc ∫⁻ ω, ⨆ t ∈ LZ.ratTimes a T, ENNReal.ofReal ((F (X t.toNNReal ω) - c0) ^ 2) ∂P
      ≤ ∫⁻ ω, (2 * (⨆ i, S i ω) + 2 * ENNReal.ofReal ((F (X a.toNNReal ω) - c0) ^ 2)) ∂P :=
        lintegral_mono_ae hpt
    _ = 2 * (∫⁻ ω, ⨆ i, S i ω ∂P) + 2 * ENNReal.ofReal Var := by
        have hm2 : Measurable fun ω => ENNReal.ofReal ((F (X a.toNNReal ω) - c0) ^ 2) :=
          ENNReal.measurable_ofReal.comp (((hFm.comp (hXm _)).sub measurable_const).pow_const 2)
        rw [lintegral_add_left hA, lintegral_const_mul (2 : ℝ≥0∞) (Measurable.iSup hSm),
          lintegral_const_mul (2 : ℝ≥0∞) hm2, hvar]
    _ ≤ 2 * ENNReal.ofReal (40 * T * β⁻¹ * E) + 2 * ENNReal.ofReal Var := by gcongr
    _ ≤ ENNReal.ofReal 80 * (ENNReal.ofReal Var + ENNReal.ofReal (β⁻¹ * T) * ENNReal.ofReal E) := by
        have hE0 : 0 ≤ E := integral_nonneg fun Y => Finset.sum_nonneg fun k _ => sq_nonneg _
        have h2le : (2 : ℝ≥0∞) ≤ ENNReal.ofReal 80 := by
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
          exact ENNReal.ofReal_le_ofReal (by norm_num)
        have h1 : 2 * ENNReal.ofReal (40 * T * β⁻¹ * E) =
            ENNReal.ofReal 80 * (ENNReal.ofReal (β⁻¹ * T) * ENNReal.ofReal E) := by
          have hb : 0 ≤ β⁻¹ * T := mul_nonneg (inv_nonneg.mpr hβ.le) hT
          rw [← ENNReal.ofReal_mul hb, ← ENNReal.ofReal_mul (by norm_num),
            show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring
        rw [mul_add, h1, add_comm]
        gcongr

end EQLZSm

end MD

end HRS

end
