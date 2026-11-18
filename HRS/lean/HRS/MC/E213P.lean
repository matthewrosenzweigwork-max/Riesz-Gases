import HRS.MC.E213N3
import HRS.MC.S7UCU
import HRS.MD.EQInterpHolder
import HRS.Main.T25PAux29
import HRS.Main.A34Aux17
import HRS.Main.A33Aux2
import HRS.Main.GFEVAux7

/-!
# E213P (GS-2): transfer of the window law of the Gaussian limit field to level `m`

For `S : PreparedData d`, `EdgeworthHyp S β₀ m`, `r = 2d + 6`, a Gaussian limit field `η*` at level `r`
(`IsGaussianLimitField S.dyn S.ρ (withDensityReal S.ρ0) β₀ r P* η*`, e.g. the global field of `E213N`)
and any `(ν, P', Z₀, Z)` with `ν` centred Gaussian of covariance `preparedCov` and
`IsPreparedLinear S m (a+T) ν P' Z₀ Z`:

`law P' (windowPath m T a Z) = (law P* (procWin r T a η*)).map (epath _ T)`.

Steps: (i) `embed m ∘ η*` is a linear fluctuation solution at level `m`; (ii) `ν = (embed m)_* law(η*⁰)`
(`a34_gauss_unique`, `E213L`); (iii) `t25p_lin_unique`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213P

open HRS HRS.Main HRS.GF HRS.T25P HRS.Sec7

variable {d : ℕ}

/-! ### Step (i): replacing the initial datum by `Y 0`, and the level change -/

/-- The initial datum of an `IsLinearFluctuationSolution` can be replaced by the (measurable) `Y 0`. -/
theorem e213p_linSol_init_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (D : DynData d)
    (ρ : ℝ → Torus d → ℝ) {r q T : ℝ} {Y₀ : Ω → NegSobolev d r} {Y : ℝ → Ω → NegSobolev d r}
    (h : IsLinearFluctuationSolution P D ρ r q T Y₀ Y) :
    IsLinearFluctuationSolution P D ρ r q T (Y 0) Y := by
  have hae : Y 0 =ᵐ[P] Y₀ := h.init
  refine ⟨Filter.Eventually.of_forall fun ω => rfl, h.cont, h.meas, fun p ts φ hts hφ => ?_⟩
  obtain ⟨hi, hl⟩ := h.gaussian_part p ts φ hts hφ
  have hG : (fun ω => (WithLp.toLp 2 fun a =>
      NegSobolev.eval (Y (ts a) ω) (φ a) -
        NegSobolev.eval (Y 0 ω) (propagator D ρ 0 (ts a) (φ a)) : EuclideanSpace ℝ (Fin p))) =ᵐ[P]
      (fun ω => (WithLp.toLp 2 fun a =>
      NegSobolev.eval (Y (ts a) ω) (φ a) -
        NegSobolev.eval (Y₀ ω) (propagator D ρ 0 (ts a) (φ a)) : EuclideanSpace ℝ (Fin p))) := by
    filter_upwards [hae] with ω hω
    simp only [hω]
  refine ⟨hi.congr hG.symm hae.symm, ?_⟩
  show P.map _ = _
  rw [Measure.map_congr hG]
  exact hl

/-- The level change `E_r ↪ E_m` preserves `IsLinearFluctuationSolution` (same data, evaluations agree). -/
theorem e213p_linSol_embed {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (D : DynData d)
    (ρ : ℝ → Torus d → ℝ) {r m q T : ℝ} (hrm : r ≤ m) {Y₀ : Ω → NegSobolev d r}
    {Y : ℝ → Ω → NegSobolev d r}
    (h : IsLinearFluctuationSolution P D ρ r q T Y₀ Y) :
    IsLinearFluctuationSolution P D ρ m q T (fun ω => NegSobolev.embed m (Y₀ ω))
      (fun t ω => NegSobolev.embed m (Y t ω)) := by
  have hcont : Continuous (fun F : NegSobolev d r => NegSobolev.embed m F) :=
    (HRS.MD.EQInterp.embedCLM hrm).continuous
  refine ⟨?_, ?_, ?_, fun p ts φ hts hφ => ?_⟩
  · filter_upwards [h.init] with ω hω
    simp only [hω]
  · filter_upwards [h.cont] with ω hω
    exact hcont.comp_continuousOn hω
  · intro t
    exact hcont.measurable.comp (h.meas t)
  · obtain ⟨hi, hl⟩ := h.gaussian_part p ts φ hts hφ
    have hG : (fun ω => (WithLp.toLp 2 fun a =>
        NegSobolev.eval (NegSobolev.embed m (Y (ts a) ω)) (φ a) -
          NegSobolev.eval (NegSobolev.embed m (Y₀ ω)) (propagator D ρ 0 (ts a) (φ a)) :
          EuclideanSpace ℝ (Fin p))) =
        (fun ω => (WithLp.toLp 2 fun a =>
        NegSobolev.eval (Y (ts a) ω) (φ a) -
          NegSobolev.eval (Y₀ ω) (propagator D ρ 0 (ts a) (φ a)) : EuclideanSpace ℝ (Fin p))) := by
      funext ω
      simp only [gfev_eval_embed hrm]
    refine ⟨?_, ?_⟩
    · show IndepFun _ _ P
      rw [hG]
      exact hi.comp measurable_id hcont.measurable
    · show P.map _ = _
      rw [hG]
      exact hl

/-! ### Step (ii): the embedded initial law -/

/-- The level change preserves `IsCenteredGaussianWithCov`. -/
theorem e213p_cgc_embed {r m : ℝ} (hrm : r ≤ m) {γ : Measure (NegSobolev d r)}
    {C : (Torus d → ℝ) → (Torus d → ℝ) → ℝ} (h : IsCenteredGaussianWithCov r γ C) :
    IsCenteredGaussianWithCov m (γ.map (fun F => NegSobolev.embed m F)) C := by
  have hL : (fun F : NegSobolev d r => NegSobolev.embed m F) =
      ⇑(HRS.MD.EQInterp.embedCLM hrm) := rfl
  rw [hL]
  obtain ⟨⟨hg, hmean⟩, hcov⟩ := h
  have := hg
  refine ⟨⟨inferInstance, fun L => ?_⟩, fun φ ψ hφ hψ => ?_⟩
  · rw [integral_map (HRS.MD.EQInterp.embedCLM hrm).continuous.aemeasurable
      L.continuous.aestronglyMeasurable]
    exact hmean (L.comp (HRS.MD.EQInterp.embedCLM hrm))
  · have hmφ := HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hφ m
    have hmψ := HRS.PDE.MFSemigroup.memSobolev_of_isSmooth hψ m
    have hcm : Continuous fun F : NegSobolev d m =>
        NegSobolev.eval F φ * NegSobolev.eval F ψ :=
      (HRS.Uniform.Q54c.continuous_eval_const hmφ).mul (HRS.Uniform.Q54c.continuous_eval_const hmψ)
    rw [integral_map (HRS.MD.EQInterp.embedCLM hrm).continuous.aemeasurable
      hcm.aestronglyMeasurable]
    simp only [HRS.MD.EQInterp.embedCLM_apply, gfev_eval_embed hrm]
    exact hcov φ ψ hφ hψ

theorem e213p_r_le_m {S : PreparedData d} {β₀ m : ℝ} (hE : EdgeworthHyp S β₀ m) {r : ℝ}
    (hr : r = 2 * (d : ℝ) + 6) : r ≤ m := by
  have := hE.m_gt
  have h0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rw [hr]; linarith

/-! ### Window paths -/

theorem e213p_windowPath_embed {Ω : Type} {r m : ℝ} (hrm : r ≤ m) (T a : ℝ) (ha : 0 ≤ a)
    (η : ℝ → Ω → NegSobolev d r) (ω : Ω)
    (hω : ContinuousOn (fun t => η t ω) (Set.Icc 0 (a + T))) :
    windowPath m T a (fun t ω => NegSobolev.embed m (η t ω)) ω =
      HRS.MD.EQInterp.epath hrm T (procWin r T a η ω) := by
  have hcont : Continuous (fun F : NegSobolev d r => NegSobolev.embed m F) :=
    (HRS.MD.EQInterp.embedCLM hrm).continuous
  have hc : Continuous fun t : Set.Icc (0 : ℝ) T => η (a + t) ω := by
    have : ContinuousOn (fun t => η (a + t) ω) (Set.Icc 0 T) :=
      hω.comp (continuousOn_const.add continuousOn_id)
        (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    exact continuousOn_iff_continuous_domRestrict.1 this
  have hc' : Continuous fun t : Set.Icc (0 : ℝ) T => NegSobolev.embed m (η (a + t) ω) := hcont.comp hc
  have e1 : toPath r T (fun t ω => η (a + t) ω) ω =
      (⟨fun t : Set.Icc (0 : ℝ) T => η (a + t) ω, hc⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d r)) :=
    dif_pos hc
  have e2 : toPath m T (fun t ω => NegSobolev.embed m (η (a + t) ω)) ω =
      (⟨fun t : Set.Icc (0 : ℝ) T => NegSobolev.embed m (η (a + t) ω), hc'⟩ :
        C(Set.Icc (0 : ℝ) T, NegSobolev d m)) := dif_pos hc'
  show toPath m T (fun t ω => NegSobolev.embed m (η (a + t) ω)) ω =
    HRS.MD.EQInterp.epath hrm T (toPath r T (fun t ω => η (a + t) ω) ω)
  rw [e1, e2]
  exact ContinuousMap.ext fun t => rfl

/-- `AEMeasurable` of the window of an `IsPreparedLinear` path (so that its law is not the zero measure). -/
theorem e213p_windowPath_aemeasurable (S : PreparedData d) (m : ℝ) (T a : ℝ) (hT : 0 < T) (ha : 0 ≤ a)
    {ν : Measure (NegSobolev d m)} {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] {Z₀ : Ω' → NegSobolev d m} {Z : ℝ → Ω' → NegSobolev d m}
    (hZ : IsPreparedLinear S m (a + T) ν P' Z₀ Z) :
    AEMeasurable (windowPath m T a Z) P' :=
  HRS.MC.Sec7.S7UCU.S7UCU_procWin_aemeasurable P' m T hT Z a ha hZ.sol.meas hZ.sol.cont

/-! ### Step (iii): the window law -/

/-- **GS-2.**  The window law of every `IsPreparedLinear` solution (at level `m`, centred Gaussian initial
law of covariance `preparedCov`) is the image under `epath` of the window law of any Gaussian limit field
`η` at level `r = 2d+6`; in particular it does not depend on the solution. -/
theorem e213p_window_law (S : PreparedData d) (β₀ m : ℝ) (hE : EdgeworthHyp S β₀ m)
    (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T a : ℝ) (hT : 0 < T) (ha : 0 ≤ a)
    {Ω₀ : Type} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    (η : ℝ → Ω₀ → NegSobolev d r)
    (hη : IsGaussianLimitField S.dyn S.ρ (withDensityReal S.ρ0) β₀ r P₀ η)
    (ν : Measure (NegSobolev d m)) (hν : IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m)
    (hZ : IsPreparedLinear S m (a + T) ν P' Z₀ Z) :
    law P' (windowPath m T a Z) =
      (law P₀ (procWin r T a η)).map (HRS.MD.EQInterp.epath (e213p_r_le_m hE hr) T) := by
  have hrm := e213p_r_le_m hE hr
  have : IsGaussian ν := hν.1.1
  obtain ⟨Y₀, hY₀cov, hlin⟩ := hη
  have hsol := e213p_linSol_init_zero S.dyn S.ρ (hlin (a + T))
  have hsolm := e213p_linSol_embed S.dyn S.ρ hrm hsol
  -- the initial law at level `m`
  have hae : η 0 =ᵐ[P₀] Y₀ := (hlin 0).init
  have hν₀ : IsCenteredGaussianWithCov r (P₀.map (η 0))
      (susceptibilityCov (periodicRiesz d S.dyn.s) (withDensityReal S.ρ0) β₀) := by
    rw [Measure.map_congr hae]; exact hY₀cov
  have hνm := e213p_cgc_embed hrm hν₀
  have : IsGaussian ((P₀.map (η 0)).map (fun F => NegSobolev.embed m F)) := hνm.1.1
  have hνeq : (P₀.map (η 0)).map (fun F => NegSobolev.embed m F) = ν := by
    obtain ⟨e⟩ := HRS.A33.a33_exists_equiv (d := d) (by have := S.hd; omega)
    refine HRS.A34.a34_gauss_unique e hνm.1 hν.1 (fun φ ψ hφ hψ => ?_)
    rw [hνm.2 φ ψ hφ hψ, hν.2 φ ψ hφ hψ]
    exact (HRS.MC.E213L.e213l_preparedCov_eq_susceptibilityCov_density S.hρ0 S.s β₀ hφ hψ).symm
  have hmeasη0 : Measurable fun ω => NegSobolev.embed m (η 0 ω) :=
    (HRS.MD.EQInterp.embedCLM hrm).continuous.measurable.comp ((hlin 0).meas 0)
  have hlaw : P'.map Z₀ = P₀.map (fun ω => NegSobolev.embed m (η 0 ω)) := by
    have h1 : P'.map Z₀ = ν := hZ.law_init
    rw [h1, ← hνeq, Measure.map_map (g := fun F => NegSobolev.embed m F)
      (HRS.MD.EQInterp.embedCLM hrm).continuous.measurable ((hlin 0).meas 0)]
    rfl
  -- uniqueness of the window law
  have htr := HRS.T25.t25_traj S
  obtain ⟨Cr, cr, hCr, hcr, VA, hdualA, -, hdecA, -⟩ :=
    HRS.AdjK.adjk_evolution_along_trajectory S.hd htr m
  have hKb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ a + T → ‖VA t r‖ ≤ Cr := by
    intro r t hr hrt _
    refine (hdecA r t hr hrt).trans ?_
    have h1 : Real.exp (-cr * (t - r)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sub_nonneg.2 hrt]
    nlinarith
  have key := t25p_lin_unique S.hd htr hT ha hdualA hCr.le hKb P' P₀ Z₀ hZ.meas Z hZ.sol
    (fun ω => NegSobolev.embed m (η 0 ω)) hmeasη0 (fun t ω => NegSobolev.embed m (η t ω))
    hsolm hlaw
  -- back to level `r`
  have hcontP : ∀ᵐ ω ∂P₀, ContinuousOn (fun t => η t ω) (Set.Icc 0 (a + T)) := (hlin (a + T)).cont
  have hpw : windowPath m T a (fun t ω => NegSobolev.embed m (η t ω)) =ᵐ[P₀]
      fun ω => HRS.MD.EQInterp.epath hrm T (procWin r T a η ω) := by
    filter_upwards [hcontP] with ω hω
    exact e213p_windowPath_embed hrm T a ha η ω hω
  have hmeasη : AEMeasurable (procWin r T a η) P₀ :=
    HRS.MC.Sec7.S7UCU.S7UCU_procWin_aemeasurable P₀ r T hT η a ha (fun t => (hlin 0).meas t) hcontP
  rw [key]
  show P₀.map _ = _
  rw [Measure.map_congr hpw]
  exact (AEMeasurable.map_map_of_aemeasurable (HRS.MD.EQInterp.epath hrm T).continuous.aemeasurable
    hmeasη).symm

/-- **GS-2 with the global field of `E213N`.**  There is a single Gaussian limit field `η*` (on a probability
space, `IsGaussianLimitField` for the regime of `S`) such that for every window `(T, a)` its window path is a.e.
measurable and the window law of every `IsPreparedLinear` solution is `(epath)_* (law (procWin r T a η*))`. -/
theorem e213p_global_window_law (S : PreparedData d) (β₀ m : ℝ) (hE : EdgeworthHyp S β₀ m)
    (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) :
    ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
      (η : ℝ → Ω₀ → NegSobolev d r),
      IsGaussianLimitField S.dyn S.ρ (withDensityReal S.ρ0) β₀ r P₀ η ∧
      ∀ T a : ℝ, 0 < T → 0 ≤ a →
        AEMeasurable (procWin r T a η) P₀ ∧
        ∀ (ν : Measure (NegSobolev d m)),
          IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0) →
          ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
            (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m),
            IsPreparedLinear S m (a + T) ν P' Z₀ Z →
            law P' (windowPath m T a Z) =
              (law P₀ (procWin r T a η)).map (HRS.MD.EQInterp.epath (e213p_r_le_m hE hr) T) := by
  obtain ⟨Ω₀, mΩ, P₀, hP₀, η, hη⟩ :=
    HRS.MC.E213N.e213n_exists_gaussianLimitField (HRS.MC.E213A.regimeOfPrepared S β₀ hE) r hr
  refine ⟨Ω₀, mΩ, P₀, hP₀, η, hη, fun T a hT ha => ⟨?_, ?_⟩⟩
  · obtain ⟨Y₀, -, hlin⟩ := hη
    exact HRS.MC.Sec7.S7UCU.S7UCU_procWin_aemeasurable P₀ r T hT η a ha (fun t => (hlin 0).meas t)
      (hlin (a + T)).cont
  · intro ν hν Ω' _ P' _ Z₀ Z hZ
    exact e213p_window_law S β₀ m hE r hr T a hT ha P₀ η hη ν hν P' Z₀ Z hZ

end HRS.MC.E213P

end
