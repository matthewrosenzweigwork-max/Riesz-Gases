import HRS.ME.RetBurnStmt
import HRS.MD.EQBurnClt
import HRS.MD.EQGaussWindow
import HRS.MD.EQInterpWin
import HRS.MD.EQBurnGaussLinLaw

/-!
# Row 5.10: projection of the path-space weighted estimates to finite vectors

`ret_shift_of_burn_proof`, `ret_initial_of_burn_proof`: from `RetBurnShift` and `RetBurnInit` to `RetStationaryShift` and
`RetStationaryInitial`, by pushing forward along the evaluation `γ ↦ (⟨γ(t_a), φ_a⟩)_a` of `C([0,T]; E_m) → ℝ^p`, whose norm is at most
`evBound m φ = (∑_a ‖ℓ_a‖²)^{1/2}` independently of the times.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.ME.Ret

open HRS HRS.LZ HRS.Uniform HRS.MD

variable {d : ℕ}

/-! ### The evaluation map -/

/-- The norm bound of the evaluation map, independent of the times. -/
def evBound (m : ℝ) {p : ℕ} (φ : Fin p → Torus d → ℝ) : ℝ :=
  Real.sqrt (∑ a, ‖HRS.GF.gfb4_ell m (φ a)‖ ^ 2)

theorem evBound_nonneg (m : ℝ) {p : ℕ} (φ : Fin p → Torus d → ℝ) : 0 ≤ evBound m φ :=
  Real.sqrt_nonneg _

theorem pathSpace_at'_add {m T : ℝ} (w v : PathSpace d m T) (t : Set.Icc (0 : ℝ) T) :
    (w + v).at' t = w.at' t + v.at' t := rfl

theorem pathSpace_at'_smul {m T : ℝ} (c : ℝ) (w : PathSpace d m T) (t : Set.Icc (0 : ℝ) T) :
    (c • w).at' t = c • w.at' t := rfl

theorem pathSpace_norm_at'_le {m T : ℝ} (w : PathSpace d m T) (t : Set.Icc (0 : ℝ) T) :
    ‖w.at' t‖ ≤ ‖w‖ :=
  ContinuousMap.norm_coe_le_norm (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from w) t

/-- The evaluation `γ ↦ (ℓ_a(γ(t_a)))_a` as a bounded linear map. -/
def evCLM (m : ℝ) {T : ℝ} {p : ℕ} (φ : Fin p → Torus d → ℝ) (ts : Fin p → Set.Icc (0 : ℝ) T) :
    PathSpace d m T →L[ℝ] EuclideanSpace ℝ (Fin p) :=
  LinearMap.mkContinuous
    { toFun := fun w => WithLp.toLp 2 fun a => HRS.GF.gfb4_ell m (φ a) (w.at' (ts a))
      map_add' := fun w v => by
        ext a
        simp [pathSpace_at'_add]
      map_smul' := fun c w => by
        ext a
        simp [pathSpace_at'_smul] }
    (evBound m φ)
    (fun w => by
      rw [EuclideanSpace.norm_eq]
      have hS : 0 ≤ ∑ a, ‖HRS.GF.gfb4_ell m (φ a)‖ ^ 2 :=
        Finset.sum_nonneg fun a _ => sq_nonneg _
      have h1 : ∑ a, ‖(HRS.GF.gfb4_ell m (φ a)) (w.at' (ts a))‖ ^ 2 ≤
          (∑ a, ‖HRS.GF.gfb4_ell m (φ a)‖ ^ 2) * ‖w‖ ^ 2 := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun a _ => ?_
        rw [← mul_pow]
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        exact ((HRS.GF.gfb4_ell m (φ a)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (pathSpace_norm_at'_le w _) (norm_nonneg _))
      calc Real.sqrt (∑ a, ‖(HRS.GF.gfb4_ell m (φ a)) (w.at' (ts a))‖ ^ 2)
          ≤ Real.sqrt ((∑ a, ‖HRS.GF.gfb4_ell m (φ a)‖ ^ 2) * ‖w‖ ^ 2) := Real.sqrt_le_sqrt h1
        _ = evBound m φ * ‖w‖ := by
          rw [Real.sqrt_mul hS, Real.sqrt_sq (norm_nonneg _)]
          rfl)

theorem evCLM_apply (m : ℝ) {T : ℝ} {p : ℕ} (φ : Fin p → Torus d → ℝ)
    (ts : Fin p → Set.Icc (0 : ℝ) T) (w : PathSpace d m T) :
    evCLM m φ ts w = WithLp.toLp 2 fun a => HRS.GF.gfb4_ell m (φ a) (w.at' (ts a)) := rfl

theorem evCLM_norm_le (m : ℝ) {T : ℝ} {p : ℕ} (φ : Fin p → Torus d → ℝ)
    (ts : Fin p → Set.Icc (0 : ℝ) T) : ‖evCLM m φ ts‖ ≤ evBound m φ :=
  LinearMap.mkContinuous_norm_le _ (evBound_nonneg m φ) _

theorem evCLM_apply' (m : ℝ) {T : ℝ} {p : ℕ} {φ : Fin p → Torus d → ℝ}
    (hφ : ∀ a, Torus.IsSmooth (φ a)) (ts : Fin p → Set.Icc (0 : ℝ) T) (w : PathSpace d m T) :
    evCLM m φ ts w = WithLp.toLp 2 fun a => NegSobolev.eval (w.at' (ts a)) (φ a) := by
  rw [evCLM_apply]
  congr 1
  funext a
  exact HRS.GF.gfb4_ell_apply (HRS.A33.a33_memSob m (hφ a)) _

/-- The pushforward inequality for the evaluation map. -/
theorem smoothDist_push_le (m : ℝ) {T : ℝ} {p : ℕ} (φ : Fin p → Torus d → ℝ)
    (ts : Fin p → Set.Icc (0 : ℝ) T) (μ ν : Measure (PathSpace d m T))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    smoothDist 2 (μ.map (evCLM m φ ts)) (ν.map (evCLM m φ ts)) ≤
      max 1 (evBound m φ ^ 2) * smoothDist 2 μ ν := by
  refine (Main.smoothDist_map_clm_le (evCLM m φ ts) 2 μ ν).trans ?_
  refine mul_le_mul_of_nonneg_right (max_le_max le_rfl ?_) (smoothDist_nonneg 2 μ ν)
  exact pow_le_pow_left₀ (norm_nonneg _) (evCLM_norm_le m φ ts) 2

theorem ofReal_smoothDist_push_le (m : ℝ) {T : ℝ} {p : ℕ} (φ : Fin p → Torus d → ℝ)
    (ts : Fin p → Set.Icc (0 : ℝ) T) (μ ν : Measure (PathSpace d m T))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {R : ℝ≥0∞}
    (hle : ENNReal.ofReal (smoothDist 2 μ ν) ≤ R) :
    ENNReal.ofReal (smoothDist 2 (μ.map (evCLM m φ ts)) (ν.map (evCLM m φ ts))) ≤
      ENNReal.ofReal (max 1 (evBound m φ ^ 2)) * R := by
  calc ENNReal.ofReal (smoothDist 2 (μ.map (evCLM m φ ts)) (ν.map (evCLM m φ ts)))
      ≤ ENNReal.ofReal (max 1 (evBound m φ ^ 2) * smoothDist 2 μ ν) :=
        ENNReal.ofReal_le_ofReal (smoothDist_push_le m φ ts μ ν)
    _ = ENNReal.ofReal (max 1 (evBound m φ ^ 2)) * ENNReal.ofReal (smoothDist 2 μ ν) :=
        ENNReal.ofReal_mul (le_trans zero_le_one (le_max_left _ _))
    _ ≤ _ := mul_le_mul' le_rfl hle

/-! ### The window, evaluated -/

theorem window_ev_map (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 2 ≤ N) {m : ℝ} (hm2 : (d : ℝ) < 2 * m)
    {T u : ℝ} (hu : 0 ≤ u) (hT : 0 ≤ T) {p : ℕ} (φ : Fin p → Torus d → ℝ)
    (hφ : ∀ a, Torus.IsSmooth (φ a)) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    (t : Fin p → ℝ) (ht : ∀ a, t a ∈ Set.Icc (0 : ℝ) T)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : IsStationaryGibbsFlow P s hs0 hsd V β hβ (u + T) X₀ W X)
    (μ : Measure Ω) (hμ : μ ≪ P) :
    (μ.map (Main.windowZeta m T u P X)).map (evCLM m φ (fun a => ⟨t a, ht a⟩)) =
      μ.map fun ω => retVec d s β V N φ fun a => X (u + t a).toNNReal ω := by
  have hN1 : 1 ≤ N := by omega
  obtain ⟨hstat, hmeas, -⟩ := MD.EQInterp.flow_facts hd hs0 hsd V hV hβ hN P hX
  obtain ⟨hGp, hex⟩ := MD.EQBurnClt.eqclt_gibbs hd hs0 hsd V hV hβ ρβ hρβ hN
  haveI := hGp
  have hwz : AEMeasurable (Main.windowZeta m T u P X) μ :=
    (MD.EQInterp.windowZeta_aemeasurable hd hs0 hsd V hV hβ hN hu hT P hX hm2).mono_ac hμ
  rw [AEMeasurable.map_map_of_aemeasurable (evCLM m φ _).continuous.aemeasurable hwz]
  refine Measure.map_congr ?_
  have hae := MD.EQInterp.windowZeta_cont_ae hd hs0 hsd V hV hβ hN hu hT P hX hm2
  filter_upwards [hμ.ae_le hae] with ω hω
  simp only [Function.comp_apply]
  rw [evCLM_apply' m hφ]
  unfold retVec
  congr 1
  funext a
  rw [MD.EQInterp.windowZeta_at' P X ω hω ⟨t a, ht a⟩]
  have hr : P.map (X (Real.toNNReal (u + t a))) = canonicalGibbs (periodicRiesz d s) V N β :=
    hstat _ (by
      rw [Real.coe_toNNReal _ (by linarith [(ht a).1])]
      linarith [(ht a).2])
  rw [hr]
  exact MD.EQBurnClt.eqclt_eval_zeta hm2 hN1 _ hex (hφ a) _

/-! ### The shifted window -/

theorem ret_shift_of_burn_proof (d : ℕ) (hB : RetBurnShift d) : RetStationaryShift d := by
  intro hd s β hs0 hsd hβ V hV ρβ hρβ hρS hρpos T hT p φ hφ
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set m : ℝ := (d : ℝ) + 3 with hm_def
  have hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m := max_lt (by linarith) (by linarith)
  have hm2 : (d : ℝ) < 2 * m := by linarith
  have hmq : (d : ℝ) + 2 < 2 * m := by linarith
  obtain ⟨C, c, hC, hc, hbd⟩ := hB hd hs0 hsd V hV hβ m hm T hT
  have hK : 0 ≤ max 1 (evBound m φ ^ 2) := le_trans zero_le_one (le_max_left _ _)
  refine ⟨max 1 (evBound m φ ^ 2) * C, c, mul_nonneg hK hC.le, hc, ?_⟩
  intro N hN u hu Ω _ P _ X₀ W X hX h hh hM hh1 t ht
  obtain ⟨Ω', _, P', _, Z, hZ⟩ := Q41.q41_field_exists hd hs0 hsd hβ V hV ρβ hρβ m hmq
  have hbdd := hbd ρβ hρβ u hu N hN P X₀ W X hX P' Z hZ h hh hM hh1
  have hN1 : 1 ≤ N := by omega
  haveI : IsProbabilityMeasure (P.withDensity fun ω => h (X₀ ω)) :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact hh1⟩
  obtain ⟨hstat, hmeas, -⟩ := MD.EQInterp.flow_facts hd hs0 hsd V hV hβ hN P hX
  obtain ⟨hGp, hex⟩ := MD.EQBurnClt.eqclt_gibbs hd hs0 hsd V hV hβ ρβ hρβ hN
  haveI := hGp
  have hwz : AEMeasurable (Main.windowZeta m T u P X) (P.withDensity fun ω => h (X₀ ω)) :=
    (MD.EQInterp.windowZeta_aemeasurable hd hs0 hsd V hV hβ hN hu hT.le P hX hm2).mono_ac
      (withDensity_absolutelyContinuous _ _)
  have hwp : AEMeasurable (Main.windowPath m T 0 Z) P' :=
    (MD.EQGaussWindow.eqgw_fidi hd hs0 hsd V hβ ρβ m T P' Z hZ 0 le_rfl).1
  haveI : IsProbabilityMeasure ((P.withDensity fun ω => h (X₀ ω)).map (Main.windowZeta m T u P X)) :=
    (Measure.isProbabilityMeasure_map_iff hwz).2 inferInstance
  haveI : IsProbabilityMeasure (law P' (Main.windowPath m T 0 Z)) :=
    (Measure.isProbabilityMeasure_map_iff hwp).2 inferInstance
  set ts : Fin p → Set.Icc (0 : ℝ) T := fun a => ⟨t a, ht a⟩ with hts
  have h1 := ofReal_smoothDist_push_le m φ ts _ _ hbdd
  have e1 := window_ev_map hd hs0 hsd V hV hβ hN hm2 hu hT.le φ hφ ρβ hρβ t ht P hX
    (P.withDensity fun ω => h (X₀ ω)) (withDensity_absolutelyContinuous _ _)
  have e2 : (law P' (Main.windowPath m T 0 Z)).map (evCLM m φ ts) =
      ProbabilityTheory.multivariateGaussian 0
        (PDE.stationaryLagCov d s β (PDE.mfData d s hs0 hsd V β hβ) ρβ t φ) := by
    have hfun : (evCLM m φ ts : PathSpace d m T → EuclideanSpace ℝ (Fin p)) =
        MD.EQGaussWindow.eqgwG ts φ := funext fun w => evCLM_apply' m hφ ts w
    have := (MD.EQGaussWindow.eqgw_fidi hd hs0 hsd V hβ ρβ m T P' Z hZ 0 le_rfl).2 p ts φ hφ
    simp only [zero_add] at this
    rw [law, hfun]
    exact this
  rw [e1, e2] at h1
  refine h1.trans ?_
  calc ENNReal.ofReal (max 1 (evBound m φ ^ 2)) *
        (ENNReal.ofReal C * (∫⁻ ω, h (X₀ ω) ^ 2 ∂P) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (Real.exp (-c * u) + Real.sqrt (deltaN d s N)))
      = ENNReal.ofReal (max 1 (evBound m φ ^ 2) * C) * (∫⁻ ω, h (X₀ ω) ^ 2 ∂P) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (Real.sqrt (deltaN d s N) + Real.exp (-c * u)) := by
        rw [ENNReal.ofReal_mul hK, add_comm (Real.exp (-c * u))]
        ring
    _ ≤ _ := le_rfl

/-! ### The window of a linear process -/

theorem windowPath_at'_Icc {m T : ℝ} {Ω' : Type*} (Y : ℝ → Ω' → NegSobolev d m) (ω : Ω')
    (hc : ContinuousOn (fun t => Y t ω) (Set.Icc 0 T)) (τ : Set.Icc (0 : ℝ) T) :
    (Main.windowPath m T 0 Y ω).at' τ = Y τ ω := by
  have hcont : Continuous fun t : Set.Icc (0 : ℝ) T => Y (0 + (t : ℝ)) ω := by
    refine hc.comp_continuous (by fun_prop) (fun t => ?_)
    simpa using t.2
  have h : Main.windowPath m T 0 Y ω = (⟨fun t : Set.Icc (0 : ℝ) T => Y (0 + (t : ℝ)) ω, hcont⟩ :
      C(Set.Icc (0 : ℝ) T, NegSobolev d m)) := by
    unfold Main.windowPath HRS.toPath
    exact dif_pos hcont
  rw [h]
  show Y (0 + (τ : ℝ)) ω = Y τ ω
  rw [zero_add]

theorem aemeasurable_windowPath_Icc {m T : ℝ} {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω')
    (Y : ℝ → Ω' → NegSobolev d m) (hY : ∀ t, Measurable (Y t))
    (hc : ∀ᵐ ω ∂P', ContinuousOn (fun t => Y t ω) (Set.Icc 0 T)) :
    AEMeasurable (Main.windowPath m T 0 Y) P' := by
  have heq : Main.windowPath m T 0 Y =
      fun ω => MD.EQLawPath.eqlaw_pathOf d m T (fun τ => Y (0 + (τ : ℝ)) ω) := by
    funext ω; rfl
  rw [heq]
  refine MD.EQLawPath.eqlaw_aemeasurable_pathOf P' T _ (fun τ => hY _) ?_
  filter_upwards [hc] with ω hω
  refine hω.comp_continuous (by fun_prop) (fun t => ?_)
  simpa using t.2

/-! ### The initial window -/

theorem ret_initial_of_burn_proof (d : ℕ) (hB : RetBurnInit d) : RetStationaryInitial d := by
  intro hd s β hs0 hsd hβ V hV ρβ hρβ hρS hρpos T hT p φ hφ
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set m : ℝ := (d : ℝ) + 3 with hm_def
  have hm : max ((d : ℝ) + 2) (max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2)) < m :=
    max_lt (by linarith) (max_lt (by linarith) (by linarith))
  have hm2 : (d : ℝ) < 2 * m := by linarith
  obtain ⟨C, hC, hbd⟩ := hB hd hs0 hsd V hV hβ ρβ hρβ m hm T hT
  have hK : 0 ≤ max 1 (evBound m φ ^ 2) := le_trans zero_le_one (le_max_left _ _)
  refine ⟨max 1 (evBound m φ ^ 2) * C, mul_nonneg hK hC.le, ?_⟩
  intro N hN Ω _ P _ X₀ W X hX h hh hM hh1 t ht
  obtain ⟨Ω', mΩ', P', hP', Y₀, Y, hsol, hlaw0, hdist⟩ := hbd N hN P X₀ W X hX h hh hM hh1
  have hN1 : 1 ≤ N := by omega
  haveI : IsProbabilityMeasure (P.withDensity fun ω => h (X₀ ω)) :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact hh1⟩
  have hX' : IsStationaryGibbsFlow P s hs0 hsd V β hβ (0 + T) X₀ W X := by
    rw [zero_add]; exact hX
  have hS : IsStrongSolution P (PDE.mfData d s hs0 hsd V β hβ) T X₀ W X := by
    rcases hX.flow.flow with ⟨hh', _⟩ | ⟨h1, _⟩
    · exact hh'
    · exfalso; omega
  obtain ⟨hstat, hmeas, -⟩ := MD.EQInterp.flow_facts hd hs0 hsd V hV hβ hN P hX
  obtain ⟨hGp, hex⟩ := MD.EQBurnClt.eqclt_gibbs hd hs0 hsd V hV hβ ρβ hρβ hN
  haveI := hGp
  have hwz : AEMeasurable (Main.windowZeta m T 0 P X) (P.withDensity fun ω => h (X₀ ω)) :=
    (MD.EQInterp.windowZeta_aemeasurable hd hs0 hsd V hV hβ hN le_rfl hT.le P hX' hm2).mono_ac
      (withDensity_absolutelyContinuous _ _)
  have hwp : AEMeasurable (Main.windowPath m T 0 Y) P' :=
    aemeasurable_windowPath_Icc P' Y hsol.meas hsol.cont
  haveI : IsProbabilityMeasure ((P.withDensity fun ω => h (X₀ ω)).map (Main.windowZeta m T 0 P X)) :=
    (Measure.isProbabilityMeasure_map_iff hwz).2 inferInstance
  haveI : IsProbabilityMeasure (law P' (Main.windowPath m T 0 Y)) :=
    (Measure.isProbabilityMeasure_map_iff hwp).2 inferInstance
  set ts : Fin p → Set.Icc (0 : ℝ) T := fun a => ⟨t a, ht a⟩ with hts
  have h1 := ofReal_smoothDist_push_le m φ ts _ _ hdist
  have e1 := window_ev_map hd hs0 hsd V hV hβ hN hm2 le_rfl hT.le φ hφ ρβ hρβ t ht P hX'
    (P.withDensity fun ω => h (X₀ ω)) (withDensity_absolutelyContinuous _ _)
  simp only [zero_add] at e1
  -- the right-hand side
  have hg : ∀ a, Torus.IsSmooth
      (propagator (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) 0 (t a) (φ a)) :=
    fun a => MD.EQBurnGaussLin.egl_prop_smooth hd hs0 hsd V hV hβ ρβ hρβ (hφ a) (ht a).1
  set ev₀ : NegSobolev d m → EuclideanSpace ℝ (Fin p) := fun y => WithLp.toLp 2 fun a =>
    NegSobolev.eval y (propagator (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) 0 (t a) (φ a))
    with hev₀
  have hev₀m : Measurable ev₀ :=
    (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 fun a =>
      (MD.EQGaussWindow.eqgw_eval_continuous (hg a)).measurable)
  obtain ⟨hind, hlawG⟩ := hsol.gaussian_part p t φ ht hφ
  set G : Ω' → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a =>
    NegSobolev.eval (Y (t a) ω) (φ a) - NegSobolev.eval (Y₀ ω)
      (propagator (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) 0 (t a) (φ a)) with hG
  have hind' : IndepFun G Y₀ P' := hind
  have hlawG' : P'.map G = ProbabilityTheory.multivariateGaussian 0
      (noiseCovMatrix (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) β⁻¹ t φ) := hlawG
  have hY0m : AEMeasurable Y₀ P' := (hsol.meas 0).aemeasurable.congr hsol.init
  have hf : AEMeasurable (ev₀ ∘ Y₀) P' := hev₀m.comp_aemeasurable hY0m
  have hYv : Measurable fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Y (t a) ω) (φ a) :
      EuclideanSpace ℝ (Fin p)) :=
    (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 fun a =>
      (MD.EQGaussWindow.eqgw_eval_continuous (hφ a)).measurable.comp (hsol.meas (t a)))
  have hGm : AEMeasurable G P' := by
    have : G = fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Y (t a) ω) (φ a) :
        EuclideanSpace ℝ (Fin p)) - (ev₀ ∘ Y₀) ω := by
      funext ω; ext a; simp [hG, hev₀]
    rw [this]; exact hYv.aemeasurable.sub hf
  have hindf : IndepFun (ev₀ ∘ Y₀) G P' := hind'.symm.comp hev₀m measurable_id
  have hsum := hindf.map_add_eq_map_conv_map₀ hf hGm
  have e2 : (law P' (Main.windowPath m T 0 Y)).map (evCLM m φ ts) =
      ((P.withDensity fun ω => h (X₀ ω)).map fun ω => retVec d s β V N
          (fun a => propagator (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) 0 (t a) (φ a))
          fun _ => X₀ ω) ∗
        ProbabilityTheory.multivariateGaussian 0
          (noiseCovMatrix (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) β⁻¹ t φ) := by
    rw [law, AEMeasurable.map_map_of_aemeasurable (evCLM m φ ts).continuous.aemeasurable hwp]
    have hcongr : P'.map (evCLM m φ ts ∘ Main.windowPath m T 0 Y) = P'.map (ev₀ ∘ Y₀ + G) := by
      refine Measure.map_congr ?_
      filter_upwards [hsol.cont] with ω hω
      simp only [Function.comp_apply]
      rw [evCLM_apply' m hφ]
      ext a
      simp only [Pi.add_apply, Function.comp_apply, hG, hev₀, PiLp.add_apply]
      rw [windowPath_at'_Icc Y ω hω (ts a)]
      ring
    rw [hcongr, hsum, hlawG']
    congr 1
    rw [← AEMeasurable.map_map_of_aemeasurable hev₀m.aemeasurable hY0m, hlaw0]
    have h0 : P.map (X 0) = canonicalGibbs (periodicRiesz d s) V N β :=
      hstat 0 (by simpa using hT.le)
    have hζ : Measurable fun ω => zetaE m (P.map (X 0)) (X 0 ω) := by
      rw [h0]
      exact (MD.EQLawPath.eqlaw_continuous_zetaE hm2 hN1 _).measurable.comp (hmeas 0)
    rw [AEMeasurable.map_map_of_aemeasurable hev₀m.aemeasurable hζ.aemeasurable]
    refine Measure.map_congr ?_
    filter_upwards [(withDensity_absolutelyContinuous P _).ae_le hS.init] with ω hω
    simp only [Function.comp_apply, hev₀]
    unfold retVec
    congr 1
    funext a
    rw [h0, ← hω]
    exact MD.EQBurnClt.eqclt_eval_zeta hm2 hN1 _ hex (hg a) _
  rw [e1, e2] at h1
  refine h1.trans ?_
  calc ENNReal.ofReal (max 1 (evBound m φ ^ 2)) *
        (ENNReal.ofReal C * (∫⁻ ω, h (X₀ ω) ^ 2 ∂P) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (Real.sqrt (deltaN d s N)))
      = ENNReal.ofReal (max 1 (evBound m φ ^ 2) * C) * (∫⁻ ω, h (X₀ ω) ^ 2 ∂P) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal (Real.sqrt (deltaN d s N)) := by
        rw [ENNReal.ofReal_mul hK]
        ring
    _ ≤ _ := le_rfl

end HRS.ME.Ret

end
