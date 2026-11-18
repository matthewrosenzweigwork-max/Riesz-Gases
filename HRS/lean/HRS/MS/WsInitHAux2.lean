import HRS.MS.WsInitHAux1

/-!
# S21H packet H, part 2: `W_1` between two coordinate laws in `ℝ^p` from a derivative-only comparison

Setting: `E` a normed space, `μ, γ` probability measures on `E` with finite second moments, `c : E →L ℝ^p` a coordinate map with `‖c‖ ≤ 1`,
and the DERIVATIVE-ONLY comparison (`S21hDerivComp`; this is the fourth conjunct of the merged `StaticFieldConclusion`, with
`η = √δ_N`, `A₁ = C S`, `A₂ = C S²`): for every `C²` function `F` on `E` with `‖DF‖ ≤ D₁`, `‖D²F‖ ≤ D₂`,
`|∫F dμ - ∫F dγ| ≤ η (A₁ D₁ + A₂ D₂)` (both integrals exist).

`s21h_w1_coord`: `W_1^{ℝ^p}(c_*μ, c_*γ) ≤ 2 ε √p + η (A₁ + A₂/ε)` for every `ε > 0`.  The Gaussian smoothing of a
clamped 1-Lipschitz test function costs `ε √p` in value and `1/ε` in the Hessian (dimension-free: part 1), the clamping costs
`(∫‖cv‖² dμ + ∫‖cv‖² dγ)/(4R)` and is removed by `R → ∞`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal Real

namespace HRS.MS.S21

/-- The derivative-only comparison of `μ` and `γ` at scale `η` (constants `A₁, A₂`). -/
def S21hDerivComp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    (μ γ : Measure E) (η A₁ A₂ : ℝ) : Prop :=
  ∀ F : E → ℝ, ContDiff ℝ 2 F → ∀ D₁ D₂ : ℝ, (∀ z, ‖fderiv ℝ F z‖ ≤ D₁) →
    (∀ z, ‖iteratedFDeriv ℝ 2 F z‖ ≤ D₂) →
    Integrable F μ ∧ Integrable F γ ∧ |∫ z, F z ∂μ - ∫ z, F z ∂γ| ≤ η * (A₁ * D₁ + A₂ * D₂)

variable {p : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin p)

section Coord

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Derivative bounds of a smooth function composed with a coordinate map of norm `≤ 1`. -/
theorem s21h_comp_bounds (c : E →L[ℝ] 𝔼) (hc : ‖c‖ ≤ 1) {g : 𝔼 → ℝ} (hg : ContDiff ℝ 2 g) {M1 M2 : ℝ}
    (h1 : ∀ z, ‖fderiv ℝ g z‖ ≤ M1) (h2 : ∀ z, ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ M2) :
    ContDiff ℝ 2 (g ∘ c) ∧ (∀ v, ‖fderiv ℝ (g ∘ c) v‖ ≤ M1) ∧
      (∀ v, ‖iteratedFDeriv ℝ 2 (g ∘ c) v‖ ≤ M2) := by
  have hM1 : 0 ≤ M1 := (norm_nonneg (fderiv ℝ g 0)).trans (h1 0)
  have hM2 : 0 ≤ M2 := (norm_nonneg (fderiv ℝ (fderiv ℝ g) 0)).trans (h2 0)
  refine ⟨hg.comp c.contDiff, fun v => ?_, fun v => ?_⟩
  · rw [fderiv_comp v (hg.differentiable (by norm_num) _) c.differentiableAt]
    simp only [ContinuousLinearMap.fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    calc ‖fderiv ℝ g (c v)‖ * ‖c‖ ≤ M1 * 1 := mul_le_mul (h1 _) hc (norm_nonneg _) hM1
      _ = M1 := mul_one _
  · rw [c.iteratedFDeriv_comp_right hg (v) (by exact_mod_cast le_rfl)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have hg2 : ‖iteratedFDeriv ℝ 2 g (c v)‖ ≤ M2 := by
      rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]; exact h2 _
    calc ‖iteratedFDeriv ℝ 2 g (c v)‖ * ∏ _i : Fin 2, ‖c‖ ≤ M2 * 1 := by
          refine mul_le_mul hg2 ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _) hM2
          rw [Fin.prod_univ_two]
          nlinarith [norm_nonneg c]
      _ = M2 := mul_one _

end Coord


/-- Smooth approximation of a 1-Lipschitz function on `ℝ^p`: a clamped Gaussian smoothing with dimension-free Hessian. -/
theorem s21h_smooth_approx {h : 𝔼 → ℝ} (hh : LipschitzWith 1 h) {ε Rc : ℝ} (hε : 0 < ε) (hRc : 0 < Rc) :
    ∃ g : 𝔼 → ℝ, ContDiff ℝ 2 g ∧ (∀ y, ‖fderiv ℝ g y‖ ≤ 1) ∧ (∀ y, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ 1 / ε) ∧
      (∀ y, |g y| ≤ Rc) ∧ ∀ y, |h y - h 0 - g y| ≤ ‖y‖ ^ 2 / (4 * Rc) + ε * Real.sqrt p := by
  set u : 𝔼 → ℝ := fun x => h x - h 0 with hu_def
  have hu : LipschitzWith 1 u := LipschitzWith.of_dist_le_mul fun x y => by
    simpa [u, Real.dist_eq] using hh.dist_le_mul x y
  set f : 𝔼 → ℝ := fun x => max (-Rc) (min Rc (u x)) with hf_def
  have hfL : LipschitzWith 1 f := (hu.const_min Rc).const_max (-Rc)
  have hfc : Continuous f := hfL.continuous
  have hfR : ∀ y, |f y| ≤ Rc := fun y => by
    rw [abs_le]; simp only [f]; constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have huf : ∀ x, |u x - f x| ≤ ‖x‖ ^ 2 / (4 * Rc) := fun x => by
    refine clamp_err hRc ?_
    have := hu.dist_le_mul x 0
    simpa [u, Real.dist_eq] using this
  refine ⟨gsmooth ε f, contDiff_gsmooth hε hfc hfR, norm_fderiv_gsmooth_le hε hfc hfR hfL,
    s21h_norm_fderiv_fderiv_gsmooth_le hε hfc hfR hfL, abs_gsmooth_le hε hfc hfR, fun y => ?_⟩
  have h1 := huf y
  have h2 : |f y - gsmooth ε f y| ≤ ε * Real.sqrt p := by
    rw [abs_sub_comm]; exact gsmooth_sub_le hε hfc hfR hfL y
  have e : h y - h 0 - gsmooth ε f y = (u y - f y) + (f y - gsmooth ε f y) := by simp [u]
  rw [e]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

section Test

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The per-test estimate: for a 1-Lipschitz `h` on `ℝ^p`. -/
theorem s21h_test_bound (μ γ : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]
    (hμ2 : MemLp id 2 μ) (hγ2 : MemLp id 2 γ) (c : E →L[ℝ] 𝔼) (hc : ‖c‖ ≤ 1) {η A₁ A₂ : ℝ}
    (hcomp : S21hDerivComp μ γ η A₁ A₂) {h : 𝔼 → ℝ} (hh : LipschitzWith 1 h) {ε Rc : ℝ} (hε : 0 < ε)
    (hRc : 0 < Rc) :
    ∫ v, h (c v) ∂μ - ∫ v, h (c v) ∂γ ≤
      ((∫ v, ‖c v‖ ^ 2 ∂μ) + ∫ v, ‖c v‖ ^ 2 ∂γ) / (4 * Rc) + 2 * ε * Real.sqrt p +
        η * (A₁ + A₂ / ε) := by
  obtain ⟨g, hg2, hg1, hg2', hgb, hgh⟩ := s21h_smooth_approx (p := p) hh hε hRc
  obtain ⟨hGc, hG1, hG2⟩ := s21h_comp_bounds c hc hg2 hg1 hg2'
  obtain ⟨iGμ, iGγ, hGd⟩ := hcomp (g ∘ c) hGc 1 (1 / ε) hG1 (by simpa using hG2)
  have hcm : Measurable c := c.continuous.measurable
  -- integrability of the pieces
  have hnorm_le : ∀ v, ‖c v‖ ≤ ‖v‖ := fun v => (c.le_opNorm v).trans (by
    nlinarith [norm_nonneg v, norm_nonneg c])
  have isq : ∀ ν : Measure E, MemLp id 2 ν → Integrable (fun v => ‖c v‖ ^ 2) ν := fun ν hν => by
    have hν' : Integrable (fun v => ‖v‖ ^ 2) ν := hν.integrable_norm_pow two_ne_zero
    refine hν'.mono' (by fun_prop) (ae_of_all _ fun v => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hnorm_le v) 2
  have iab : ∀ (ν : Measure E) [IsProbabilityMeasure ν], MemLp id 2 ν → Integrable (fun v => ‖c v‖) ν :=
    fun ν _ hν => by
    have hν' : Integrable (fun v => ‖v‖) ν := (hν.integrable one_le_two).norm
    exact hν'.mono' (by fun_prop) (ae_of_all _ fun v => by
      rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hnorm_le v)
  have ih : ∀ (ν : Measure E) [IsProbabilityMeasure ν], MemLp id 2 ν → Integrable (fun v => h (c v)) ν :=
    fun ν _ hν => integrable_lip_comp ν hh hcm (iab ν hν)
  -- one-sided bounds
  have side : ∀ (ν : Measure E) [IsProbabilityMeasure ν], MemLp id 2 ν → Integrable (fun v => g (c v)) ν →
      |(∫ v, h (c v) ∂ν) - h 0 - ∫ v, g (c v) ∂ν| ≤ (∫ v, ‖c v‖ ^ 2 ∂ν) / (4 * Rc) + ε * Real.sqrt p := by
    intro ν _ hν2 ig
    have i1 := ih ν hν2
    have e : (∫ v, h (c v) ∂ν) - h 0 - ∫ v, g (c v) ∂ν = ∫ v, (h (c v) - h 0 - g (c v)) ∂ν := by
      have e1 := integral_sub (μ := ν) (f := fun v => h (c v) - h 0) (g := fun v => g (c v))
        (i1.sub (integrable_const _)) ig
      have e2 := integral_sub (μ := ν) (f := fun v => h (c v)) (g := fun _ => h 0) i1 (integrable_const _)
      rw [e1, e2]
      simp
    rw [e]
    have ib : Integrable (fun v => ‖c v‖ ^ 2 / (4 * Rc) + ε * Real.sqrt p) ν :=
      ((isq ν hν2).div_const _).add (integrable_const _)
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ v, |h (c v) - h 0 - g (c v)| ∂ν ≤ ∫ v, (‖c v‖ ^ 2 / (4 * Rc) + ε * Real.sqrt p) ∂ν := by
          refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) ib (ae_of_all _ fun v => hgh _)
      _ = (∫ v, ‖c v‖ ^ 2 ∂ν) / (4 * Rc) + ε * Real.sqrt p := by
          rw [integral_add ((isq ν hν2).div_const _) (integrable_const _), integral_div]
          simp
  have sμ := side μ hμ2 iGμ
  have sγ := side γ hγ2 iGγ
  have hd := (le_abs_self _).trans hGd
  simp only [Function.comp] at hd
  have a1 := (abs_le.1 sμ).2
  have a2 := (abs_le.1 sγ).1
  have e3 : ((∫ v, ‖c v‖ ^ 2 ∂μ) + ∫ v, ‖c v‖ ^ 2 ∂γ) / (4 * Rc) =
      (∫ v, ‖c v‖ ^ 2 ∂μ) / (4 * Rc) + (∫ v, ‖c v‖ ^ 2 ∂γ) / (4 * Rc) := add_div _ _ _
  have e4 : η * (A₁ * 1 + A₂ * (1 / ε)) = η * (A₁ + A₂ / ε) := by ring
  rw [e3, ← e4]
  nlinarith [a1, a2, hd]


/-- The elimination of the clamping level. -/
theorem s21h_dual_bound (μ γ : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]
    (hμ2 : MemLp id 2 μ) (hγ2 : MemLp id 2 γ) (c : E →L[ℝ] 𝔼) (hc : ‖c‖ ≤ 1) {η A₁ A₂ : ℝ}
    (hcomp : S21hDerivComp μ γ η A₁ A₂) {h : 𝔼 → ℝ} (hh : LipschitzWith 1 h) {ε : ℝ} (hε : 0 < ε) :
    ∫ v, h (c v) ∂μ - ∫ v, h (c v) ∂γ ≤ 2 * ε * Real.sqrt p + η * (A₁ + A₂ / ε) := by
  set M : ℝ := (∫ v, ‖c v‖ ^ 2 ∂μ) + ∫ v, ‖c v‖ ^ 2 ∂γ with hM
  have hM0 : 0 ≤ M := add_nonneg (integral_nonneg fun _ => by positivity) (integral_nonneg fun _ => by positivity)
  refine le_of_forall_pos_le_add fun θ hθ => ?_
  have h1 := s21h_test_bound μ γ hμ2 hγ2 c hc hcomp hh hε (Rc := (M + 1) / (4 * θ)) (by positivity)
  have h2 : M / (4 * ((M + 1) / (4 * θ))) ≤ θ := by
    rw [div_le_iff₀ (by positivity)]
    have : θ * (4 * ((M + 1) / (4 * θ))) = M + 1 := by field_simp
    linarith
  linarith

/-- `W_1` of the coordinate laws in `ℝ^p`: `2 ε √p + η (A₁ + A₂/ε)` for every `ε > 0`. -/
theorem s21h_w1_coord (μ γ : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]
    (hμ2 : MemLp id 2 μ) (hγ2 : MemLp id 2 γ) (c : E →L[ℝ] 𝔼) (hc : ‖c‖ ≤ 1) {η A₁ A₂ : ℝ}
    (hcomp : S21hDerivComp μ γ η A₁ A₂) {ε : ℝ} (hε : 0 < ε) :
    wassersteinE 1 (μ.map c) (γ.map c) ≤ ENNReal.ofReal (2 * ε * Real.sqrt p + η * (A₁ + A₂ / ε)) := by
  have hcm : Measurable c := c.continuous.measurable
  set P : Measure (E × E) := μ.prod γ with hP
  have hm1 : MemLp (fun v => c v) 2 μ := c.comp_memLp' hμ2
  have hm2 : MemLp (fun v => c v) 2 γ := c.comp_memLp' hγ2
  have hX2 : MemLp (fun q : E × E => c q.1) 2 P :=
    hm1.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := γ))
  have hY2 : MemLp (fun q : E × E => c q.2) 2 P :=
    hm2.comp_measurePreserving (measurePreserving_snd (μ := μ) (ν := γ))
  have hd := wassersteinE_one_le_of_dual P (fun q : E × E => c q.1) (fun q : E × E => c q.2)
    (hcm.comp measurable_fst) (hcm.comp measurable_snd) hX2 hY2
    (2 * ε * Real.sqrt p + η * (A₁ + A₂ / ε)) (by
      intro h hh
      have e1 : ∫ q, h (c q.1) ∂P = ∫ v, h (c v) ∂μ := by
        have := integral_map (μ := P) (φ := Prod.fst) measurable_fst.aemeasurable
          (f := fun v => h (c v)) (hh.continuous.comp c.continuous).aestronglyMeasurable
        rw [← this, hP, Measure.map_fst_prod]; simp
      have e2 : ∫ q, h (c q.2) ∂P = ∫ v, h (c v) ∂γ := by
        have := integral_map (μ := P) (φ := Prod.snd) measurable_snd.aemeasurable
          (f := fun v => h (c v)) (hh.continuous.comp c.continuous).aestronglyMeasurable
        rw [← this, hP, Measure.map_snd_prod]; simp
      rw [e1, e2]
      exact s21h_dual_bound μ γ hμ2 hγ2 c hc hcomp hh hε)
  have e1 : law P (fun q : E × E => c q.1) = μ.map c := by
    show P.map (fun q : E × E => c q.1) = _
    rw [hP, show (fun q : E × E => c q.1) = c ∘ Prod.fst from rfl,
      ← Measure.map_map hcm measurable_fst, Measure.map_fst_prod]; simp
  have e2 : law P (fun q : E × E => c q.2) = γ.map c := by
    show P.map (fun q : E × E => c q.2) = _
    rw [hP, show (fun q : E × E => c q.2) = c ∘ Prod.snd from rfl,
      ← Measure.map_map hcm measurable_snd, Measure.map_snd_prod]; simp
  rw [e1, e2] at hd
  exact hd

end Test

end HRS.MS.S21
