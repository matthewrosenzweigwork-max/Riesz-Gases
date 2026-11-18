/-
# HRS.Equilibrium.PairMomentsLemmaD -- the gradient of a canonical kernel is canonical a.e. (EQ-01b)
-/
import HRS.Equilibrium.PairMomentsGrad
import HRS.Equilibrium.PairMomentsEnv

open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.PairMom

open HRS HRS.External HRS.Quad

variable {d : ℕ} {s : ℝ}

section Leb

theorem ae_zero_of_integral_zero {g : ℝ → ℝ} (hg : LocallyIntegrable g volume)
    (h : ∀ a b : ℝ, a < b → ∫ x in a..b, g x = 0) : ∀ᵐ x : ℝ, g x = 0 := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average (μ := (volume : Measure ℝ)) hg 1] with x hx
  have hδ : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => by
        show (0 : ℝ) < _
        positivity⟩
  have hx' := hx (l := atTop) (fun _ : ℕ => x) (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) hδ
    (Eventually.of_forall fun n => by
      rw [Metric.mem_closedBall, dist_self, one_mul]; positivity)
  have hz : ∀ n : ℕ, ⨍ y in Metric.closedBall x ((1 : ℝ) / ((n : ℝ) + 1)), g y = 0 := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    rw [Real.closedBall_eq_Icc, MeasureTheory.setAverage_eq, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith), h _ _ (by linarith), smul_zero]
  simp_rw [hz] at hx'
  exact tendsto_nhds_unique hx' tendsto_const_nhds |>.symm |>.symm

end Leb

section Line

theorem mk_zero' : Torus.mk (0 : Euc d) = 0 := by
  funext i
  simp [Torus.mk]

theorem fderiv_lift2_congr_left (ψ : Torus d → Torus d → ℝ) {z z' : Euc d} (h : Torus.mk z' = Torus.mk z)
    (b : Euc d) : fderiv ℝ (lift2 ψ) (z', b) = fderiv ℝ (lift2 ψ) (z, b) := by
  have hδ : Torus.mk (z' - z) = 0 := by
    funext i
    have := congrFun h i
    simp only [Torus.mk, Pi.zero_apply] at this ⊢
    rw [PiLp.sub_apply, AddCircle.coe_sub, this, sub_self]
  have hshift : (fun p : Euc d × Euc d => lift2 ψ (p + (z' - z, 0))) = lift2 ψ := by
    funext p
    simp only [lift2, Prod.fst_add, Prod.snd_add, add_zero]
    rw [mk_add', hδ, add_zero]
  have := fderiv_comp_add_right (𝕜 := ℝ) (f := lift2 ψ) (z' - z, (0 : Euc d)) (x := (z, b))
  rw [hshift] at this
  rw [this]
  congr 1
  simp

theorem line_mk_ne {x0 y : Torus d} {m : Fin d} (hy : ∃ j, j ≠ m ∧ y j ≠ x0 j) (τ : ℝ) :
    x0 + Torus.mk (τ • (EuclideanSpace.single m (1 : ℝ) : Euc d)) ≠ y := by
  obtain ⟨j, hjm, hj⟩ := hy
  intro h
  apply hj
  have := congrFun h j
  simp only [Pi.add_apply, Torus.mk] at this
  have e : (τ • (EuclideanSpace.single m (1 : ℝ) : Euc d)) j = 0 := by
    simp [EuclideanSpace.single_apply, hjm]
  rw [e] at this
  simpa using this.symm

theorem hasDerivAt_line {ψ : Torus d → Torus d → ℝ}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) (x0 y : Torus d) (m : Fin d)
    (hne : ∀ τ : ℝ, x0 + Torus.mk (τ • (EuclideanSpace.single m (1 : ℝ) : Euc d)) ≠ y) (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => ψ (x0 + Torus.mk (τ • (EuclideanSpace.single m (1 : ℝ) : Euc d))) y)
      (gradK ψ m (x0 + Torus.mk (τ • (EuclideanSpace.single m (1 : ℝ) : Euc d))) y) τ := by
  set e : Euc d := EuclideanSpace.single m (1 : ℝ) with he
  have hfun : (fun τ : ℝ => ψ (x0 + Torus.mk (τ • e)) y) =
      (lift2 ψ) ∘ (fun τ : ℝ => (Torus.rep x0 + τ • e, Torus.rep y)) := by
    funext τ
    simp only [Function.comp]
    rw [lift2_shift]
  have hpath : HasDerivAt (fun τ : ℝ => (Torus.rep x0 + τ • e, Torus.rep y)) (e, (0 : Euc d)) τ := by
    have h1 := ((hasDerivAt_id τ).smul_const e).const_add (Torus.rep x0)
    simp only [id, one_smul] at h1
    exact h1.prodMk (hasDerivAt_const τ _)
  have hmk : Torus.mk (Torus.rep x0 + τ • e) = x0 + Torus.mk (τ • e) := by
    rw [mk_add', Torus.mk_rep]
  have hp : (Torus.rep x0 + τ • e, Torus.rep y) ∈ offDiag d := by
    show Torus.mk (Torus.rep x0 + τ • e) ≠ Torus.mk (Torus.rep y)
    rw [hmk, Torus.mk_rep]
    exact hne τ
  have hd := (differentiableAt_lift2 hsm hp).hasFDerivAt
  have hcomp := hd.comp_hasDerivAt τ hpath
  rw [hfun]
  have hg : gradK ψ m (x0 + Torus.mk (τ • e)) y = fderiv ℝ (lift2 ψ) (Torus.rep x0 + τ • e, Torus.rep y) (e, 0) := by
    unfold gradK
    rw [fderiv_lift2_congr_left ψ (z := Torus.rep x0 + τ • e) (by rw [Torus.mk_rep, hmk])]
  rw [hg]
  exact hcomp

end Line

section RowBounds

theorem gradK_bound {ψ : Torus d → Torus d → ℝ} {K : ℝ}
    (hgrad : ∀ p ∈ offDiag d, ‖fderiv ℝ (lift2 ψ) p‖ ≤
      K * (1 + rTrunc (Torus.mk p.1) (Torus.mk p.2) ^ (1 - s)))
    (m : Fin d) {x y : Torus d} (hxy : x ≠ y) : |gradK ψ m x y| ≤ K * gradEnv s x y := by
  have hp : (Torus.rep x, Torus.rep y) ∈ offDiag d := by
    show Torus.mk (Torus.rep x) ≠ Torus.mk (Torus.rep y)
    rw [Torus.mk_rep, Torus.mk_rep]; exact hxy
  have h1 := hgrad _ hp
  simp only [Torus.mk_rep] at h1
  have h2 : ‖((EuclideanSpace.single m (1 : ℝ) : Euc d), (0 : Euc d))‖ = 1 := by
    rw [Prod.norm_def]
    simp
  calc |gradK ψ m x y| = ‖fderiv ℝ (lift2 ψ) (Torus.rep x, Torus.rep y) (EuclideanSpace.single m 1, 0)‖ := by
        rw [Real.norm_eq_abs]; rfl
    _ ≤ ‖fderiv ℝ (lift2 ψ) (Torus.rep x, Torus.rep y)‖ * ‖((EuclideanSpace.single m (1 : ℝ) : Euc d), (0 : Euc d))‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ K * gradEnv s x y := by rw [h2, mul_one]; exact h1

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

theorem lintegral_gradK_le {ψ : Torus d → Torus d → ℝ} {K : ℝ}
    (hgrad : ∀ p ∈ offDiag d, ‖fderiv ℝ (lift2 ψ) p‖ ≤
      K * (1 + rTrunc (Torus.mk p.1) (Torus.mk p.2) ^ (1 - s)))
    (hatom : ∀ z : Torus d, μ {z} = 0) (m : Fin d) {BA : ℝ}
    (hBA : ∀ x, ∫⁻ y, ENNReal.ofReal (gradEnv s x y) ∂μ ≤ ENNReal.ofReal BA) (x : Torus d) :
    ∫⁻ y, ‖gradK ψ m x y‖ₑ ∂μ ≤ ENNReal.ofReal |K| * ENNReal.ofReal BA := by
  have hae : ∀ᵐ y ∂μ, y ≠ x := HRS.External.PoleVar.ae_ne_pt hatom x
  calc ∫⁻ y, ‖gradK ψ m x y‖ₑ ∂μ ≤ ∫⁻ y, ENNReal.ofReal |K| * ENNReal.ofReal (gradEnv s x y) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with y hy
        rw [← ENNReal.ofReal_mul (abs_nonneg _), Real.enorm_eq_ofReal_abs]
        refine ENNReal.ofReal_le_ofReal ?_
        calc |gradK ψ m x y| ≤ K * gradEnv s x y := gradK_bound hgrad m (Ne.symm hy)
          _ ≤ |K| * gradEnv s x y := mul_le_mul_of_nonneg_right (le_abs_self K) (gradEnv_nonneg s x y)
    _ = ENNReal.ofReal |K| * ∫⁻ y, ENNReal.ofReal (gradEnv s x y) ∂μ := by
        rw [lintegral_const_mul']; exact ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul' le_rfl (hBA x)

theorem integrable_gradK {ψ : Torus d → Torus d → ℝ} {K : ℝ}
    (hgrad : ∀ p ∈ offDiag d, ‖fderiv ℝ (lift2 ψ) p‖ ≤
      K * (1 + rTrunc (Torus.mk p.1) (Torus.mk p.2) ^ (1 - s)))
    (hatom : ∀ z : Torus d, μ {z} = 0) (m : Fin d) {BA : ℝ}
    (hBA : ∀ x, ∫⁻ y, ENNReal.ofReal (gradEnv s x y) ∂μ ≤ ENNReal.ofReal BA) (x : Torus d) :
    Integrable (gradK ψ m x) μ := by
  refine ⟨((measurable_gradK ψ m).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable, ?_⟩
  exact lt_of_le_of_lt (lintegral_gradK_le hgrad hatom m hBA x)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

theorem abs_integral_gradK_le {ψ : Torus d → Torus d → ℝ} {K : ℝ}
    (hgrad : ∀ p ∈ offDiag d, ‖fderiv ℝ (lift2 ψ) p‖ ≤
      K * (1 + rTrunc (Torus.mk p.1) (Torus.mk p.2) ^ (1 - s)))
    (hatom : ∀ z : Torus d, μ {z} = 0) (m : Fin d) {BA : ℝ} (hBA0 : 0 ≤ BA)
    (hBA : ∀ x, ∫⁻ y, ENNReal.ofReal (gradEnv s x y) ∂μ ≤ ENNReal.ofReal BA) (x : Torus d) :
    |∫ y, gradK ψ m x y ∂μ| ≤ |K| * BA := by
  have h1 := norm_integral_le_lintegral_norm (μ := μ) (gradK ψ m x)
  rw [Real.norm_eq_abs] at h1
  refine h1.trans (ENNReal.toReal_le_of_le_ofReal (by positivity) ?_)
  simp_rw [ofReal_norm_eq_enorm]
  refine (lintegral_gradK_le hgrad hatom m hBA x).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]

end RowBounds

section Fubini

theorem volume_coord_null (j : Fin d) (a : UnitAddCircle) :
    (volume : Measure (Torus d)) {y : Torus d | y j = a} = 0 := by
  have : {y : Torus d | y j = a} = Set.pi Set.univ (fun i => if i = j then {a} else Set.univ) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h i
      by_cases hi : i = j
      · subst hi; simpa using h
      · simp [hi]
    · intro h
      have := h j
      simpa using this
  rw [this]
  show (Measure.pi fun _ : Fin d => (volume : Measure UnitAddCircle)) _ = 0
  rw [Measure.pi_pi]
  refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
  rw [if_pos rfl]
  exact volume_singleton_circle a

theorem measure_bad_line_null (hd : 2 ≤ d) (μ : Measure (Torus d)) (hμ : μ ≪ volume) (x0 : Torus d) (m : Fin d) :
    μ {y : Torus d | ¬ ∃ j, j ≠ m ∧ y j ≠ x0 j} = 0 := by
  obtain ⟨j, hj⟩ : ∃ j : Fin d, j ≠ m := by
    by_cases h0 : m = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, by rw [h0]; simp [Fin.ext_iff]⟩
    · exact ⟨⟨0, by omega⟩, fun h => h0 h.symm⟩
  refine hμ (measure_mono_null ?_ (volume_coord_null j (x0 j)))
  intro y hy
  simp only [Set.mem_ofPred_eq, not_exists, not_and, not_not] at hy ⊢
  exact hy j hj

end Fubini

section LineIntegral

theorem integral_norm_gradK_le {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {ψ : Torus d → Torus d → ℝ} {K : ℝ}
    (hgrad : ∀ p ∈ offDiag d, ‖fderiv ℝ (lift2 ψ) p‖ ≤
      K * (1 + rTrunc (Torus.mk p.1) (Torus.mk p.2) ^ (1 - s)))
    (hatom : ∀ z : Torus d, μ {z} = 0) (m : Fin d) {BA : ℝ} (hBA0 : 0 ≤ BA)
    (hBA : ∀ x, ∫⁻ y, ENNReal.ofReal (gradEnv s x y) ∂μ ≤ ENNReal.ofReal BA) (x : Torus d) :
    ∫ y, ‖gradK ψ m x y‖ ∂μ ≤ |K| * BA := by
  have hmx : AEStronglyMeasurable (gradK ψ m x) μ :=
    ((measurable_gradK ψ m).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  rw [integral_norm_eq_lintegral_enorm hmx]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  refine (lintegral_gradK_le hgrad hatom m hBA x).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]

theorem line_integral_zero (hd : 2 ≤ d) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {ψ : Torus d → Torus d → ℝ}
    {K : ℝ}
    (hcan : ∀ x, Integrable (ψ x) (withDensityReal ρ) ∧ ∫ y, ψ x y ∂(withDensityReal ρ) = 0)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d))
    (hgrad : ∀ p ∈ offDiag d, ‖fderiv ℝ (lift2 ψ) p‖ ≤
      K * (1 + rTrunc (Torus.mk p.1) (Torus.mk p.2) ^ (1 - s)))
    {BA : ℝ} (hBA0 : 0 ≤ BA)
    (hBA : ∀ x, ∫⁻ y, ENNReal.ofReal (gradEnv s x y) ∂(withDensityReal ρ) ≤ ENNReal.ofReal BA)
    (m : Fin d) (x0 : Torus d) {t : ℝ} (ht : 0 < t) :
    ∫ τ in Set.Ioc 0 t, (∫ y, gradK ψ m (x0 + Torus.mk (τ • (EuclideanSpace.single m (1 : ℝ) : Euc d))) y
      ∂(withDensityReal ρ)) = 0 := by
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
  have hac : withDensityReal ρ ≪ volume := withDensity_absolutelyContinuous _ _
  set e : Euc d := EuclideanSpace.single m (1 : ℝ) with he
  set F : ℝ → Torus d → ℝ := fun τ y => gradK ψ m (x0 + Torus.mk (τ • e)) y with hF
  have hℓ : Measurable fun τ : ℝ => x0 + Torus.mk (τ • e) :=
    measurable_const.add (Torus.continuous_mk.comp (continuous_id.smul continuous_const)).measurable
  have hFm : Measurable (Function.uncurry F) :=
    (measurable_gradK ψ m).comp ((hℓ.comp measurable_fst).prodMk measurable_snd)
  have hFint : Integrable (Function.uncurry F) ((volume.restrict (Set.Ioc 0 t)).prod (withDensityReal ρ)) := by
    rw [integrable_prod_iff hFm.aestronglyMeasurable]
    have hbd : ∀ τ : ℝ, ∫ y, ‖F τ y‖ ∂(withDensityReal ρ) ≤ |K| * BA := fun τ =>
      integral_norm_gradK_le hgrad hatom m hBA0 hBA (x0 + Torus.mk (τ • e))
    have hmeas : AEStronglyMeasurable (fun τ : ℝ => ∫ y, ‖Function.uncurry F (τ, y)‖ ∂(withDensityReal ρ))
        (volume.restrict (Set.Ioc 0 t)) :=
      (hFm.norm.stronglyMeasurable.integral_prod_right' (ν := withDensityReal ρ)).aestronglyMeasurable
    refine ⟨Eventually.of_forall fun τ => ?_, ?_⟩
    · exact integrable_gradK hgrad hatom m hBA (x0 + Torus.mk (τ • e))
    · refine Integrable.mono' (g := fun _ => |K| * BA) (integrable_const _) hmeas (Eventually.of_forall fun τ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
      exact hbd τ
  have hsec : ∀ᵐ y ∂(withDensityReal ρ), Integrable (fun τ => F τ y) (volume.restrict (Set.Ioc 0 t)) :=
    hFint.prod_left_ae
  have hgood : ∀ᵐ y ∂(withDensityReal ρ), ∃ j, j ≠ m ∧ y j ≠ x0 j :=
    ae_iff.2 (measure_bad_line_null hd _ hac x0 m)
  have hFTC : ∀ᵐ y ∂(withDensityReal ρ), ψ (x0 + Torus.mk (t • e)) y - ψ x0 y =
      ∫ τ in Set.Ioc 0 t, F τ y := by
    filter_upwards [hsec, hgood] with y hs hg
    have hne := line_mk_ne (m := m) hg
    have hint : IntervalIntegrable (fun τ => F τ y) volume 0 t :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).2 hs
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
      (fun τ _ => hasDerivAt_line hsm x0 y m hne τ) hint
    rw [← intervalIntegral.integral_of_le ht.le, this]
    simp [mk_zero', he]
  have h0 : ∫ y, (ψ (x0 + Torus.mk (t • e)) y - ψ x0 y) ∂(withDensityReal ρ) = 0 := by
    rw [integral_sub (hcan _).1 (hcan _).1, (hcan _).2, (hcan _).2, sub_zero]
  rw [integral_congr_ae hFTC] at h0
  exact (integral_integral_swap hFint).trans h0

end LineIntegral

section LemmaD

/-- Along every line in direction `e_m` the row mean `c_m` vanishes a.e. -/
theorem gradK_line_ae_zero (hd : 2 ≤ d) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {ψ : Torus d → Torus d → ℝ}
    {K : ℝ}
    (hcan : ∀ x, Integrable (ψ x) (withDensityReal ρ) ∧ ∫ y, ψ x y ∂(withDensityReal ρ) = 0)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d))
    (hgrad : ∀ p ∈ offDiag d, ‖fderiv ℝ (lift2 ψ) p‖ ≤
      K * (1 + rTrunc (Torus.mk p.1) (Torus.mk p.2) ^ (1 - s)))
    {BA : ℝ} (hBA0 : 0 ≤ BA)
    (hBA : ∀ x, ∫⁻ y, ENNReal.ofReal (gradEnv s x y) ∂(withDensityReal ρ) ≤ ENNReal.ofReal BA)
    (m : Fin d) (x0 : Torus d) :
    ∀ᵐ σ : ℝ, (∫ y, gradK ψ m (x0 + Torus.mk (σ • (EuclideanSpace.single m (1 : ℝ) : Euc d))) y
      ∂(withDensityReal ρ)) = 0 := by
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
  set e : Euc d := EuclideanSpace.single m (1 : ℝ) with he
  set c : Torus d → ℝ := fun x => ∫ y, gradK ψ m x y ∂(withDensityReal ρ) with hc
  have hcm : Measurable c :=
    ((measurable_gradK ψ m).stronglyMeasurable.integral_prod_right' (ν := withDensityReal ρ)).measurable
  have hcb : ∀ x, |c x| ≤ |K| * BA := fun x => abs_integral_gradK_le hgrad hatom m hBA0 hBA x
  set g : ℝ → ℝ := fun σ => c (x0 + Torus.mk (σ • e)) with hg
  have hℓ : Measurable fun σ : ℝ => x0 + Torus.mk (σ • e) :=
    measurable_const.add (Torus.continuous_mk.comp (continuous_id.smul continuous_const)).measurable
  have hgm : Measurable g := hcm.comp hℓ
  have hloc : LocallyIntegrable g volume := by
    rw [locallyIntegrable_iff]
    intro C hC
    refine Measure.integrableOn_of_bounded (M := |K| * BA) hC.measure_lt_top.ne hgm.aestronglyMeasurable ?_
    exact Eventually.of_forall fun σ => by rw [Real.norm_eq_abs]; exact hcb _
  have hab : ∀ a b : ℝ, a < b → ∫ σ in a..b, g σ = 0 := by
    intro a b hab
    have h1 : ∫ τ in Set.Ioc 0 (b - a), c (x0 + Torus.mk (a • e) + Torus.mk (τ • e)) = 0 :=
      line_integral_zero hd hρ hcan hsm hgrad hBA0 hBA m (x0 + Torus.mk (a • e)) (t := b - a) (by linarith)
    have h2 : ∀ τ : ℝ, x0 + Torus.mk (a • e) + Torus.mk (τ • e) = x0 + Torus.mk ((a + τ) • e) := by
      intro τ
      rw [add_smul, mk_add', add_assoc]
    simp_rw [h2] at h1
    rw [← intervalIntegral.integral_of_le (by linarith)] at h1
    have h3 := intervalIntegral.integral_comp_add_left (fun σ => g σ) (a := 0) (b := b - a) a
    simp only [add_zero, add_sub_cancel] at h3
    rw [← h3]
    exact h1
  exact ae_zero_of_integral_zero hloc hab

end LemmaD

section LemmaD2

theorem gradK_integral_ae_zero (hd : 2 ≤ d) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
    {ψ : Torus d → Torus d → ℝ} {K : ℝ}
    (hcan : ∀ x, Integrable (ψ x) (withDensityReal ρ) ∧ ∫ y, ψ x y ∂(withDensityReal ρ) = 0)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d))
    (hgrad : ∀ p ∈ offDiag d, ‖fderiv ℝ (lift2 ψ) p‖ ≤
      K * (1 + rTrunc (Torus.mk p.1) (Torus.mk p.2) ^ (1 - s)))
    {BA : ℝ} (hBA0 : 0 ≤ BA)
    (hBA : ∀ x, ∫⁻ y, ENNReal.ofReal (gradEnv s x y) ∂(withDensityReal ρ) ≤ ENNReal.ofReal BA)
    (m : Fin d) :
    ∀ᵐ x ∂(withDensityReal ρ), (∫ y, gradK ψ m x y ∂(withDensityReal ρ)) = 0 := by
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  have hac : withDensityReal ρ ≪ volume := withDensity_absolutelyContinuous _ _
  set e : Euc d := EuclideanSpace.single m (1 : ℝ) with he
  set c : Torus d → ℝ := fun x => ∫ y, gradK ψ m x y ∂(withDensityReal ρ) with hc
  have hcm : Measurable c :=
    ((measurable_gradK ψ m).stronglyMeasurable.integral_prod_right' (ν := withDensityReal ρ)).measurable
  have hline : ∀ x0 : Torus d, ∀ᵐ σ : ℝ, c (x0 + Torus.mk (σ • e)) = 0 :=
    fun x0 => gradK_line_ae_zero hd hρ hcan hsm hgrad hBA0 hBA m x0
  set Z : Set (Torus d) := {x | c x ≠ 0} with hZdef
  have hZ : MeasurableSet Z := (hcm (measurableSet_singleton 0)).compl
  have hmk : Measurable fun σ : ℝ => Torus.mk (σ • e) :=
    (Torus.continuous_mk.comp (continuous_id.smul continuous_const)).measurable
  set H : Torus d × ℝ → ℝ≥0∞ := fun p => Z.indicator (fun _ => (1 : ℝ≥0∞)) (p.1 + Torus.mk (p.2 • e)) with hH
  have hHm : Measurable H :=
    (measurable_const.indicator hZ).comp (measurable_fst.add (hmk.comp measurable_snd))
  have ha : ∀ x : Torus d, ∫⁻ σ in Set.Icc (0 : ℝ) 1, H (x, σ) = 0 := by
    intro x
    have : ∀ᵐ σ : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), H (x, σ) = 0 := by
      refine ae_restrict_of_ae ?_
      filter_upwards [hline x] with σ hσ
      simp only [hH]
      rw [Set.indicator_of_notMem]
      simpa [hZdef] using hσ
    rw [lintegral_congr_ae this, lintegral_zero]
  have hb : ∀ σ : ℝ, ∫⁻ x, H (x, σ) = volume Z := by
    intro σ
    have := lintegral_add_right_eq_self (μ := (volume : Measure (Torus d)))
      (Z.indicator (fun _ => (1 : ℝ≥0∞))) (Torus.mk (σ • e))
    simp only [hH]
    rw [this, lintegral_indicator_const hZ, one_mul]
  have hswap := lintegral_lintegral_swap (μ := (volume : Measure (Torus d)))
    (ν := volume.restrict (Set.Icc (0 : ℝ) 1)) (f := fun x σ => H (x, σ)) hHm.aemeasurable
  simp_rw [ha, hb] at hswap
  simp only [lintegral_zero, lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one] at hswap
  have hvol : volume Z = 0 := hswap.symm
  exact (hac hvol : withDensityReal ρ Z = 0) |> fun h => by
    rw [ae_iff]; simpa [hZdef] using h

end LemmaD2

end HRS.PairMom

end
