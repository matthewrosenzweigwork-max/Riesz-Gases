import HRS.Energy.StaticLimitEnergy
import HRS.Energy.StaticLimitGI

/-!
# The tilted Gaussian: truncated resolvents (work package STAT-4.21)
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace HRS.StaticLimitAux

open HRS Torus

section PartA

variable {d : ℕ} (a : Lattice d → ℝ) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]

open Classical in
/-- The truncated coercive form `⟨h,k⟩ + β ∑_{i∈S} ⟨Z_i,h⟩⟨Z_i,k⟩`. -/
def BS (S : Finset (Idx d)) (β : ℝ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ →L[ℝ] ℝ :=
  (show Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ →L[ℝ] ℝ from innerSL ℝ) + β • (∑ i ∈ S, (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
    (innerSL ℝ (ZL μ a i)) (innerSL ℝ (ZL μ a i)) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ →L[ℝ] ℝ)

theorem BS_apply (S : Finset (Idx d)) (β : ℝ) (h k : Lp ℝ 2 μ) :
    BS a μ S β h k = ⟪h, k⟫ + β * ∑ i ∈ S, ⟪ZL μ a i, h⟫ * ⟪ZL μ a i, k⟫ := by
  simp [BS]
  rfl

theorem BS_coercive (S : Finset (Idx d)) {β : ℝ} (hβ : 0 ≤ β) : IsCoercive (BS a μ S β) := by
  refine ⟨1, one_pos, fun u => ?_⟩
  rw [BS_apply, one_mul, ← real_inner_self_eq_norm_mul_norm]
  have : 0 ≤ β * ∑ i ∈ S, ⟪ZL μ a i, u⟫ * ⟪ZL μ a i, u⟫ :=
    mul_nonneg hβ (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  linarith

/-- The solution operator of the truncated problem. -/
def RS (S : Finset (Idx d)) {β : ℝ} (hβ : 0 ≤ β) : Lp ℝ 2 μ ≃L[ℝ] Lp ℝ 2 μ :=
  (BS_coercive a μ S hβ).continuousLinearEquivOfBilin.symm

theorem RS_spec (S : Finset (Idx d)) {β : ℝ} (hβ : 0 ≤ β) (z k : Lp ℝ 2 μ) :
    ⟪z, k⟫ = BS a μ S β (RS a μ S hβ z) k := by
  have := (BS_coercive a μ S hβ).continuousLinearEquivOfBilin_apply
    ((BS_coercive a μ S hβ).continuousLinearEquivOfBilin.symm z) k
  simpa [RS] using this

open Classical in
theorem sum_eq_inner_trunc (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) (S : Finset (Idx d))
    (h k : Lp ℝ 2 μ) :
    ∑ i ∈ S, ⟪ZL μ a i, h⟫ * ⟪ZL μ a i, k⟫ =
      ⟪truncLp S (Tco μ ha0 has h), Tco μ ha0 has k⟫ := by
  rw [lp.inner_eq_tsum, tsum_eq_sum (s := S)]
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [truncLp_apply, if_pos hi]
    simp [Tco_apply, mul_comm]
  · intro i hi
    rw [truncLp_apply, if_neg hi]
    simp

open Classical in
theorem tendsto_inner_RS (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) {β : ℝ} (hβ : 0 ≤ β)
    (g : Lp ℝ 2 μ) {Sq : ℕ → Finset (Idx d)} (hS : Tendsto Sq atTop atTop) :
    Tendsto (fun n => ⟪g, RS a μ (Sq n) hβ g⟫) atTop (𝓝 ⟪g, Rr μ ha0 has hβ g⟫) := by
  set h := Rr μ ha0 has hβ g with hh
  set v := Tco μ ha0 has h with hv
  have hk : ∀ n, ‖RS a μ (Sq n) hβ g - h‖ ≤
      β * ‖Tco μ ha0 has‖ * ‖v - truncLp (Sq n) v‖ := by
    intro n
    obtain ⟨k0, hk0⟩ : ∃ k0, k0 = RS a μ (Sq n) hβ g - h := ⟨_, rfl⟩
    rw [← hk0]
    have hx : RS a μ (Sq n) hβ g = h + k0 := by rw [hk0]; abel
    have e1 : BS a μ (Sq n) β h k0 + β * ⟪v - truncLp (Sq n) v, Tco μ ha0 has k0⟫ = ⟪g, k0⟫ := by
      rw [BS_apply, sum_eq_inner_trunc a μ ha0 has, inner_sub_left, Rr_spec μ ha0 has hβ g k0,
        Bform_apply μ ha0 has]
      ring
    have e2 : BS a μ (Sq n) β (RS a μ (Sq n) hβ g) k0 = ⟪g, k0⟫ := (RS_spec a μ _ hβ g k0).symm
    have e3 : BS a μ (Sq n) β k0 k0 = β * ⟪v - truncLp (Sq n) v, Tco μ ha0 has k0⟫ := by
      have : BS a μ (Sq n) β (RS a μ (Sq n) hβ g) k0 = BS a μ (Sq n) β h k0 + BS a μ (Sq n) β k0 k0 := by
        rw [hx, map_add, ContinuousLinearMap.add_apply]
      rw [this] at e2; linarith
    have e4 : ‖k0‖ ^ 2 ≤ BS a μ (Sq n) β k0 k0 := by
      rw [BS_apply, ← real_inner_self_eq_norm_sq]
      have : 0 ≤ β * ∑ i ∈ Sq n, ⟪ZL μ a i, k0⟫ * ⟪ZL μ a i, k0⟫ :=
        mul_nonneg hβ (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
      linarith
    have e5 : β * ⟪v - truncLp (Sq n) v, Tco μ ha0 has k0⟫ ≤
        β * (‖v - truncLp (Sq n) v‖ * (‖Tco μ ha0 has‖ * ‖k0‖)) := by
      refine mul_le_mul_of_nonneg_left ((real_inner_le_norm _ _).trans ?_) hβ
      exact mul_le_mul_of_nonneg_left ((Tco μ ha0 has).le_opNorm k0) (norm_nonneg _)
    have e6 : ‖k0‖ ^ 2 ≤ ‖k0‖ * (β * ‖Tco μ ha0 has‖ * ‖v - truncLp (Sq n) v‖) := by
      calc ‖k0‖ ^ 2 ≤ _ := e4
        _ = _ := e3
        _ ≤ _ := e5
        _ = _ := by ring
    by_cases h0 : ‖k0‖ = 0
    · rw [h0]; positivity
    · have hp : 0 < ‖k0‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      nlinarith
  have hv0 : Tendsto (fun n => ‖v - truncLp (Sq n) v‖) atTop (𝓝 0) := by
    have ht := (tendsto_tsum_compl_atTop_zero (fun i : Idx d => (v i) ^ 2)).comp hS
    have hsq := (Real.continuous_sqrt.tendsto 0).comp ht
    rw [Real.sqrt_zero] at hsq
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hsq
    have := norm_sub_truncLp_sq_le v (Sq n) (fun i => (v i) ^ 2) (lp_sq_summable v) (fun i => le_rfl)
    exact Real.le_sqrt_of_sq_le this
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine squeeze_zero (fun n => norm_nonneg _)
    (fun n => ?_) (by simpa using hv0.const_mul (‖g‖ * (β * ‖Tco μ ha0 has‖)))
  rw [← inner_sub_right]
  calc ‖⟪g, RS a μ (Sq n) hβ g - h⟫‖ ≤ ‖g‖ * ‖RS a μ (Sq n) hβ g - h‖ := norm_inner_le_norm _ _
    _ ≤ ‖g‖ * (β * ‖Tco μ ha0 has‖ * ‖v - truncLp (Sq n) v‖) :=
        mul_le_mul_of_nonneg_left (hk n) (norm_nonneg _)
    _ = _ := by ring

end PartA

section PartB

variable {d : ℕ} {m : ℝ} (μ : Measure (Torus d)) [IsProbabilityMeasure μ]

theorem continuous_inner_Ye (hm : (d : ℝ) < 2 * m) (t : NegSobolev d m) :
    Continuous fun z => ⟪t, Ye m μ z⟫ :=
  continuous_const.inner (continuous_Ye hm μ)

theorem integrable_Ye (hm : (d : ℝ) < 2 * m) : Integrable (fun x => Ye m μ x) μ :=
  Integrable.of_bound (continuous_Ye hm μ).aestronglyMeasurable
    (Real.sqrt (8 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))))
    (Filter.Eventually.of_forall fun x => norm_ofMeasureDiff_le hm (Measure.dirac x) μ)

theorem integral_inner_Ye (hm : (d : ℝ) < 2 * m) (t : NegSobolev d m) :
    ∫ z, ⟪t, Ye m μ z⟫ ∂μ = 0 := by
  rw [integral_inner (integrable_Ye μ hm), integral_Ye_eq_zero hm μ, inner_zero_right]

theorem inner_Ye_eq (hm : (d : ℝ) < 2 * m) (t : NegSobolev d m) (z : Torus d) :
    ⟪t, Ye m μ z⟫ = evalFun m t z - ∫ y, evalFun m t y ∂μ := by
  -- pointwise difference is independent of `z`
  have hs : ∀ z, Summable fun k : NonzeroLattice d =>
      NegSobolev.coord t k * NegSobolev.coord (Ye m μ z) k := by
    intro z
    have h := lp.summable_inner (𝕜 := ℝ) (show lp (fun _ : NonzeroLattice d => ℝ) 2 from t)
      (show lp (fun _ : NonzeroLattice d => ℝ) 2 from Ye m μ z)
    refine h.congr fun k => ?_
    simp only [RCLike.inner_apply, conj_trivial]
    show _ = _
    rw [mul_comm]; rfl
  have hin : ∀ z, ⟪t, Ye m μ z⟫ = ∑' k : NonzeroLattice d,
      NegSobolev.coord t k * NegSobolev.coord (Ye m μ z) k := by
    intro z
    show ⟪(show lp (fun _ : NonzeroLattice d => ℝ) 2 from t),
      (show lp (fun _ : NonzeroLattice d => ℝ) 2 from Ye m μ z)⟫ = _
    rw [lp.inner_eq_tsum]
    refine tsum_congr fun k => ?_
    simp only [RCLike.inner_apply, conj_trivial]
    show _ = _
    rw [mul_comm]; rfl
  set κ : NonzeroLattice d → ℝ := fun k =>
    NegSobolev.coord t k * (wgt m k * Torus.measureRealCoeff μ k) with hκ
  have hsA := summable_evalFun hm t
  have hdiff : ∀ z, ⟪t, Ye m μ z⟫ = evalFun m t z - ∑' k, κ k := by
    intro z
    have hk : ∀ k, NegSobolev.coord t k * NegSobolev.coord (Ye m μ z) k =
        NegSobolev.coord t k * (wgt m k * Torus.realMode k z) - κ k := by
      intro k
      rw [coord_Ye hm]; simp only [hκ]; unfold wgt; ring
    have hκs : Summable κ := by
      have := (hsA z).sub (hs z)
      refine this.congr fun k => ?_
      rw [hk k]; ring
    rw [hin z, show (fun k => NegSobolev.coord t k * NegSobolev.coord (Ye m μ z) k) =
      fun k => NegSobolev.coord t k * (wgt m k * Torus.realMode k z) - κ k from funext hk,
      Summable.tsum_sub (hsA z) hκs]
    rfl
  have h0 := integral_inner_Ye μ hm t
  have hint : ∫ z, ⟪t, Ye m μ z⟫ ∂μ = ∫ z, (evalFun m t z - ∑' k, κ k) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall hdiff)
  have hev : Integrable (evalFun m t) μ :=
    (continuous_evalFun hm t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_sub hev (integrable_const _)] at hint
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hint
  rw [hdiff z]
  linarith

theorem cl_inner_Ye_eq (hm : (d : ℝ) < 2 * m) (t : NegSobolev d m) :
    cl μ (fun z => ⟪t, Ye m μ z⟫) (continuous_inner_Ye μ hm t) = Pmap μ (Wmap μ hm t) := by
  refine Lp.ext ?_
  have hW : (⇑(Wmap μ hm t) : Torus d → ℝ) =ᵐ[μ] evalFun m t := by
    rw [Wmap_apply]; exact cl_ae μ (continuous_evalFun hm t)
  filter_upwards [cl_ae μ (continuous_inner_Ye μ hm t), Pmap_ae μ (Wmap μ hm t), hW] with z h1 h2 h3
  rw [h1, h2, inner_Ye_eq μ hm t z, h3]
  congr 1
  exact integral_congr_ae hW.symm

end PartB

section PartC

variable {d : ℕ} {m : ℝ} {a : Lattice d → ℝ}

open Classical in
/-- The `ℓ²` vector `∑_{i∈S} ξ_i e_i`. -/
def fv (d : ℕ) (S : Finset (Idx d)) (ξ : EuclideanSpace ℝ S) : FeatSp d :=
  ∑ i : S, ξ i • singleF d (i : Idx d)

open Classical in
theorem inner_fv (S : Finset (Idx d)) (ξ : EuclideanSpace ℝ S) (f : FeatSp d) :
    ⟪fv d S ξ, f⟫ = ∑ i : S, ξ i * FeatSp.coord f (i : Idx d) := by
  unfold fv
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left]
  congr 1
  show ⟪(lp.single 2 (i : Idx d) (1 : ℝ) : lp (fun _ : Idx d => ℝ) 2),
    (show lp (fun _ : Idx d => ℝ) 2 from f)⟫ = _
  rw [lp.inner_single_left]
  simp [FeatSp.coord]

/-- The test vector `(t, √β ∑ ξ_i e_i)` in the joint space. -/
def uvec (m : ℝ) (S : Finset (Idx d)) (β : ℝ) (t : NegSobolev d m) (ξ : EuclideanSpace ℝ S) :
    JSp d m :=
  WithLp.toLp 2 (t, Real.sqrt β • fv d S ξ)

theorem inner_uvec_Yj (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (S : Finset (Idx d)) (β : ℝ) (t : NegSobolev d m)
    (ξ : EuclideanSpace ℝ S) (z : Torus d) :
    ⟪uvec m S β t ξ, Yj m ha0 has μ z⟫ =
      ⟪t, Ye m μ z⟫ + Real.sqrt β * ∑ i : S, ξ i * Zfeat μ a (i : Idx d) z := by
  unfold uvec Yj
  rw [WithLp.prod_inner_apply]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, real_inner_smul_left]
  rw [inner_fv]
  rfl

variable (a) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]

open Classical in
/-- `ξ ↦ √β ∑_{i∈S} ξ_i Z_i ∈ L²(μ)`. -/
def Tmap (S : Finset (Idx d)) (β : ℝ) : EuclideanSpace ℝ S →L[ℝ] Lp ℝ 2 μ :=
  ∑ i : S, (EuclideanSpace.proj i : EuclideanSpace ℝ S →L[ℝ] ℝ).smulRight
    (Real.sqrt β • ZL μ a (i : Idx d))

theorem Tmap_apply (S : Finset (Idx d)) (β : ℝ) (ξ : EuclideanSpace ℝ S) :
    Tmap a μ S β ξ = ∑ i : S, (Real.sqrt β * ξ i) • ZL μ a (i : Idx d) := by
  simp [Tmap, smul_smul, mul_comm]

theorem coeFn_finset_sum_ae {ι : Type*} (s : Finset ι) (f : ι → Lp ℝ 2 μ) :
    (⇑(∑ i ∈ s, f i) : Torus d → ℝ) =ᵐ[μ] ∑ i ∈ s, (⇑(f i) : Torus d → ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Lp.coeFn_zero ℝ 2 μ
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (f j) (∑ i ∈ s, f i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Pi.add_apply]

theorem inner_Ye_cont_sum (hm : (d : ℝ) < 2 * m) (S : Finset (Idx d)) (β : ℝ)
    (t : NegSobolev d m) (ξ : EuclideanSpace ℝ S) :
    Continuous fun z => ⟪t, Ye m μ z⟫ +
      Real.sqrt β * ∑ i : S, ξ i * Zfeat μ a (i : Idx d) z := by
  refine (continuous_inner_Ye μ hm t).add (continuous_const.mul ?_)
  exact continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_Zfeat μ _)

theorem cl_sum_eq (hm : (d : ℝ) < 2 * m) (S : Finset (Idx d)) (β : ℝ)
    (t : NegSobolev d m) (ξ : EuclideanSpace ℝ S) :
    cl μ _ (inner_Ye_cont_sum a μ hm S β t ξ) = Pmap μ (Wmap μ hm t) + Tmap a μ S β ξ := by
  classical
  rw [← cl_inner_Ye_eq μ hm t, Tmap_apply]
  refine Lp.ext ?_
  have hz : ∀ i : S, (⇑(ZL μ a (i : Idx d)) : Torus d → ℝ) =ᵐ[μ] Zfeat μ a (i : Idx d) :=
    fun i => cl_ae μ (continuous_Zfeat μ _)
  have hall : ∀ᵐ x ∂μ, ∀ i : S, (ZL μ a (i : Idx d)) x = Zfeat μ a (i : Idx d) x :=
    ae_all_iff.2 hz
  have hsm : ∀ i : S, ∀ᵐ x ∂μ, ((Real.sqrt β * ξ i) • ZL μ a (i : Idx d)) x =
      (Real.sqrt β * ξ i) * (ZL μ a (i : Idx d)) x := fun i => by
    filter_upwards [Lp.coeFn_smul (Real.sqrt β * ξ i) (ZL μ a (i : Idx d))] with x hx
    rw [hx]; rfl
  have hsm' : ∀ᵐ x ∂μ, ∀ i : S, ((Real.sqrt β * ξ i) • ZL μ a (i : Idx d)) x =
      (Real.sqrt β * ξ i) * (ZL μ a (i : Idx d)) x := ae_all_iff.2 hsm
  filter_upwards [cl_ae μ (inner_Ye_cont_sum a μ hm S β t ξ), cl_ae μ (continuous_inner_Ye μ hm t),
    Lp.coeFn_add (cl μ _ (continuous_inner_Ye μ hm t))
      (∑ i : S, (Real.sqrt β * ξ i) • ZL μ a (i : Idx d)),
    coeFn_finset_sum_ae μ Finset.univ (fun i : S => (Real.sqrt β * ξ i) • ZL μ a (i : Idx d)),
    hall, hsm'] with x h1 h2 h3 h4 h5 h6
  rw [h1, h3, Pi.add_apply, h2, h4, Finset.sum_apply, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h6 i, h5 i]; ring

theorem cov_uvec (hm : (d : ℝ) < 2 * m) (ha0 : ∀ k, 0 ≤ a k) (has : Summable a)
    (S : Finset (Idx d)) (β : ℝ) (t : NegSobolev d m) (ξ : EuclideanSpace ℝ S) :
    ProbabilityTheory.covarianceBilin (μ.map (Yj m ha0 has μ)) (uvec m S β t ξ) (uvec m S β t ξ) =
      ‖Pmap μ (Wmap μ hm t) + Tmap a μ S β ξ‖ ^ 2 := by
  have hc := continuous_Yj hm ha0 has μ
  have hmem : MemLp id 2 (μ.map (Yj m ha0 has μ)) := by
    rw [memLp_map_measure_iff aestronglyMeasurable_id hc.aemeasurable]
    exact MemLp.of_bound (C := Mconst d m a) hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => norm_Yj_le hm ha0 has μ x)
  have hint : Integrable (Yj m ha0 has μ) μ :=
    Integrable.of_bound hc.aestronglyMeasurable (Mconst d m a)
      (Filter.Eventually.of_forall fun x => norm_Yj_le hm ha0 has μ x)
  have hmean : ∫ y, id y ∂(μ.map (Yj m ha0 has μ)) = 0 := by
    rw [integral_map hc.aemeasurable aestronglyMeasurable_id]
    exact integral_Yj_eq_zero hm ha0 has μ
  rw [ProbabilityTheory.covarianceBilin_apply hmem, hmean]
  simp only [sub_zero]
  rw [integral_map hc.aemeasurable
    ((continuous_const.inner continuous_id).mul (continuous_const.inner continuous_id)).aestronglyMeasurable]
  simp_rw [inner_uvec_Yj ha0 has μ S β t ξ]
  rw [← real_inner_self_eq_norm_sq, ← cl_sum_eq a μ hm S β t ξ,
    inner_cl_cl μ (inner_Ye_cont_sum a μ hm S β t ξ) (inner_Ye_cont_sum a μ hm S β t ξ)]

end PartC

section PartD

open Complex

variable {d : ℕ} {m : ℝ} {a : Lattice d → ℝ}

/-- The truncated tilt weight. -/
def wS (β : ℝ) (S : Finset (Idx d)) (f : FeatSp d) : ℝ :=
  Real.exp (-(β / 2) * ∑ i ∈ S, FeatSp.coord f i ^ 2)

theorem inner_uvec (S : Finset (Idx d)) (β : ℝ) (t : NegSobolev d m) (ξ : EuclideanSpace ℝ S)
    (z : JSp d m) :
    ⟪z, uvec m S β t ξ⟫ = ⟪z.fst, t⟫ + ∑ i : S, ξ i * (Real.sqrt β * FeatSp.coord z.snd (i : Idx d)) := by
  unfold uvec
  rw [WithLp.prod_inner_apply]
  show ⟪WithLp.fst z, t⟫ + ⟪WithLp.snd z, Real.sqrt β • fv d S ξ⟫ = _
  rw [real_inner_smul_right, real_inner_comm (fv d S ξ) (WithLp.snd z), inner_fv, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem step1 (S : Finset (Idx d)) {β : ℝ} (hβ : 0 ≤ β) (t : NegSobolev d m) (z : JSp d m) :
    ∫ ξ : EuclideanSpace ℝ S, cexp (-(1 / 2 : ℂ) * (‖ξ‖ : ℂ) ^ 2) *
        cexp (Complex.I * (⟪z, uvec m S β t ξ⟫ : ℝ)) =
      gaussC (EuclideanSpace ℝ S) * (cexp (Complex.I * (⟪z.fst, t⟫ : ℝ)) * (wS β S z.snd : ℝ)) := by
  classical
  set s : EuclideanSpace ℝ S :=
    WithLp.toLp 2 (fun i : S => Real.sqrt β * FeatSp.coord z.snd (i : Idx d)) with hs
  have hin : ∀ ξ, ⟪z, uvec m S β t ξ⟫ = ⟪z.fst, t⟫ + ⟪s, ξ⟫ := by
    intro ξ
    rw [inner_uvec]
    congr 1
  have hns : ‖s‖ ^ 2 = β * ∑ i ∈ S, FeatSp.coord z.snd i ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, ← Finset.sum_coe_sort S, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hs, Real.norm_eq_abs, sq_abs, mul_pow]
    rw [Real.sq_sqrt hβ]
  have hw : (wS β S z.snd : ℂ) = cexp (-(((‖s‖ ^ 2 : ℝ) : ℂ)) / 2) := by
    unfold wS
    rw [hns, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hw]
  have : ∀ ξ : EuclideanSpace ℝ S, cexp (-(1 / 2 : ℂ) * (‖ξ‖ : ℂ) ^ 2) *
        cexp (Complex.I * (⟪z, uvec m S β t ξ⟫ : ℝ)) =
      cexp (Complex.I * (⟪z.fst, t⟫ : ℝ)) *
        cexp (-(1 / 2 : ℂ) * (‖ξ‖ : ℂ) ^ 2 + Complex.I * (⟪s, ξ⟫ : ℝ)) := by
    intro ξ
    rw [hin ξ, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [this]
  rw [integral_const_mul, hs_gaussian s]
  ring

theorem continuous_uvec (S : Finset (Idx d)) (β : ℝ) (t : NegSobolev d m) :
    Continuous (uvec m S β t) := by
  classical
  unfold uvec
  refine (WithLp.prod_continuous_toLp 2 _ _).comp (continuous_const.prodMk ?_)
  have hfv : Continuous (fv d S) := by
    unfold fv
    refine continuous_finset_sum _ fun i _ => ?_
    exact (show Continuous fun ξ : EuclideanSpace ℝ S => ξ i from
      (EuclideanSpace.proj i : EuclideanSpace ℝ S →L[ℝ] ℝ).continuous).smul
      (continuous_const (y := singleF d (i : Idx d)))
  exact hfv.const_smul (Real.sqrt β)

/-- The double-integral integrand. -/
def PhiG (m : ℝ) (S : Finset (Idx d)) (β : ℝ) (t : NegSobolev d m)
    (p : JSp d m × EuclideanSpace ℝ S) : ℂ :=
  cexp (-(1 / 2 : ℂ) * (‖p.2‖ : ℂ) ^ 2) * cexp (Complex.I * (⟪p.1, uvec m S β t p.2⟫ : ℝ))

theorem continuous_PhiG (S : Finset (Idx d)) (β : ℝ) (t : NegSobolev d m) :
    Continuous (PhiG m S β t) := by
  unfold PhiG
  refine Continuous.mul ?_ ?_
  · exact Complex.continuous_exp.comp (continuous_const.mul
      ((Complex.continuous_ofReal.comp continuous_snd.norm).pow 2))
  · refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
    exact continuous_fst.inner ((continuous_uvec S β t).comp continuous_snd)

theorem norm_PhiG (S : Finset (Idx d)) (β : ℝ) (t : NegSobolev d m)
    (p : JSp d m × EuclideanSpace ℝ S) :
    ‖PhiG m S β t p‖ = Real.exp (-(1 / 2) * ‖p.2‖ ^ 2) := by
  unfold PhiG
  rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
  simp [← Complex.ofReal_pow]

theorem integrable_PhiG (S : Finset (Idx d)) (β : ℝ) (t : NegSobolev d m)
    (Γ : Measure (JSp d m)) [IsProbabilityMeasure Γ] :
    Integrable (PhiG m S β t) (Γ.prod volume) := by
  have hA : Integrable (fun ξ : EuclideanSpace ℝ S => Real.exp (-(1 / 2) * ‖ξ‖ ^ 2)) volume := by
    have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := EuclideanSpace ℝ S)
      (b := (1 / 2 : ℂ)) (by norm_num) 0 0).norm
    refine this.congr (Filter.Eventually.of_forall fun ξ => ?_)
    simp only [Complex.norm_exp]
    simp [← Complex.ofReal_pow]
  have hB : Integrable (fun p : JSp d m × EuclideanSpace ℝ S =>
      (1 : ℝ) * Real.exp (-(1 / 2) * ‖p.2‖ ^ 2)) (Γ.prod volume) :=
    Integrable.mul_prod (f := fun _ : JSp d m => (1 : ℝ))
      (g := fun ξ : EuclideanSpace ℝ S => Real.exp (-(1 / 2) * ‖ξ‖ ^ 2)) (integrable_const _) hA
  refine hB.mono' (continuous_PhiG S β t).aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
  rw [norm_PhiG, one_mul]

end PartD

section PartE

variable {d : ℕ} (a : Lattice d → ℝ) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]

theorem inner_Tmap_left (S : Finset (Idx d)) (β : ℝ) (ξ : EuclideanSpace ℝ S) (k : Lp ℝ 2 μ) :
    ⟪Tmap a μ S β ξ, k⟫ = ∑ i : S, Real.sqrt β * ξ i * ⟪ZL μ a (i : Idx d), k⟫ := by
  rw [Tmap_apply, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left]

theorem inner_Tmap_right (S : Finset (Idx d)) (β : ℝ) (η : EuclideanSpace ℝ S) (h : Lp ℝ 2 μ) :
    ⟪h, Tmap a μ S β η⟫ = ∑ i : S, Real.sqrt β * η i * ⟪ZL μ a (i : Idx d), h⟫ := by
  rw [real_inner_comm, inner_Tmap_left]

/-- The minimiser `ξ₀ = -T* h`. -/
def xi0 (S : Finset (Idx d)) {β : ℝ} (hβ : 0 ≤ β) (g : Lp ℝ 2 μ) : EuclideanSpace ℝ S :=
  WithLp.toLp 2 (fun i : S => -(Real.sqrt β * ⟪ZL μ a (i : Idx d), RS a μ S hβ g⟫))

theorem RS_gi (S : Finset (Idx d)) {β : ℝ} (hβ : 0 ≤ β) (g : Lp ℝ 2 μ) :
    g + Tmap a μ S β (xi0 a μ S hβ g) = RS a μ S hβ g ∧
    (∀ η, ⟪RS a μ S hβ g, Tmap a μ S β η⟫ = -⟪xi0 a μ S hβ g, η⟫) ∧
    ‖RS a μ S hβ g‖ ^ 2 + ‖xi0 a μ S hβ g‖ ^ 2 = ⟪g, RS a μ S hβ g⟫ := by
  classical
  set h := RS a μ S hβ g with hh
  have hspec : ∀ k, ⟪g, k⟫ = ⟪h, k⟫ + β * ∑ i : S, ⟪ZL μ a (i : Idx d), h⟫ * ⟪ZL μ a (i : Idx d), k⟫ := by
    intro k
    rw [hh, RS_spec a μ S hβ g k, BS_apply, Finset.sum_coe_sort S
      (fun i => ⟪ZL μ a i, RS a μ S hβ g⟫ * ⟪ZL μ a i, k⟫)]
  have hsq : Real.sqrt β * Real.sqrt β = β := Real.mul_self_sqrt hβ
  refine ⟨?_, ?_, ?_⟩
  · refine ext_inner_right ℝ fun k => ?_
    rw [inner_add_left, inner_Tmap_left, hspec k]
    have : ∑ i : S, Real.sqrt β * (xi0 a μ S hβ g) i * ⟪ZL μ a (i : Idx d), k⟫ =
        -(β * ∑ i : S, ⟪ZL μ a (i : Idx d), h⟫ * ⟪ZL μ a (i : Idx d), k⟫) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [xi0]
      rw [← hh]
      linear_combination (-(⟪ZL μ a (i : Idx d), h⟫ * ⟪ZL μ a (i : Idx d), k⟫)) * hsq
    rw [this]; ring
  · intro η
    rw [inner_Tmap_right]
    simp only [xi0, PiLp.inner_apply]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [RCLike.inner_apply, conj_trivial]
    rw [← hh]
    ring
  · rw [hspec h, real_inner_self_eq_norm_sq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [xi0, Real.norm_eq_abs, sq_abs]
    rw [← hh]
    linear_combination (⟪ZL μ a (i : Idx d), h⟫ * ⟪ZL μ a (i : Idx d), h⟫) * hsq

end PartE

section PartF

open Complex

variable {d : ℕ} {m : ℝ} {a : Lattice d → ℝ}

theorem trunc_main (hm : (d : ℝ) < 2 * m) (ha0 : ∀ k, 0 ≤ a k) (has : Summable a)
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {β : ℝ} (hβ : 0 ≤ β)
    (Γ : Measure (JSp d m)) (hΓ : IsCenteredGaussian Γ)
    (hcov : ∀ x y, ProbabilityTheory.covarianceBilin Γ x y =
      ProbabilityTheory.covarianceBilin (μ.map (Yj m ha0 has μ)) x y)
    (S : Finset (Idx d)) (t : NegSobolev d m) :
    gaussC (EuclideanSpace ℝ S) *
        ∫ z, cexp (Complex.I * (⟪z.fst, t⟫ : ℝ)) * (wS β S z.snd : ℝ) ∂Γ =
      cexp (-(((⟪Pmap μ (Wmap μ hm t), RS a μ S hβ (Pmap μ (Wmap μ hm t))⟫ : ℝ) : ℂ)) / 2) *
        ∫ η : EuclideanSpace ℝ S, cexp (-(1 / 2 : ℂ) * (‖η‖ : ℂ) ^ 2) *
          cexp (-(1 / 2 : ℂ) * (‖Tmap a μ S β η‖ : ℂ) ^ 2) := by
  classical
  have hG := hΓ.1
  set g := Pmap μ (Wmap μ hm t) with hg
  have hI : Integrable (Function.uncurry fun (z : JSp d m) (ξ : EuclideanSpace ℝ S) =>
      PhiG m S β t (z, ξ)) (Γ.prod volume) := integrable_PhiG S β t Γ
  have hfub := integral_integral_swap hI
  have hL : ∫ z, ∫ ξ : EuclideanSpace ℝ S, PhiG m S β t (z, ξ) ∂volume ∂Γ =
      gaussC (EuclideanSpace ℝ S) *
        ∫ z, cexp (Complex.I * (⟪z.fst, t⟫ : ℝ)) * (wS β S z.snd : ℝ) ∂Γ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact step1 S hβ t z
  have hR : ∀ ξ : EuclideanSpace ℝ S, ∫ z, PhiG m S β t (z, ξ) ∂Γ =
      cexp (-(1 / 2 : ℂ) * (‖ξ‖ : ℂ) ^ 2) *
        cexp (-(1 / 2 : ℂ) * (‖g + Tmap a μ S β ξ‖ : ℂ) ^ 2) := by
    intro ξ
    unfold PhiG
    simp only
    rw [integral_const_mul]
    congr 1
    have h1 : ∫ z, cexp (Complex.I * (⟪z, uvec m S β t ξ⟫ : ℝ)) ∂Γ =
        charFun Γ (uvec m S β t ξ) := by
      rw [charFun_apply]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [mul_comm]
    rw [h1, HilbertCLTAux.charFun_centered_gaussian hΓ, hcov, cov_uvec a μ hm ha0 has]
    congr 1
    push_cast
    ring
  rw [hL] at hfub
  rw [hfub]
  simp_rw [hR]
  obtain ⟨h1, h2, h3⟩ := RS_gi a μ S hβ g
  rw [gi_complete (Tmap a μ S β) g (RS a μ S hβ g) (xi0 a μ S hβ g) h1 h2, h3]

end PartF

section PartG

open Complex

theorem charFun_tilt_map {B E : Type*} [MeasurableSpace B] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (w : B → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (ν : Measure B)
    (hA : 0 < ∫ y, w y ∂ν) (T : B → E) (hT : Measurable T) (t : E) :
    charFun ((tiltMeasure w ν).map T) t =
      (∫ x, cexp ((⟪T x, t⟫ : ℝ) * Complex.I) * (w x : ℂ) ∂ν) / (((∫ y, w y ∂ν : ℝ)) : ℂ) := by
  rw [charFun_apply, integral_map hT.aemeasurable (by fun_prop), tiltMeasure_eq w ν hw hw0 hA]
  have hmeas : Measurable fun x => (w x / ∫ y, w y ∂ν).toNNReal :=
    (hw.div_const _).real_toNNReal
  have e : (fun x => ENNReal.ofReal (w x / ∫ y, w y ∂ν)) =
      fun x => (((w x / ∫ y, w y ∂ν).toNNReal : ℝ≥0) : ℝ≥0∞) := rfl
  rw [e, integral_withDensity_eq_integral_smul hmeas, ← integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [NNReal.smul_def, Real.coe_toNNReal _ (div_nonneg (hw0 x) hA.le)]
  simp only [Complex.real_smul]
  push_cast
  ring

end PartG

section PartH

open Complex

variable {d : ℕ} {m : ℝ} {a : Lattice d → ℝ} {β : ℝ}

theorem continuous_wS (β : ℝ) (S : Finset (Idx d)) : Continuous (wS β S : FeatSp d → ℝ) := by
  unfold wS
  refine Real.continuous_exp.comp (continuous_const.mul (continuous_finset_sum _ fun i _ => ?_))
  have hc : Continuous fun f : FeatSp d => FeatSp.coord f i := (fcoordCLM i).continuous
  exact hc.pow 2

theorem wS_nonneg (β : ℝ) (S : Finset (Idx d)) (f : FeatSp d) : 0 ≤ wS β S f :=
  (Real.exp_pos _).le

theorem wS_le_one {β : ℝ} (hβ : 0 ≤ β) (S : Finset (Idx d)) (f : FeatSp d) : wS β S f ≤ 1 := by
  unfold wS
  rw [Real.exp_le_one_iff]
  have : 0 ≤ ∑ i ∈ S, FeatSp.coord f i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  nlinarith

theorem tendsto_wS {Sq : ℕ → Finset (Idx d)} (hS : Tendsto Sq atTop atTop) (z : JSp d m) :
    Tendsto (fun n => wS β (Sq n) z.snd) atTop (𝓝 (tw (qJ d m) β z)) := by
  have h := ((FeatSp.summable_sq z.snd).hasSum).comp hS
  have h2 := (Real.continuous_exp.tendsto _).comp ((h.const_mul (-(β / 2))))
  unfold tw qJ wS
  rw [FeatSp.norm_sq z.snd]
  exact h2

theorem tendsto_J (hβ' : 0 ≤ β) (Γ : Measure (JSp d m)) [IsProbabilityMeasure Γ]
    {Sq : ℕ → Finset (Idx d)} (hS : Tendsto Sq atTop atTop) (t : NegSobolev d m) :
    Tendsto (fun n => ∫ z, cexp (Complex.I * (⟪z.fst, t⟫ : ℝ)) * (wS β (Sq n) z.snd : ℝ) ∂Γ)
      atTop (𝓝 (∫ z, cexp (Complex.I * (⟪z.fst, t⟫ : ℝ)) * (tw (qJ d m) β z : ℝ) ∂Γ)) := by
  have hc1 : Continuous fun z : JSp d m => cexp (Complex.I * (⟪z.fst, t⟫ : ℝ)) :=
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      ((WithLp.continuous_fst 2 _ _).inner continuous_const)))
  refine tendsto_integral_of_dominated_convergence (fun _ => 1) (fun n => ?_) (integrable_const _)
    (fun n => Filter.Eventually.of_forall fun z => ?_) (Filter.Eventually.of_forall fun z => ?_)
  · refine (hc1.mul (Complex.continuous_ofReal.comp ((continuous_wS β (Sq n)).comp
      (WithLp.continuous_snd 2 _ _)))).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_zero, Real.exp_zero, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    rw [abs_of_nonneg (wS_nonneg β _ _)]
    exact wS_le_one hβ' _ _
  · exact (tendsto_const_nhds.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_wS hS z)))

end PartH

section PartI

open Complex

variable {d : ℕ} {m : ℝ} {a : Lattice d → ℝ}

theorem tilt_ident (hm : (d : ℝ) < 2 * m) (ha0 : ∀ k, 0 ≤ a k) (has : Summable a)
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {β : ℝ} (hβ : 0 ≤ β)
    (Γ : Measure (JSp d m)) (hΓ : IsCenteredGaussian Γ)
    (hcov : ∀ x y, ProbabilityTheory.covarianceBilin Γ x y =
      ProbabilityTheory.covarianceBilin (μ.map (Yj m ha0 has μ)) x y) (t : NegSobolev d m) :
    ∫ z, cexp (Complex.I * (⟪z.fst, t⟫ : ℝ)) * (tw (qJ d m) β z : ℝ) ∂Γ =
      ((∫ z, tw (qJ d m) β z ∂Γ : ℝ) : ℂ) *
        cexp (-((Cmap μ ha0 has hβ hm t t : ℝ) : ℂ) / 2) := by
  classical
  haveI := hΓ.1
  have hS := tendsto_seqF d
  set Sq := seqF d with hSq
  set g := Pmap μ (Wmap μ hm t) with hg
  -- the truncated identity
  have hkey : ∀ n, ∫ z, cexp (Complex.I * (⟪z.fst, t⟫ : ℝ)) * (wS β (Sq n) z.snd : ℝ) ∂Γ =
      cexp (-(((⟪g, RS a μ (Sq n) hβ g⟫ : ℝ) : ℂ)) / 2) *
        ∫ z, cexp (Complex.I * (⟪z.fst, (0 : NegSobolev d m)⟫ : ℝ)) *
          (wS β (Sq n) z.snd : ℝ) ∂Γ := by
    intro n
    have h1 := trunc_main hm ha0 has μ hβ Γ hΓ hcov (Sq n) t
    have h0 := trunc_main hm ha0 has μ hβ Γ hΓ hcov (Sq n) 0
    have hz : Pmap μ (Wmap μ hm (0 : NegSobolev d m)) = 0 := by simp
    rw [hz, map_zero, inner_zero_left, Complex.ofReal_zero, neg_zero, zero_div, Complex.exp_zero,
      one_mul] at h0
    rw [← hg] at h1
    have hne := gaussC_ne_zero (V := EuclideanSpace ℝ (Sq n))
    apply mul_left_cancel₀ hne
    rw [h1, mul_left_comm, h0]
  have hq : Tendsto (fun n => cexp (-(((⟪g, RS a μ (Sq n) hβ g⟫ : ℝ) : ℂ)) / 2)) atTop
      (𝓝 (cexp (-((Cmap μ ha0 has hβ hm t t : ℝ) : ℂ) / 2))) := by
    have h := tendsto_inner_RS a μ ha0 has hβ g hS
    rw [Cmap_apply]
    refine (Complex.continuous_exp.tendsto _).comp ?_
    exact ((Complex.continuous_ofReal.tendsto _).comp h).neg.div_const 2
  have hlim := tendsto_J hβ Γ hS t
  have hlim0 := tendsto_J hβ Γ hS (0 : NegSobolev d m)
  have hlim' : Tendsto (fun n => ∫ z, cexp (Complex.I * (⟪z.fst, t⟫ : ℝ)) *
      (wS β (Sq n) z.snd : ℝ) ∂Γ) atTop
      (𝓝 (cexp (-((Cmap μ ha0 has hβ hm t t : ℝ) : ℂ) / 2) *
        ∫ z, cexp (Complex.I * (⟪z.fst, (0 : NegSobolev d m)⟫ : ℝ)) * (tw (qJ d m) β z : ℝ) ∂Γ)) := by
    simp_rw [hkey]
    exact hq.mul hlim0
  rw [tendsto_nhds_unique hlim hlim']
  simp only [inner_zero_right, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
  rw [integral_complex_ofReal, mul_comm]

end PartI

end HRS.StaticLimitAux
