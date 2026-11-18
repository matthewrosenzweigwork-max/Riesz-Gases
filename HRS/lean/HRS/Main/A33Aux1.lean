import Mathlib

/-!
# Packet A33, helper 1: the isonormal Gaussian process of a Hilbert space
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ENNReal NNReal Matrix

namespace HRS.A33

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma a33_integral_abs_le (f : Ω → ℝ) (hf : MemLp f 2 P) :
    ∫ ω, |f ω| ∂P ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂P) := by
  have h1 : MemLp (fun ω => |f ω|) 2 P := hf.abs
  have h2 := variance_nonneg (fun ω => |f ω|) P
  rw [variance_eq_sub h1] at h2
  have h4 : (P[fun ω => |f ω|]) ^ 2 ≤ ∫ ω, f ω ^ 2 ∂P := by
    simp only [Pi.pow_apply, sq_abs] at h2
    linarith
  exact Real.le_sqrt_of_sq_le h4

lemma a33_charFun_eq (Y : Ω → ℝ) (hY : Measurable Y) (t : ℝ) :
    charFun (P.map Y) t = ∫ ω, Complex.exp (((t * Y ω : ℝ) : ℂ) * Complex.I) ∂P := by
  rw [charFun_apply_real, integral_map hY.aemeasurable (by fun_prop)]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp [mul_assoc]

lemma a33_norm_exp_sub (x y : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I)‖ ≤ |x - y| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y)
  have e : Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I) =
      Complex.exp ((y : ℂ) * Complex.I) * (Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast; ring
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa using h

lemma a33_meas_exp (X : Ω → ℝ) (hXm : Measurable X) (t : ℝ) :
    Measurable fun ω => Complex.exp (((t * X ω : ℝ) : ℂ) * Complex.I) :=
  Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp (hXm.const_mul t)).mul_const _)

lemma a33_charFun_dist (X Y : Ω → ℝ) (hXm : Measurable X) (hYm : Measurable Y)
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P) (t : ℝ) :
    ‖charFun (P.map X) t - charFun (P.map Y) t‖ ≤
      |t| * Real.sqrt (∫ ω, (X ω - Y ω) ^ 2 ∂P) := by
  rw [a33_charFun_eq X hXm, a33_charFun_eq Y hYm, ← integral_sub]
  · have hd : MemLp (fun ω => X ω - Y ω) 2 P := hX.sub hY
    calc ‖∫ ω, (Complex.exp (((t * X ω : ℝ) : ℂ) * Complex.I) -
            Complex.exp (((t * Y ω : ℝ) : ℂ) * Complex.I)) ∂P‖
        ≤ ∫ ω, ‖Complex.exp (((t * X ω : ℝ) : ℂ) * Complex.I) -
            Complex.exp (((t * Y ω : ℝ) : ℂ) * Complex.I)‖ ∂P := norm_integral_le_integral_norm _
      _ ≤ ∫ ω, |t| * |X ω - Y ω| ∂P := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun ω => norm_nonneg _) ?_
            (Eventually.of_forall fun ω => ?_)
          · exact (hd.abs.integrable (by norm_num)).const_mul _
          · refine (a33_norm_exp_sub _ _).trans ?_
            rw [← mul_sub, abs_mul]
      _ = |t| * ∫ ω, |X ω - Y ω| ∂P := integral_const_mul _ _
      _ ≤ |t| * Real.sqrt (∫ ω, (X ω - Y ω) ^ 2 ∂P) :=
          mul_le_mul_of_nonneg_left (a33_integral_abs_le _ hd) (abs_nonneg _)
  · exact (Integrable.of_bound (a33_meas_exp X hXm t).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => (Complex.norm_exp_ofReal_mul_I _).le))
  · exact (Integrable.of_bound (a33_meas_exp Y hYm t).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => (Complex.norm_exp_ofReal_mul_I _).le))

/-- The isometry `x ↦ x • v` for a unit vector `v`. -/
def a33_line {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : E) (hv : ‖v‖ = 1) :
    ℝ →ₗᵢ[ℝ] E where
  toFun x := x • v
  map_add' x y := add_smul x y v
  map_smul' c x := by simp [smul_smul]
  norm_map' x := by simp [norm_smul, hv]

lemma a33_line_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : E)
    (hv : ‖v‖ = 1) (x : ℝ) : a33_line v hv x = x • v := rfl

lemma a33_charFun_limit {ι : Type*} {l : Filter ι} [l.NeBot] (X : ι → Ω → ℝ) (Y : Ω → ℝ)
    (hXm : ∀ j, Measurable (X j)) (hYm : Measurable Y) (hX : ∀ j, MemLp (X j) 2 P)
    (hY : MemLp Y 2 P) (hconv : Tendsto (fun j => ∫ ω, (X j ω - Y ω) ^ 2 ∂P) l (𝓝 0))
    (v : ι → ℝ) (v' : ℝ) (hv : Tendsto v l (𝓝 v'))
    (hlaw : ∀ j (t : ℝ), charFun (P.map (X j)) t = Complex.exp (-((v j : ℂ) * (t : ℂ) ^ 2 / 2)))
    (t : ℝ) : charFun (P.map Y) t = Complex.exp (-((v' : ℂ) * (t : ℂ) ^ 2 / 2)) := by
  have h1 : Tendsto (fun j => charFun (P.map (X j)) t) l (𝓝 (charFun (P.map Y) t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun j => |t| * Real.sqrt (∫ ω, (X j ω - Y ω) ^ 2 ∂P)) l (𝓝 0) := by
      have := ((Real.continuous_sqrt.tendsto 0).comp hconv).const_mul |t|
      simpa using this
    exact squeeze_zero (fun j => norm_nonneg _) (fun j => a33_charFun_dist (X j) Y (hXm j) hYm
      (hX j) hY t) h0
  have h2 : Tendsto (fun j => charFun (P.map (X j)) t) l
      (𝓝 (Complex.exp (-((v' : ℂ) * (t : ℂ) ^ 2 / 2)))) := by
    simp_rw [hlaw]
    refine (Complex.continuous_exp.tendsto _).comp ?_
    have := ((Complex.continuous_ofReal.tendsto _).comp hv).mul_const ((t : ℂ) ^ 2)
    exact (this.div_const 2).neg
  exact tendsto_nhds_unique h1 h2

section Iso

variable {ι : Type} (ξ : ι → Ω → ℝ)

lemma a33_xi_memLp (hξl : ∀ i, HasLaw (ξ i) (gaussianReal 0 1) P) (i : ι) : MemLp (ξ i) 2 P :=
  (hξl i).hasGaussianLaw.memLp_two

open Classical in
lemma a33_xi_inner (hξm : ∀ i, Measurable (ξ i)) (hξl : ∀ i, HasLaw (ξ i) (gaussianReal 0 1) P)
    (hξi : iIndepFun ξ P) (i j : ι) :
    ∫ ω, ξ i ω * ξ j ω ∂P = if i = j then 1 else 0 := by
  have hmean : ∀ i, ∫ ω, ξ i ω ∂P = 0 := fun i => by
    rw [(hξl i).integral_eq]; simp
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left_iff.2 (fun h => absurd rfl h)]
    have h1 := variance_eq_sub (a33_xi_memLp ξ hξl i)
    have h2 : Var[ξ i; P] = 1 := by
      rw [(hξl i).variance_eq]; simp
    rw [h2, hmean i] at h1
    simp only [Pi.pow_apply] at h1
    have : ∫ ω, ξ i ω * ξ i ω ∂P = ∫ ω, ξ i ω ^ 2 ∂P := by simp [sq]
    rw [this]; linarith
  · rw [ite_eq_right_iff.2 (fun h => absurd h hij)]
    have := (hξi.indepFun hij).integral_mul_eq_mul_integral (hξm i).aestronglyMeasurable
      (hξm j).aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, hmean i, hmean j]; simp

end Iso

lemma a33_lp_norm_sq (f : Lp ℝ 2 P) : ‖f‖ ^ 2 = ∫ ω, ((f : Ω → ℝ) ω) ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp [sq]

lemma a33_coeFn_sum {ι' : Type*} (J : Finset ι') (f : ι' → Lp ℝ 2 P) :
    ⇑(∑ i ∈ J, f i) =ᵐ[P] fun ω => ∑ i ∈ J, (f i : Ω → ℝ) ω := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℝ 2 P] with ω h
    simp [h]
  | insert a J ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ J, f i), ih] with ω h1 h2
    simp only [Finset.sum_insert ha, h1, h2, Pi.add_apply]

lemma a33_gram_psd {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {κ : Type}
    [Fintype κ] [DecidableEq κ] (h : κ → H) :
    (Matrix.of fun a b => ⟪h a, h b⟫ : Matrix κ κ ℝ).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine Matrix.IsHermitian.ext fun a b => ?_
    simp [real_inner_comm]
  · have : star x ⬝ᵥ ((Matrix.of fun a b => ⟪h a, h b⟫ : Matrix κ κ ℝ) *ᵥ x) =
        ⟪∑ a, x a • h a, ∑ a, x a • h a⟫ := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, star_trivial, sum_inner, inner_sum,
        inner_smul_left, inner_smul_right, conj_trivial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [real_inner_comm (h a) (h b)]
      ring
    rw [this]
    exact real_inner_self_nonneg

lemma a33_gram_quad {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {κ : Type}
    [Fintype κ] [DecidableEq κ] (h : κ → H) (t : κ → ℝ) :
    t ⬝ᵥ ((Matrix.of fun a b => ⟪h a, h b⟫ : Matrix κ κ ℝ) *ᵥ t) =
        ⟪∑ a, t a • h a, ∑ a, t a • h a⟫ := by
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, conj_trivial, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [real_inner_comm (h a) (h b)]
  ring

/-- The isonormal Gaussian process of a real Hilbert space: a family of measurable square-integrable
random variables `W h`, a.e. linear in `h`, with `E[W h W h'] = ⟪h, h'⟫`, whose finite families are
jointly centred Gaussian with the Gram covariance. -/
theorem a33_isonormal (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (W : H → Ω → ℝ),
      (∀ h, Measurable (W h)) ∧ (∀ h, MemLp (W h) 2 P) ∧
      (∀ (a b : ℝ) (h h' : H), W (a • h + b • h') =ᵐ[P] fun ω => a * W h ω + b * W h' ω) ∧
      (∀ {κ : Type} (h : κ → H) (t : κ → ℝ) (J : Finset κ),
        W (∑ a ∈ J, t a • h a) =ᵐ[P] fun ω => ∑ a ∈ J, t a * W (h a) ω) ∧
      (∀ h h', ∫ ω, W h ω * W h' ω ∂P = ⟪h, h'⟫) ∧
      (∀ g : H, P.map (W g) = gaussianReal 0 (Real.toNNReal (‖g‖ ^ 2))) ∧
      (∀ (κ : Type) [Fintype κ] [DecidableEq κ] (h : κ → H),
        P.map (fun ω => (WithLp.toLp 2 (fun a => W (h a) ω) : EuclideanSpace ℝ κ)) =
          multivariateGaussian 0 (Matrix.of fun a b => ⟪h a, h b⟫)) := by
  classical
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℝ H
  obtain ⟨Ω, mΩ, P, ξ, hξm, hξl, hξi, hP⟩ := exists_iid w (gaussianReal 0 1)
  haveI := hP
  have hξ2 := a33_xi_memLp ξ hξl
  have hξn := a33_xi_inner ξ hξm hξl hξi
  set e : w → Lp ℝ 2 P := fun i => (hξ2 i).toLp (ξ i) with he
  have he_inner : ∀ i j, ⟪e i, e j⟫ = if i = j then 1 else 0 := by
    intro i j
    rw [L2.inner_def]
    have : (fun a => ⟪(e i : Ω → ℝ) a, (e j : Ω → ℝ) a⟫) =ᵐ[P] fun a => ξ i a * ξ j a := by
      filter_upwards [(hξ2 i).coeFn_toLp, (hξ2 j).coeFn_toLp] with a h1 h2
      simp [he, h1, h2, mul_comm]
    rw [integral_congr_ae this, hξn]
    congr
  have he_norm : ∀ i, ‖e i‖ = 1 := by
    intro i
    have h1 := he_inner i i
    rw [real_inner_self_eq_norm_sq] at h1
    rw [ite_eq_left_iff.2 (fun h => absurd rfl h)] at h1
    nlinarith [norm_nonneg (e i)]
  let V : ∀ i : w, ℝ →ₗᵢ[ℝ] Lp ℝ 2 P := fun i => a33_line (e i) (he_norm i)
  have hV : OrthogonalFamily ℝ (fun _ : w => ℝ) V := by
    intro i j hij x y
    simp [V, a33_line_apply, inner_smul_left, inner_smul_right, he_inner, hij]
  let ℓ : H →ₗᵢ[ℝ] Lp ℝ 2 P := hV.linearIsometry.comp b.repr.toLinearIsometry
  let W : H → Ω → ℝ := fun h => (Lp.aestronglyMeasurable (ℓ h)).mk _
  have hWae : ∀ h, W h =ᵐ[P] ⇑(ℓ h) := fun h => (Lp.aestronglyMeasurable (ℓ h)).ae_eq_mk.symm
  have hWm : ∀ h, Measurable (W h) := fun h =>
    (Lp.aestronglyMeasurable (ℓ h)).stronglyMeasurable_mk.measurable
  have hW2 : ∀ h, MemLp (W h) 2 P := fun h => (Lp.memLp (ℓ h)).ae_eq (hWae h).symm
  have hlin : ∀ (a c : ℝ) (h h' : H),
      W (a • h + c • h') =ᵐ[P] fun ω => a * W h ω + c * W h' ω := by
    intro a c h h'
    have e1 : ℓ (a • h + c • h') = a • ℓ h + c • ℓ h' := by simp
    filter_upwards [hWae (a • h + c • h'), hWae h, hWae h', Lp.coeFn_add (a • ℓ h) (c • ℓ h'),
      Lp.coeFn_smul a (ℓ h), Lp.coeFn_smul c (ℓ h')] with ω h1 h2 h3 h4 h5 h6
    rw [h1, e1, h4]
    simp only [Pi.add_apply, h5, h6, Pi.smul_apply, smul_eq_mul, h2, h3]
  have hinner : ∀ h h', ∫ ω, W h ω * W h' ω ∂P = ⟪h, h'⟫ := by
    intro h h'
    rw [← LinearIsometry.inner_map_map ℓ h h', L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hWae h, hWae h'] with ω h1 h2
    rw [h1, h2]
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  have hsingle : ∀ g : H, P.map (W g) = gaussianReal 0 (Real.toNNReal (‖g‖ ^ 2)) := by
    intro g
    refine Measure.ext_of_charFun ?_
    funext t
    set c : w → ℝ := fun i => b.repr g i with hc
    have hsum : HasSum (fun i => V i (c i)) (ℓ g) := hV.hasSum_linearIsometry (b.repr g)
    have hsum' : Tendsto (fun J : Finset w => ∑ i ∈ J, V i (c i)) atTop (𝓝 (ℓ g)) := hsum
    let X : Finset w → Ω → ℝ := fun J ω => ∑ i ∈ J, c i * ξ i ω
    have hXm : ∀ J, Measurable (X J) := fun J =>
      Finset.measurable_sum _ fun i _ => (hξm i).const_mul _
    have hX2 : ∀ J, MemLp (X J) 2 P := fun J =>
      memLp_finset_sum (f := fun i ω => c i * ξ i ω) J fun i _ => (hξ2 i).const_mul _
    have hX_ae : ∀ J : Finset w, ⇑(∑ i ∈ J, V i (c i)) =ᵐ[P] X J := by
      intro J
      refine (a33_coeFn_sum J (fun i => V i (c i))).trans ?_
      have : ∀ i : w, (V i (c i) : Ω → ℝ) =ᵐ[P] fun ω => c i * ξ i ω := by
        intro i
        have h1 : V i (c i) = c i • e i := rfl
        rw [h1]
        filter_upwards [Lp.coeFn_smul (c i) (e i), (hξ2 i).coeFn_toLp] with ω h2 h3
        rw [h2, Pi.smul_apply, smul_eq_mul]
        exact congrArg (c i * ·) h3
      have hall : ∀ᵐ ω ∂P, ∀ i ∈ J, (V i (c i) : Ω → ℝ) ω = c i * ξ i ω :=
        (Filter.eventually_all_finset J).2 fun i _ => this i
      filter_upwards [hall] with ω hω
      exact Finset.sum_congr rfl fun i hi => hω i hi
    have hconv : Tendsto (fun J => ∫ ω, (X J ω - W g ω) ^ 2 ∂P) atTop (𝓝 0) := by
      have h0 := tendsto_iff_norm_sub_tendsto_zero.1 hsum'
      have h1 : Tendsto (fun J : Finset w => ‖∑ i ∈ J, V i (c i) - ℓ g‖ ^ 2) atTop (𝓝 0) := by
        simpa using h0.pow 2
      refine h1.congr fun J => ?_
      rw [a33_lp_norm_sq]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (∑ i ∈ J, V i (c i)) (ℓ g), hX_ae J, hWae g] with ω h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3]
    have hv : Tendsto (fun J : Finset w => ∑ i ∈ J, c i ^ 2) atTop (𝓝 (‖g‖ ^ 2)) := by
      have h := lp.hasSum_norm (p := 2) (by norm_num) (b.repr g)
      have h' : Tendsto (fun J : Finset w => ∑ i ∈ J, ‖(b.repr g) i‖ ^ (2 : ENNReal).toReal) atTop
          (𝓝 (‖b.repr g‖ ^ (2 : ENNReal).toReal)) := h
      simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
        LinearIsometryEquiv.norm_map] at h'
      exact h'
    have hlaw : ∀ (J : Finset w) (t : ℝ), charFun (P.map (X J)) t =
        Complex.exp (-(((∑ i ∈ J, c i ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2)) := by
      intro J t
      have hind : iIndepFun (J.restrict fun i ω => c i * ξ i ω) P :=
        (hξi.comp (fun i x => c i * x) (fun i => measurable_const_mul _)).restrict J
      have := iIndepFun.charFun_map_fun_finsetSum_eq_prod
        (X := fun i ω => c i * ξ i ω) (s := J) (P := P)
        (fun i _ => ((hξm i).const_mul _).aemeasurable) hind
      show charFun (P.map (fun ω => ∑ i ∈ J, c i * ξ i ω)) t = _
      rw [this]
      simp only [Finset.prod_apply]
      have hi : ∀ i : w, charFun (P.map (fun ω => c i * ξ i ω)) t =
          Complex.exp (-(((c i ^ 2 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2)) := by
        intro i
        have e1 : P.map (fun ω => c i * ξ i ω) = (P.map (ξ i)).map (fun x => c i * x) := by
          rw [Measure.map_map (measurable_const_mul _) (hξm i)]; rfl
        rw [e1, (hξl i).map_eq, gaussianReal_map_const_mul, charFun_gaussianReal]
        congr 1
        push_cast
        ring
      simp_rw [hi]
      rw [← Complex.exp_sum]
      congr 1
      push_cast
      rw [Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.sum_mul]
    have := a33_charFun_limit X (W g) hXm (hWm g) hX2 (hW2 g) hconv _ _ hv hlaw t
    rw [this, charFun_gaussianReal]
    congr 1
    simp [Real.coe_toNNReal _ (sq_nonneg ‖g‖)]
  have hW0 : W 0 =ᵐ[P] fun _ => 0 := by
    have := hlin 0 0 0 0
    simpa using this
  have hfin : ∀ {κ : Type} (h : κ → H) (t : κ → ℝ) (J : Finset κ),
      W (∑ a ∈ J, t a • h a) =ᵐ[P] fun ω => ∑ a ∈ J, t a * W (h a) ω := by
    intro κ h t J
    classical
    induction J using Finset.induction_on with
    | empty => simpa using hW0
    | insert a J ha ih =>
      rw [Finset.sum_insert ha]
      have h1 := hlin (t a) 1 (h a) (∑ a ∈ J, t a • h a)
      rw [one_smul] at h1
      filter_upwards [h1, ih] with ω h2 h3
      rw [h2, Finset.sum_insert ha, h3]
      ring
  refine ⟨Ω, mΩ, P, hP, W, hWm, hW2, hlin, hfin, hinner, hsingle, ?_⟩
  intro κ _ _ h
  refine Measure.ext_of_charFun ?_
  funext t
  have hS := a33_gram_psd h
  rw [charFun_multivariateGaussian hS]
  set g : H := ∑ a, t a • h a with hg
  have hVm : Measurable (fun ω => (WithLp.toLp 2 (fun a => W (h a) ω) : EuclideanSpace ℝ κ)) :=
    (PiLp.continuous_toLp 2 (fun _ : κ => ℝ)).measurable.comp
      (measurable_pi_iff.2 fun a => hWm (h a))
  rw [charFun_apply, integral_map hVm.aemeasurable (by fun_prop)]
  have hip : ∀ ω, ⟪(WithLp.toLp 2 (fun a => W (h a) ω) : EuclideanSpace ℝ κ), t⟫ =
      ∑ a, t a * W (h a) ω := by
    intro ω
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  have e1 : ∫ ω, Complex.exp (↑⟪(WithLp.toLp 2 (fun a => W (h a) ω) : EuclideanSpace ℝ κ), t⟫ *
      Complex.I) ∂P = ∫ ω, Complex.exp (((1 * W g ω : ℝ) : ℂ) * Complex.I) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hfin h (fun a => t a) Finset.univ] with ω hω
    rw [hip, one_mul]
    congr 3
    exact hω.symm
  rw [e1, ← a33_charFun_eq (W g) (hWm g) 1, hsingle g, charFun_gaussianReal]
  have hq : t ⬝ᵥ ((Matrix.of fun a b => ⟪h a, h b⟫ : Matrix κ κ ℝ) *ᵥ t) = ‖g‖ ^ 2 := by
    rw [a33_gram_quad h t, real_inner_self_eq_norm_sq]
  have hq' : t.ofLp ⬝ᵥ ((Matrix.of fun a b => ⟪h a, h b⟫ : Matrix κ κ ℝ) *ᵥ t.ofLp) = ‖g‖ ^ 2 := hq
  rw [hq']
  congr 1
  simp [Real.coe_toNNReal _ (sq_nonneg ‖g‖)]

end HRS.A33
