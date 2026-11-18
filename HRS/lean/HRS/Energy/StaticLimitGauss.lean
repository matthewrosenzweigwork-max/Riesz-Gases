import HRS.Energy.StaticLimitResponse
import HRS.Prob.HilbertCLT

/-!
# Existence of the Gaussian targets of Proposition 4.21 (work package STAT-4.21)

The susceptibility covariance `C_{β,μ}(φ,ψ) = ⟨P_μ φ, (I+βK_μ)⁻¹ P_μ ψ⟩_{L²(μ)}` defines a
trace-class covariance form on `E_m = H^{-m}_0(𝕋^d)`; the centered Gaussian measure with this
covariance exists by `exists_centeredGaussian_of_traceClass`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace HRS.StaticLimitAux

open HRS Torus

theorem separable_lp {ι : Type*} [Countable ι] : TopologicalSpace.SeparableSpace (lp (fun _ : ι => ℝ) 2) := by
  classical
  set S : Set (lp (fun _ : ι => ℝ) 2) := Set.range fun i : ι => lp.single (E := fun _ : ι => ℝ) 2 i (1 : ℝ) with hS
  have h1 : TopologicalSpace.IsSeparable S := (Set.countable_range _).isSeparable
  have h2 : TopologicalSpace.IsSeparable (Submodule.span ℝ S : Set (lp (fun _ : ι => ℝ) 2)) := h1.span
  have h3 : ∀ f : lp (fun _ : ι => ℝ) 2, f ∈ closure (Submodule.span ℝ S : Set (lp (fun _ : ι => ℝ) 2)) := by
    intro f
    have := lp.hasSum_single (p := 2) (by simp) f
    refine mem_closure_of_tendsto this (Filter.Eventually.of_forall fun s => ?_)
    refine Submodule.sum_mem _ fun i _ => ?_
    have : lp.single (E := fun _ : ι => ℝ) 2 i (f i) = f i • lp.single (E := fun _ : ι => ℝ) 2 i (1 : ℝ) := by
      rw [← lp.single_smul]; simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h4 : TopologicalSpace.IsSeparable (Set.univ : Set (lp (fun _ : ι => ℝ) 2)) := by
    refine h2.closure.mono ?_
    intro f _; exact h3 f
  exact (TopologicalSpace.isSeparable_univ_iff.mp h4)

instance instSepNeg (d : ℕ) (m : ℝ) : TopologicalSpace.SeparableSpace (NegSobolev d m) :=
  separable_lp (ι := NonzeroLattice d)

instance instSCNeg (d : ℕ) (m : ℝ) : SecondCountableTopology (NegSobolev d m) :=
  UniformSpace.secondCountable_of_separable _

section Eval

variable {d : ℕ} {m : ℝ}

/-- The weight `⟨k⟩^{-m}`. -/
def wgt (m : ℝ) (k : NonzeroLattice d) : ℝ := Lattice.jp k.1 ^ (-m)

theorem wgt_pos (k : NonzeroLattice d) : 0 < wgt m k := Real.rpow_pos_of_pos (jp_pos k.1) _

theorem summable_wgt_sq (hm : (d : ℝ) < 2 * m) : Summable fun k : NonzeroLattice d => wgt m k ^ 2 := by
  refine (summable_jp_rpow (d := d) m hm).congr fun k => ?_
  unfold wgt
  rw [jp_rpow_sq]; congr 1; ring

/-- The function `z ↦ ∑_k F̂(k) ⟨k⟩^{...}`-pairing: the test function associated to a dual vector. -/
def evalFun (m : ℝ) (x : NegSobolev d m) (z : Torus d) : ℝ :=
  ∑' k : NonzeroLattice d, NegSobolev.coord x k * (wgt m k * realMode k z)

theorem summable_evalFun (hm : (d : ℝ) < 2 * m) (x : NegSobolev d m) (z : Torus d) :
    Summable fun k : NonzeroLattice d => NegSobolev.coord x k * (wgt m k * realMode k z) := by
  obtain ⟨hx2, -⟩ := NegSobolev.coord_sq x
  have hcs := cs_tsum (fun k => |NegSobolev.coord x k|) (fun k => wgt m k) (fun _ => abs_nonneg _)
    (fun k => (wgt_pos k).le) (by simpa [sq_abs] using hx2) (summable_wgt_sq hm)
  refine Summable.of_norm_bounded (hcs.1.mul_right (Real.sqrt 2)) fun k => ?_
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (wgt_pos k)]
  calc |NegSobolev.coord x k| * (wgt m k * |realMode k z|)
      ≤ |NegSobolev.coord x k| * (wgt m k * Real.sqrt 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (abs_realMode_le k z) (wgt_pos k).le)
          (abs_nonneg _)
    _ = |NegSobolev.coord x k| * wgt m k * Real.sqrt 2 := by ring

/-- Uniform bound constant. -/
def evalConst (m : ℝ) : ℝ := Real.sqrt 2 * Real.sqrt (∑' k : NonzeroLattice d, wgt m k ^ 2)

theorem abs_evalFun_le (hm : (d : ℝ) < 2 * m) (x : NegSobolev d m) (z : Torus d) :
    |evalFun m x z| ≤ evalConst (d := d) m * ‖x‖ := by
  obtain ⟨hx2, hxn⟩ := NegSobolev.coord_sq x
  have hcs := cs_tsum (fun k => |NegSobolev.coord x k|) (fun k => wgt m k) (fun _ => abs_nonneg _)
    (fun k => (wgt_pos k).le) (by simpa [sq_abs] using hx2) (summable_wgt_sq hm)
  have hxs : Real.sqrt (∑' k, NegSobolev.coord x k ^ 2) = ‖x‖ := by
    rw [← hxn]; exact Real.sqrt_sq (norm_nonneg _)
  unfold evalFun
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm (summable_evalFun hm x z).norm).trans ?_
  calc ∑' k, ‖NegSobolev.coord x k * (wgt m k * realMode k z)‖
      ≤ ∑' k, |NegSobolev.coord x k| * wgt m k * Real.sqrt 2 := by
        refine Summable.tsum_le_tsum (fun k => ?_) (summable_evalFun hm x z).norm
          (hcs.1.mul_right _)
        rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos (wgt_pos k)]
        calc |NegSobolev.coord x k| * (wgt m k * |realMode k z|)
            ≤ |NegSobolev.coord x k| * (wgt m k * Real.sqrt 2) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (abs_realMode_le k z)
                (wgt_pos k).le) (abs_nonneg _)
          _ = |NegSobolev.coord x k| * wgt m k * Real.sqrt 2 := by ring
    _ = (∑' k, |NegSobolev.coord x k| * wgt m k) * Real.sqrt 2 := tsum_mul_right
    _ ≤ (Real.sqrt (∑' k, |NegSobolev.coord x k| ^ 2) * Real.sqrt (∑' k, wgt m k ^ 2)) * Real.sqrt 2 :=
        mul_le_mul_of_nonneg_right hcs.2 (Real.sqrt_nonneg _)
    _ = evalConst m * ‖x‖ := by
        simp only [sq_abs, hxs, evalConst]; ring

theorem continuous_evalFun (hm : (d : ℝ) < 2 * m) (x : NegSobolev d m) : Continuous (evalFun m x) := by
  obtain ⟨hx2, -⟩ := NegSobolev.coord_sq x
  have hcs := cs_tsum (fun k => |NegSobolev.coord x k|) (fun k => wgt m k) (fun _ => abs_nonneg _)
    (fun k => (wgt_pos k).le) (by simpa [sq_abs] using hx2) (summable_wgt_sq hm)
  refine continuous_tsum (u := fun k => |NegSobolev.coord x k| * wgt m k * Real.sqrt 2)
    (fun k => ?_) (hcs.1.mul_right _) fun k z => ?_
  · exact continuous_const.mul (continuous_const.mul (by
      unfold realMode
      split_ifs
      · exact continuous_const.mul (continuous_cosMode _)
      · exact continuous_const.mul (continuous_sinMode _)))
  · rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (wgt_pos k)]
    calc |NegSobolev.coord x k| * (wgt m k * |realMode k z|)
        ≤ |NegSobolev.coord x k| * (wgt m k * Real.sqrt 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (abs_realMode_le k z)
            (wgt_pos k).le) (abs_nonneg _)
      _ = |NegSobolev.coord x k| * wgt m k * Real.sqrt 2 := by ring

theorem evalFun_add (hm : (d : ℝ) < 2 * m) (x y : NegSobolev d m) :
    evalFun m (x + y) = evalFun m x + evalFun m y := by
  funext z
  simp only [evalFun, Pi.add_apply]
  rw [← (summable_evalFun hm x z).tsum_add (summable_evalFun hm y z)]
  refine tsum_congr fun k => ?_
  have : NegSobolev.coord (x + y) k = NegSobolev.coord x k + NegSobolev.coord y k := rfl
  rw [this]; ring

theorem evalFun_smul (hm : (d : ℝ) < 2 * m) (c : ℝ) (x : NegSobolev d m) :
    evalFun m (c • x) = c • evalFun m x := by
  funext z
  simp only [evalFun, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have : NegSobolev.coord (c • x) k = c * NegSobolev.coord x k := rfl
  rw [this]; ring

end Eval

section Cov

variable {d : ℕ} {m : ℝ} {a : Lattice d → ℝ} (μ : Measure (Torus d)) [IsProbabilityMeasure μ]

theorem evalConst_nonneg : 0 ≤ evalConst (d := d) m :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- The map `x ↦ [evalFun x] ∈ L²(μ)`. -/
def Wmap (hm : (d : ℝ) < 2 * m) : NegSobolev d m →L[ℝ] Lp ℝ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun x => cl μ (evalFun m x) (continuous_evalFun hm x)
      map_add' := fun x y => by
        refine Lp.ext ?_
        filter_upwards [cl_ae μ (continuous_evalFun hm (x + y)), cl_ae μ (continuous_evalFun hm x),
          cl_ae μ (continuous_evalFun hm y),
          Lp.coeFn_add (cl μ (evalFun m x) (continuous_evalFun hm x))
            (cl μ (evalFun m y) (continuous_evalFun hm y))] with z h1 h2 h3 h4
        rw [h1, h4, Pi.add_apply, h2, h3, evalFun_add hm]; rfl
      map_smul' := fun c x => by
        refine Lp.ext ?_
        filter_upwards [cl_ae μ (continuous_evalFun hm (c • x)), cl_ae μ (continuous_evalFun hm x),
          Lp.coeFn_smul c (cl μ (evalFun m x) (continuous_evalFun hm x))] with z h1 h2 h4
        rw [h1]
        show _ = (c • (cl μ (evalFun m x) (continuous_evalFun hm x) : Lp ℝ 2 μ)) z
        rw [h4, Pi.smul_apply, h2, evalFun_smul hm]; rfl }
    (evalConst (d := d) m)
    (fun x => by
      show ‖cl μ (evalFun m x) (continuous_evalFun hm x)‖ ≤ _
      refine norm_cl_le μ _ (mul_nonneg evalConst_nonneg (norm_nonneg _)) fun z => ?_
      exact abs_evalFun_le hm x z)

theorem Wmap_apply (hm : (d : ℝ) < 2 * m) (x : NegSobolev d m) :
    Wmap μ hm x = cl μ (evalFun m x) (continuous_evalFun hm x) := rfl

/-- The projection `P_μ` onto mean-zero functions as an operator on `L²(μ)`. -/
def Pmap : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  ContinuousLinearMap.id ℝ _ -
    (innerSL ℝ (cl μ (fun _ => (1 : ℝ)) continuous_const)).smulRight (cl μ (fun _ => (1 : ℝ)) continuous_const)

theorem Pmap_ae (f : Lp ℝ 2 μ) :
    (⇑(Pmap μ f) : Torus d → ℝ) =ᵐ[μ] fun x => f x - ∫ y, f y ∂μ := by
  have h1 : ⟪cl μ (fun _ => (1 : ℝ)) continuous_const, f⟫ = ∫ y, f y ∂μ := by
    rw [inner_cl_left]; simp
  have e : Pmap μ f = f - (⟪cl μ (fun _ => (1 : ℝ)) continuous_const, f⟫) • cl μ (fun _ => (1 : ℝ)) continuous_const := by
    simp [Pmap]
  rw [e]
  filter_upwards [Lp.coeFn_sub f (⟪cl μ (fun _ => (1 : ℝ)) continuous_const, f⟫ • cl μ (fun _ => (1 : ℝ)) continuous_const),
    Lp.coeFn_smul ⟪cl μ (fun _ => (1 : ℝ)) continuous_const, f⟫ (cl μ (fun _ => (1 : ℝ)) continuous_const),
    cl_ae μ (continuous_const (y := (1:ℝ)))] with x h1' h2 h3
  rw [h1', Pi.sub_apply, h2, Pi.smul_apply, h3, h1, smul_eq_mul, mul_one]

section Cov2

variable (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) {β : ℝ} (hβ : 0 ≤ β)

/-- The resolvent `(I + βK_μ)^{-1}` on `L²(μ)` (Lax-Milgram inverse). -/
def Rr : Lp ℝ 2 μ ≃L[ℝ] Lp ℝ 2 μ :=
  (Bform_coercive μ ha0 has hβ).continuousLinearEquivOfBilin.symm

include ha0 has hβ in
theorem Rr_spec (z k : Lp ℝ 2 μ) : ⟪z, k⟫ = Bform μ ha0 has β (Rr μ ha0 has hβ z) k := by
  have := (Bform_coercive μ ha0 has hβ).continuousLinearEquivOfBilin_apply
    ((Bform_coercive μ ha0 has hβ).continuousLinearEquivOfBilin.symm z) k
  simpa [Rr] using this

include ha0 has hβ in
theorem norm_Rr_le (z : Lp ℝ 2 μ) : ‖Rr μ ha0 has hβ z‖ ≤ ‖z‖ := by
  set h := Rr μ ha0 has hβ z with hh
  have h1 := Rr_spec μ ha0 has hβ z h
  rw [Bform_apply μ ha0 has] at h1
  have h2 : 0 ≤ β * ⟪Tco μ ha0 has h, Tco μ ha0 has h⟫ := mul_nonneg hβ real_inner_self_nonneg
  have h3 : ‖h‖ * ‖h‖ ≤ ⟪z, h⟫ := by
    rw [h1, real_inner_self_eq_norm_mul_norm]; linarith
  have h4 : ⟪z, h⟫ ≤ ‖z‖ * ‖h‖ := real_inner_le_norm z h
  by_cases h0 : ‖h‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have : ‖h‖ ≤ ‖z‖ := by
      have hpos : 0 < ‖h‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      nlinarith
    exact this

/-- The covariance form of the Gaussian target as a continuous bilinear form on `E_m`. -/
def Cmap (hm : (d : ℝ) < 2 * m) : NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ :=
  (innerSL ℝ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ →L[ℝ] ℝ).bilinearComp (Pmap μ ∘L Wmap μ hm)
    ((Rr μ ha0 has hβ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) ∘L (Pmap μ ∘L Wmap μ hm))

theorem Cmap_apply (hm : (d : ℝ) < 2 * m) (x y : NegSobolev d m) :
    Cmap μ ha0 has hβ hm x y = ⟪Pmap μ (Wmap μ hm x), Rr μ ha0 has hβ (Pmap μ (Wmap μ hm y))⟫ := by
  simp [Cmap]

include ha0 has hβ in
theorem Cmap_eq_B (hm : (d : ℝ) < 2 * m) (x y : NegSobolev d m) :
    Cmap μ ha0 has hβ hm x y = Bform μ ha0 has β (Rr μ ha0 has hβ (Pmap μ (Wmap μ hm x)))
      (Rr μ ha0 has hβ (Pmap μ (Wmap μ hm y))) := by
  rw [Cmap_apply]
  exact Rr_spec μ ha0 has hβ _ _

include ha0 has hβ in
theorem Cmap_symm (hm : (d : ℝ) < 2 * m) (x y : NegSobolev d m) :
    Cmap μ ha0 has hβ hm x y = Cmap μ ha0 has hβ hm y x := by
  rw [Cmap_eq_B μ ha0 has hβ hm, Cmap_eq_B μ ha0 has hβ hm, Bform_apply μ ha0 has,
    Bform_apply μ ha0 has, real_inner_comm, real_inner_comm (Tco μ ha0 has _)]

include ha0 has hβ in
theorem Cmap_nonneg (hm : (d : ℝ) < 2 * m) (x : NegSobolev d m) :
    0 ≤ Cmap μ ha0 has hβ hm x x := by
  rw [Cmap_eq_B μ ha0 has hβ hm, Bform_apply μ ha0 has]
  exact add_nonneg real_inner_self_nonneg (mul_nonneg hβ real_inner_self_nonneg)

include ha0 has hβ in
theorem Cmap_le (hm : (d : ℝ) < 2 * m) (x : NegSobolev d m) :
    Cmap μ ha0 has hβ hm x x ≤ ‖Pmap μ (Wmap μ hm x)‖ ^ 2 := by
  rw [Cmap_apply]
  calc ⟪Pmap μ (Wmap μ hm x), Rr μ ha0 has hβ (Pmap μ (Wmap μ hm x))⟫
      ≤ ‖Pmap μ (Wmap μ hm x)‖ * ‖Rr μ ha0 has hβ (Pmap μ (Wmap μ hm x))‖ :=
        real_inner_le_norm _ _
    _ ≤ ‖Pmap μ (Wmap μ hm x)‖ * ‖Pmap μ (Wmap μ hm x)‖ :=
        mul_le_mul_of_nonneg_left (norm_Rr_le μ ha0 has hβ _) (norm_nonneg _)
    _ = _ := by ring

theorem evalFun_single (k : NonzeroLattice d) (z : Torus d) :
    evalFun m (show NegSobolev d m from lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k (1 : ℝ)) z
      = wgt m k * realMode k z := by
  unfold evalFun
  rw [tsum_eq_single k]
  · simp [NegSobolev.coord]
  · intro j hj
    simp [NegSobolev.coord, lp.single_apply, hj]

/-- The identity isometry `E_m ≃ ℓ²`. -/
def negRepr (d : ℕ) (m : ℝ) : NegSobolev d m ≃ₗᵢ[ℝ] lp (fun _ : NonzeroLattice d => ℝ) 2 where
  toFun := id
  invFun := id
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  norm_map' := fun _ => rfl

/-- The standard Hilbert basis of `E_m`. -/
def negBasis (d : ℕ) (m : ℝ) : HilbertBasis (NonzeroLattice d) ℝ (NegSobolev d m) :=
  HilbertBasis.ofRepr (negRepr d m)

theorem negBasis_apply (k : NonzeroLattice d) :
    (negBasis d m k : NegSobolev d m) =
      (show NegSobolev d m from lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k (1 : ℝ)) := by
  classical
  rw [← HilbertBasis.repr_symm_single]; rfl

include ha0 has hβ in
theorem Cmap_trace (hm : (d : ℝ) < 2 * m) :
    ∃ (ι : Type) (b : HilbertBasis ι ℝ (NegSobolev d m)),
      Summable fun i => Cmap μ ha0 has hβ hm (b i) (b i) := by
  refine ⟨NonzeroLattice d, negBasis d m, ?_⟩
  have hb := negBasis_apply (d := d) (m := m)
  refine Summable.of_nonneg_of_le (fun k => Cmap_nonneg μ ha0 has hβ hm _)
    (fun k => ?_) ((summable_wgt_sq (m := m) hm).mul_left (2 * ‖Pmap μ‖ ^ 2))
  rw [hb k]
  refine (Cmap_le μ ha0 has hβ hm _).trans ?_
  have h1 : ‖Wmap μ hm (show NegSobolev d m from lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k (1 : ℝ))‖
      ≤ Real.sqrt 2 * wgt m k := by
    rw [Wmap_apply]
    refine norm_cl_le μ _ (mul_nonneg (Real.sqrt_nonneg _) (wgt_pos k).le) fun z => ?_
    rw [evalFun_single, abs_mul, abs_of_pos (wgt_pos k)]
    calc wgt m k * |realMode k z| ≤ wgt m k * Real.sqrt 2 :=
          mul_le_mul_of_nonneg_left (abs_realMode_le k z) (wgt_pos k).le
      _ = _ := by ring
  have h2 := (Pmap μ).le_opNorm (Wmap μ hm (show NegSobolev d m from lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k (1 : ℝ)))
  have h3 : ‖Pmap μ (Wmap μ hm (show NegSobolev d m from lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k (1 : ℝ)))‖
      ≤ ‖Pmap μ‖ * (Real.sqrt 2 * wgt m k) :=
    h2.trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
  have h4 := pow_le_pow_left₀ (norm_nonneg _) h3 2
  calc _ ≤ (‖Pmap μ‖ * (Real.sqrt 2 * wgt m k)) ^ 2 := h4
    _ = 2 * ‖Pmap μ‖ ^ 2 * wgt m k ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]; ring

end Cov2

section Link

variable {d : ℕ} {m : ℝ}

theorem summable_weighted_smooth (m : ℝ) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * funRealCoeff φ k ^ 2 := by
  have hd : ∀ n : ℕ, ContDiff ℝ n (lift φ) := fun n =>
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift φ) from hφ).of_le (by exact_mod_cast le_top)
  have hint : Integrable φ :=
    (continuous_of_continuous_lift (hd 0).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  obtain ⟨n, hn⟩ := exists_nat_gt (m + (d : ℝ) / 2)
  obtain ⟨B, hB⟩ := fcoef_pow_decay (hd n)
  have hs := summable_jp_rpow (d := d) ((n : ℝ) - m) (by linarith)
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (Real.rpow_nonneg (jp_pos _).le _) (sq_nonneg _)) (fun k => ?_)
    (hs.mul_left (2 * B ^ 2))
  have hj := jp_pos k.1
  have h1 := two_mul_norm_fcoef_sq hint k
  have h2 : funRealCoeff φ k ^ 2 ≤ 2 * ‖fcoef φ k.1‖ ^ 2 := by
    rw [h1]; nlinarith [sq_nonneg (funRealCoeff φ (negNZ d k))]
  have hJ : 0 < Lattice.jp k.1 ^ n := pow_pos hj n
  have h3 : ‖fcoef φ k.1‖ * Lattice.jp k.1 ^ n ≤ B := hB k
  have h3' : (‖fcoef φ k.1‖ * Lattice.jp k.1 ^ n) ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ (by positivity) h3 2
  have h4 : ‖fcoef φ k.1‖ ^ 2 ≤ B ^ 2 / (Lattice.jp k.1 ^ n) ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith [h3']
  have h5 : Lattice.jp k.1 ^ (-(2 * ((n : ℝ) - m))) =
      Lattice.jp k.1 ^ (2 * m) / (Lattice.jp k.1 ^ n) ^ 2 := by
    rw [show -(2 * ((n : ℝ) - m)) = 2 * m + (-((2 * n : ℕ) : ℝ)) by push_cast; ring,
      Real.rpow_add hj, Real.rpow_neg hj.le, Real.rpow_natCast, pow_mul', div_eq_mul_inv]
  rw [h5]
  have h6 : 0 ≤ Lattice.jp k.1 ^ (2 * m) := Real.rpow_nonneg hj.le _
  calc Lattice.jp k.1 ^ (2 * m) * funRealCoeff φ k ^ 2
      ≤ Lattice.jp k.1 ^ (2 * m) * (2 * (B ^ 2 / (Lattice.jp k.1 ^ n) ^ 2)) :=
        mul_le_mul_of_nonneg_left (h2.trans (by linarith)) h6
    _ = _ := by ring

/-- The vector of `E_m` representing `F ↦ F(φ)`. -/
def avec (m : ℝ) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) : NegSobolev d m :=
  (⟨fun k : NonzeroLattice d => Lattice.jp k.1 ^ m * funRealCoeff φ k,
    (memℓp_two_iff _).2 ((summable_weighted_smooth m hφ).congr fun k => by
      rw [mul_pow, jp_rpow_sq])⟩ : lp (fun _ : NonzeroLattice d => ℝ) 2)

theorem coord_avec (m : ℝ) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (k : NonzeroLattice d) :
    NegSobolev.coord (avec m hφ) k = Lattice.jp k.1 ^ m * funRealCoeff φ k := rfl

theorem eval_eq_inner (m : ℝ) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (F : NegSobolev d m) :
    NegSobolev.eval F φ = ⟪F, avec m hφ⟫ := by
  show _ = ⟪(show lp (fun _ : NonzeroLattice d => ℝ) 2 from F), (show lp (fun _ : NonzeroLattice d => ℝ) 2 from avec m hφ)⟫
  rw [lp.inner_eq_tsum]
  unfold NegSobolev.eval NegSobolev.fourierCoeff
  refine tsum_congr fun k => ?_
  have e : (⟪(show lp (fun _ : NonzeroLattice d => ℝ) 2 from F) k,
      (show lp (fun _ : NonzeroLattice d => ℝ) 2 from avec m hφ) k⟫) =
      NegSobolev.coord (avec m hφ) k * NegSobolev.coord F k := by
    simp only [RCLike.inner_apply, conj_trivial]; rfl
  rw [e, coord_avec]; ring

end Link

theorem continuous_of_smooth {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) : Continuous φ :=
  continuous_of_continuous_lift
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift φ) from hφ).continuous

theorem summable_fcoef_smooth {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Summable fun k : Lattice d => ‖fcoef φ k‖ :=
  summable_fcoef_of_contDiff fun n =>
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift φ) from hφ).of_le (by exact_mod_cast le_top)

theorem evalFun_avec (m : ℝ) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (z : Torus d) :
    evalFun m (avec m hφ) z = φ z - Torus.mean φ := by
  rw [← (hasSum_realExpansion (continuous_of_smooth hφ) (summable_fcoef_smooth hφ) z).tsum_eq]
  unfold evalFun
  refine tsum_congr fun k => ?_
  rw [coord_avec]; unfold wgt
  have h : Lattice.jp k.1 ^ m * Lattice.jp k.1 ^ (-m) = 1 := by
    rw [← Real.rpow_add (jp_pos _)]; simp
  calc Lattice.jp k.1 ^ m * funRealCoeff φ k * (Lattice.jp k.1 ^ (-m) * realMode k z)
      = (Lattice.jp k.1 ^ m * Lattice.jp k.1 ^ (-m)) * (funRealCoeff φ k * realMode k z) := by ring
    _ = _ := by rw [h, one_mul]

section Link2

variable {a : Lattice d → ℝ} (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
  (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) {β : ℝ} (hβ : 0 ≤ β)

theorem Pmap_Wmap_avec (hm : (d : ℝ) < 2 * m) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Pmap μ (Wmap μ hm (avec m hφ)) =
      cl μ (fun x => φ x - pair μ φ) ((continuous_of_smooth hφ).sub continuous_const) := by
  have hc := continuous_of_smooth hφ
  have hW : (⇑(Wmap μ hm (avec m hφ)) : Torus d → ℝ) =ᵐ[μ] fun x => φ x - Torus.mean φ := by
    rw [Wmap_apply]
    filter_upwards [cl_ae μ (continuous_evalFun hm (avec m hφ))] with x hx
    rw [hx, evalFun_avec]
  have hint : ∫ y, (⇑(Wmap μ hm (avec m hφ)) : Torus d → ℝ) y ∂μ = pair μ φ - Torus.mean φ := by
    rw [integral_congr_ae hW, integral_sub
      (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (integrable_const _)]
    simp [pair]
  refine Lp.ext ?_
  filter_upwards [Pmap_ae μ (Wmap μ hm (avec m hφ)),
    cl_ae μ (f := fun x => φ x - pair μ φ) (hc.sub continuous_const), hW] with x h1 h2 h3
  rw [h1, h2, h3, hint]; ring

include ha0 has hβ in
theorem Cmap_avec (hm : (d : ℝ) < 2 * m) {φ ψ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    (hψ : Torus.IsSmooth ψ) :
    Cmap μ ha0 has hβ hm (avec m hφ) (avec m hψ) = susceptibilityCov (specKernel a) μ β φ ψ := by
  have hcψ := continuous_of_smooth hψ
  rw [Cmap_apply, Pmap_Wmap_avec μ hm hφ, Pmap_Wmap_avec μ hm hψ]
  set zψ := cl μ (fun x => ψ x - pair μ ψ) (hcψ.sub continuous_const) with hzψ
  have hr : IsResponse (specKernel a) μ β ψ ⇑(Rr μ ha0 has hβ zψ) :=
    isResponse_of_solution μ ha0 has hβ hcψ _ (fun k => Rr_spec μ ha0 has hβ zψ k)
  have hex : ∃ h, IsResponse (specKernel a) μ β ψ h := ⟨_, hr⟩
  unfold susceptibilityCov responseInverse
  rw [dif_pos hex]
  have hu := isResponse_unique μ ha0 has hβ hex.choose_spec hr
  unfold l2Inner
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hu, cl_ae μ (f := fun x => φ x - pair μ φ) ((continuous_of_smooth hφ).sub continuous_const)]
    with x h1 h2
  rw [h1, h2]
  simp only [RCLike.inner_apply, conj_trivial, projMean]
  ring

include ha0 has hβ in
theorem exists_gauss_spec (hm : (d : ℝ) < 2 * m) :
    ∃ γ : Measure (NegSobolev d m), IsProbabilityMeasure γ ∧ IsCenteredGaussian γ ∧
      ∀ φ ψ : Torus d → ℝ, Torus.IsSmooth φ → Torus.IsSmooth ψ →
        ∫ F, NegSobolev.eval F φ * NegSobolev.eval F ψ ∂γ =
          susceptibilityCov (specKernel a) μ β φ ψ := by
  obtain ⟨γ, hp, hg, hcov⟩ := exists_centeredGaussian_of_traceClass (Cmap μ ha0 has hβ hm)
    ⟨Cmap_symm μ ha0 has hβ hm, Cmap_nonneg μ ha0 has hβ hm, Cmap_trace μ ha0 has hβ hm⟩
  refine ⟨γ, hp, hg, fun φ ψ hφ hψ => ?_⟩
  have := hg.1
  have hmem : MemLp id 2 γ := ProbabilityTheory.IsGaussian.memLp_two_id
  have h := ProbabilityTheory.covarianceBilin_apply hmem (avec m hφ) (avec m hψ)
  rw [hcov, HilbertCLTAux.gaussian_mean_zero hg, Cmap_avec μ ha0 has hβ hm hφ hψ] at h
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun F => ?_)
  simp only [Pi.zero_apply, sub_zero, id]
  rw [eval_eq_inner m hφ, eval_eq_inner m hψ, real_inner_comm (avec m hφ), real_inner_comm (avec m hψ)]

end Link2


end Cov

end HRS.StaticLimitAux

