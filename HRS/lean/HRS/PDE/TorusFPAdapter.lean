import HRS.Appendix.CepaFlow
import HRS.PDE.Fourier

/-!
# Packet D1: adapter `Config d N ≃ Torus (N*d)`

`Config d N = Fin N → UnitAddTorus (Fin d)` and `Torus (N*d) = Fin (N*d) → UnitAddCircle`
are identified through `finProdFinEquiv : Fin N × Fin d ≃ Fin (N*d)`.  This file defines the
measurable/topological/additive equivalence `d1_configEquiv`, the matching continuous linear
equivalence `d1_eucEquiv : (Fin N → Euc d) ≃L[ℝ] Euc (N*d)` of the covering spaces, and proves
that they intertwine `Torus.mk`, `Torus.rep`, volume, translations, `IsCk`, gradients and
Laplacians (the shapes used by `fkeGenerator`, `configDiv`, `configLift` in
`HRS/Stochastic/SelectedFlow.lean`).  Everything in this file is proved.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS

variable {d N : ℕ}

/-- The index equivalence `Fin N × Fin d ≃ Fin (N*d)`. -/
def d1_idx (d N : ℕ) : Fin N × Fin d ≃ Fin (N * d) := finProdFinEquiv

/-- The identification of configurations with points of the big torus `𝕋^{N d}`. -/
def d1_configEquiv (d N : ℕ) : Config d N ≃ᵐ Torus (N * d) :=
  (MeasurableEquiv.curry (Fin N) (Fin d) UnitAddCircle).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (N * d) => UnitAddCircle) (d1_idx d N))

theorem d1_configEquiv_apply (X : Config d N) (m : Fin (N * d)) :
    d1_configEquiv d N X m = X ((d1_idx d N).symm m).1 ((d1_idx d N).symm m).2 := by
  simp [d1_configEquiv, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast,
    Function.uncurry]

theorem d1_configEquiv_symm_apply (Z : Torus (N * d)) (i : Fin N) (j : Fin d) :
    (d1_configEquiv d N).symm Z i j = Z (d1_idx d N (i, j)) := by
  have h : d1_configEquiv d N ((d1_configEquiv d N).symm Z) = Z := (d1_configEquiv d N).apply_symm_apply Z
  have := congrFun h (d1_idx d N (i, j))
  rw [d1_configEquiv_apply] at this
  simpa using this


/-- Currying is volume preserving. -/
theorem d1_curry_symm_measurePreserving :
    MeasurePreserving (MeasurableEquiv.curry (Fin N) (Fin d) UnitAddCircle).symm
      (volume : Measure (Config d N)) (volume : Measure (Fin N × Fin d → UnitAddCircle)) where
  measurable := (MeasurableEquiv.curry (Fin N) (Fin d) UnitAddCircle).symm.measurable
  map_eq := by
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [MeasurableEquiv.map_apply]
    have : (MeasurableEquiv.curry (Fin N) (Fin d) UnitAddCircle).symm ⁻¹' Set.univ.pi s =
        Set.univ.pi fun i : Fin N => Set.univ.pi fun j : Fin d => s (i, j) := by
      ext X
      simp [MeasurableEquiv.coe_curry_symm, Function.uncurry]
    rw [this]
    show (Measure.pi fun _ : Fin N => (Measure.pi fun _ : Fin d => (volume : Measure UnitAddCircle)))
      (Set.univ.pi fun i : Fin N => Set.univ.pi fun j : Fin d => s (i, j)) = _
    rw [Measure.pi_pi]
    simp_rw [Measure.pi_pi]
    exact (Fintype.prod_prod_type (fun p : Fin N × Fin d => (volume : Measure UnitAddCircle) (s p))).symm

theorem d1_configEquiv_measurePreserving (d N : ℕ) :
    MeasurePreserving (d1_configEquiv d N) (volume : Measure (Config d N))
      (volume : Measure (Torus (N * d))) :=
  (volume_measurePreserving_piCongrLeft (fun _ : Fin (N * d) => UnitAddCircle) (d1_idx d N)).comp
    d1_curry_symm_measurePreserving

theorem d1_configEquiv_symm_measurePreserving (d N : ℕ) :
    MeasurePreserving (d1_configEquiv d N).symm (volume : Measure (Torus (N * d)))
      (volume : Measure (Config d N)) :=
  (d1_configEquiv_measurePreserving d N).symm _

theorem d1_configEquiv_continuous (d N : ℕ) : Continuous (d1_configEquiv d N) := by
  refine continuous_pi fun m => ?_
  simp_rw [d1_configEquiv_apply]
  exact (continuous_apply _).comp (continuous_apply _)

theorem d1_configEquiv_symm_continuous (d N : ℕ) : Continuous (d1_configEquiv d N).symm := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp_rw [d1_configEquiv_symm_apply]
  exact continuous_apply _

/-- The homeomorphism underlying `d1_configEquiv`. -/
def d1_configHomeo (d N : ℕ) : Config d N ≃ₜ Torus (N * d) where
  toEquiv := (d1_configEquiv d N).toEquiv
  continuous_toFun := d1_configEquiv_continuous d N
  continuous_invFun := d1_configEquiv_symm_continuous d N

theorem d1_configEquiv_add (X Y : Config d N) :
    d1_configEquiv d N (X + Y) = d1_configEquiv d N X + d1_configEquiv d N Y := by
  funext m; simp [d1_configEquiv_apply]

theorem d1_configEquiv_sub (X Y : Config d N) :
    d1_configEquiv d N (X - Y) = d1_configEquiv d N X - d1_configEquiv d N Y := by
  funext m; simp [d1_configEquiv_apply]

theorem d1_configEquiv_zero : d1_configEquiv d N 0 = 0 := by
  funext m; simp [d1_configEquiv_apply]

theorem d1_configEquiv_neg (X : Config d N) : d1_configEquiv d N (-X) = -d1_configEquiv d N X := by
  funext m; simp [d1_configEquiv_apply]

/-- Translations: `φ(· - a)` transported along the adapter. -/
theorem d1_translate_comp (a : Config d N) (φ : Torus (N * d) → ℝ) (X : Config d N) :
    Torus.translate (d1_configEquiv d N a) φ (d1_configEquiv d N X) =
      (φ ∘ d1_configEquiv d N) (X - a) := by
  simp [Torus.translate, d1_configEquiv_sub]

/-- Translation invariance of the volume on `Config d N` (as a corollary of the adapter). -/
theorem d1_volume_map_configEquiv (d N : ℕ) :
    (volume : Measure (Config d N)).map (d1_configEquiv d N) = volume :=
  (d1_configEquiv_measurePreserving d N).map_eq

theorem d1_integral_configEquiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Torus (N * d) → E) :
    ∫ X : Config d N, f (d1_configEquiv d N X) = ∫ x : Torus (N * d), f x :=
  (d1_configEquiv_measurePreserving d N).integral_comp' f


/-! ### The covering spaces -/

/-- The linear identification `(Fin N → ℝ^d) ≃ ℝ^{N d}` of the covering spaces. -/
def d1_eucLinEquiv (d N : ℕ) : (Fin N → Euc d) ≃ₗ[ℝ] Euc (N * d) where
  toFun Y := WithLp.toLp 2 fun m => (Y ((d1_idx d N).symm m).1).ofLp ((d1_idx d N).symm m).2
  invFun Z := fun i => WithLp.toLp 2 fun j => Z.ofLp (d1_idx d N (i, j))
  map_add' Y Y' := by ext m; simp
  map_smul' c Y := by ext m; simp
  left_inv Y := by funext i; ext j; simp
  right_inv Z := by ext m; simp

/-- The continuous linear equivalence of the covering spaces. -/
def d1_eucEquiv (d N : ℕ) : (Fin N → Euc d) ≃L[ℝ] Euc (N * d) :=
  (d1_eucLinEquiv d N).toContinuousLinearEquiv

theorem d1_eucEquiv_apply (Y : Fin N → Euc d) (m : Fin (N * d)) :
    (d1_eucEquiv d N Y).ofLp m = (Y ((d1_idx d N).symm m).1).ofLp ((d1_idx d N).symm m).2 := rfl

theorem d1_eucEquiv_symm_apply (Z : Euc (N * d)) (i : Fin N) (j : Fin d) :
    ((d1_eucEquiv d N).symm Z i).ofLp j = Z.ofLp (d1_idx d N (i, j)) := rfl

/-- The covering maps correspond: `e (mk Y) = mk (E Y)`. -/
theorem d1_configEquiv_mk (Y : Fin N → Euc d) :
    d1_configEquiv d N (fun i => Torus.mk (Y i)) = Torus.mk (d1_eucEquiv d N Y) := by
  funext m
  rw [d1_configEquiv_apply]
  simp [Torus.mk, d1_eucEquiv_apply]

/-- The canonical representatives correspond. -/
theorem d1_eucEquiv_rep (X : Config d N) :
    d1_eucEquiv d N (fun i => Torus.rep (X i)) = Torus.rep (d1_configEquiv d N X) := by
  ext m
  rw [d1_eucEquiv_apply]
  simp [Torus.rep, d1_configEquiv_apply]

theorem d1_configEquiv_symm_mk (y : Euc (N * d)) :
    (d1_configEquiv d N).symm (Torus.mk y) = fun i => Torus.mk ((d1_eucEquiv d N).symm y i) := by
  apply (d1_configEquiv d N).injective
  rw [(d1_configEquiv d N).apply_symm_apply, d1_configEquiv_mk, ContinuousLinearEquiv.apply_symm_apply]

/-- The basis vectors correspond. -/
theorem d1_eucEquiv_configBasis (k : Fin N × Fin d) :
    d1_eucEquiv d N (configBasis d N k) = EuclideanSpace.single (d1_idx d N k) 1 := by
  ext m
  obtain ⟨⟨i, j⟩, rfl⟩ := (d1_idx d N).surjective m
  rw [d1_eucEquiv_apply, Equiv.symm_apply_apply]
  simp only [configBasis, PiLp.single_apply, Pi.single_apply, EquivLike.apply_eq_iff_eq]
  by_cases h1 : i = k.1
  · by_cases h2 : j = k.2
    · have : (i, j) = k := Prod.ext h1 h2
      subst this; simp
    · subst h1
      have : ((k.1, j) : Fin N × Fin d) ≠ k := fun h => h2 (by simpa using congrArg Prod.snd h)
      simp [h2, this]
  · have : (i, j) ≠ k := fun h => h1 (by rw [← h])
    simp [h1, this]

theorem d1_inner_eucEquiv (Y Y' : Fin N → Euc d) :
    inner ℝ (d1_eucEquiv d N Y) (d1_eucEquiv d N Y') = ∑ i, inner ℝ (Y i) (Y' i) := by
  rw [PiLp.inner_apply, ← (d1_idx d N).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [d1_eucEquiv_apply, Equiv.symm_apply_apply]

theorem d1_norm_sq_eucEquiv (Y : Fin N → Euc d) :
    ‖d1_eucEquiv d N Y‖ ^ 2 = ∑ i, ‖Y i‖ ^ 2 := by
  have h := d1_inner_eucEquiv Y Y
  simpa [real_inner_self_eq_norm_sq] using h


/-! ### Smooth functions, gradients, Laplacians -/

/-- A function `φ` on the big torus read on the covering space `Fin N → ℝ^d` of the configuration
space (this is `configLift (fun _ => φ ∘ d1_configEquiv d N)`). -/
def d1_cl {E : Type*} (φ : Torus (N * d) → E) : (Fin N → Euc d) → E :=
  fun Y => φ (d1_configEquiv d N fun i => Torus.mk (Y i))

theorem d1_cl_eq {E : Type*} (φ : Torus (N * d) → E) :
    d1_cl φ = Torus.lift φ ∘ d1_eucEquiv d N := by
  funext Y
  simp [d1_cl, Torus.lift, d1_configEquiv_mk]

theorem d1_configLift_comp {E : Type*} (φ : Torus (N * d) → ℝ) (r : ℝ) :
    configLift (fun _ X => φ (d1_configEquiv d N X)) r = d1_cl φ := rfl

theorem d1_isCk_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : WithTop ℕ∞)
    (φ : Torus (N * d) → E) : Torus.IsCk k φ ↔ ContDiff ℝ k (d1_cl φ) := by
  rw [d1_cl_eq]
  exact ((d1_eucEquiv d N).contDiff_comp_iff (f := Torus.lift φ) (n := k)).symm

theorem d1_fderiv_cl (φ : Torus (N * d) → ℝ) (Y v : Fin N → Euc d) :
    fderiv ℝ (d1_cl φ) Y v = fderiv ℝ (Torus.lift φ) (d1_eucEquiv d N Y) (d1_eucEquiv d N v) := by
  rw [d1_cl_eq]
  rw [(d1_eucEquiv d N).comp_right_fderiv]
  rfl

/-- Gradient transfer: the derivative of the configuration-space lift in the direction `v` is the
inner product of the torus gradient with the transported direction. -/
theorem d1_fderiv_cl_eq_inner (φ : Torus (N * d) → ℝ) (X : Config d N) (v : Fin N → Euc d) :
    fderiv ℝ (d1_cl φ) (fun i => Torus.rep (X i)) v =
      inner ℝ (Torus.grad φ (d1_configEquiv d N X)) (d1_eucEquiv d N v) := by
  rw [d1_fderiv_cl, d1_eucEquiv_rep]
  unfold Torus.grad gradient
  rw [InnerProductSpace.toDual_symm_apply]

/-- Partial derivatives: `∂_{(i,j)}` of the lift is `∂_{idx (i,j)}` on the big torus. -/
theorem d1_partialDeriv (φ : Torus (N * d) → ℝ) (X : Config d N) (k : Fin N × Fin d) :
    Torus.partialDeriv (d1_idx d N k) φ (d1_configEquiv d N X) =
      fderiv ℝ (d1_cl φ) (fun i => Torus.rep (X i)) (configBasis d N k) := by
  rw [d1_fderiv_cl, d1_eucEquiv_rep, d1_eucEquiv_configBasis]
  rfl

/-- The `idx (i,j)`-th component of the torus gradient is the directional derivative of the lift
in the coordinate direction `(i,j)`. -/
theorem d1_grad_apply (φ : Torus (N * d) → ℝ) (X : Config d N) (k : Fin N × Fin d) :
    (Torus.grad φ (d1_configEquiv d N X)).ofLp (d1_idx d N k) =
      fderiv ℝ (d1_cl φ) (fun i => Torus.rep (X i)) (configBasis d N k) := by
  rw [d1_fderiv_cl_eq_inner, d1_eucEquiv_configBasis, EuclideanSpace.inner_single_right]
  simp

theorem d1_fderiv2_cl (φ : Torus (N * d) → ℝ) (Y v w : Fin N → Euc d) :
    fderiv ℝ (fderiv ℝ (d1_cl φ)) Y v w =
      fderiv ℝ (fderiv ℝ (Torus.lift φ)) (d1_eucEquiv d N Y) (d1_eucEquiv d N v)
        (d1_eucEquiv d N w) := by
  have h := (d1_eucEquiv d N).iteratedFDerivWithin_comp_right (Torus.lift φ)
    uniqueDiffOn_univ (Set.mem_univ (d1_eucEquiv d N Y)) 2
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ,
    ← d1_cl_eq] at h
  have h2 := congrArg (fun L => L ![v, w]) h
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h2
  simpa using h2

/-- Laplacian transfer: `Δφ(e X)` is the sum of the double directional derivatives of the lift in
the coordinate directions (the shape used in `fkeGenerator`). -/
theorem d1_laplacian (φ : Torus (N * d) → ℝ) (X : Config d N) :
    Torus.laplacian φ (d1_configEquiv d N X) =
      ∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ (d1_cl φ)) (fun i => Torus.rep (X i))
        (configBasis d N k) (configBasis d N k) := by
  unfold Torus.laplacian
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (Torus.lift φ)
    (EuclideanSpace.basisFun (Fin (N * d)) ℝ)]
  beta_reduce
  rw [← (d1_idx d N).sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [d1_fderiv2_cl, d1_eucEquiv_rep, d1_eucEquiv_configBasis, iteratedFDeriv_two_apply]
  simp [EuclideanSpace.basisFun_apply]

/-- A drift acting blockwise: `D(φ)[v] = ∑_i D(φ)[Pi.single i (v i)]` (the shape of `fkeGenerator`). -/
theorem d1_fderiv_cl_blocks (φ : Torus (N * d) → ℝ) (Y v : Fin N → Euc d) :
    fderiv ℝ (d1_cl φ) Y v = ∑ i, fderiv ℝ (d1_cl φ) Y (Pi.single i (v i)) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]

/-- A vector field on `Config d N` transported to a vector field on the big torus. -/
def d1_pushField (ζ : Config d N → Fin N → Euc d) : Torus (N * d) → Euc (N * d) :=
  fun x => d1_eucEquiv d N (ζ ((d1_configEquiv d N).symm x))

theorem d1_lift_pushField (ζ : Config d N → Fin N → Euc d) :
    Torus.lift (d1_pushField ζ) =
      d1_eucEquiv d N ∘ (fun Y => ζ fun i => Torus.mk (Y i)) ∘ (d1_eucEquiv d N).symm := by
  funext y
  simp [Torus.lift, d1_pushField, d1_configEquiv_symm_mk]

/-- Divergence transfer: `Div` of the transported field at `e X` is `configDiv`. -/
theorem d1_div_pushField (ζ : Config d N → Fin N → Euc d)
    (hζ : Differentiable ℝ fun Y : Fin N → Euc d => ζ fun i => Torus.mk (Y i))
    (X : Config d N) :
    Torus.div (d1_pushField ζ) (d1_configEquiv d N X) = configDiv ζ X := by
  set G : (Fin N → Euc d) → (Fin N → Euc d) := fun Y => ζ fun i => Torus.mk (Y i) with hG
  have hfd : ∀ y w : Euc (N * d), fderiv ℝ (Torus.lift (d1_pushField ζ)) y w =
      d1_eucEquiv d N (fderiv ℝ G ((d1_eucEquiv d N).symm y) ((d1_eucEquiv d N).symm w)) := by
    intro y w
    rw [d1_lift_pushField, ← Function.comp_assoc, ContinuousLinearEquiv.comp_right_fderiv,
      ContinuousLinearEquiv.comp_fderiv]
    simp [hG]
  have hrep : (d1_eucEquiv d N).symm (Torus.rep (d1_configEquiv d N X)) = fun i => Torus.rep (X i) := by
    rw [← d1_eucEquiv_rep]; simp
  unfold Torus.div configDiv
  simp only [hfd, hrep]
  rw [← (d1_idx d N).sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hb : (d1_eucEquiv d N).symm (EuclideanSpace.single (d1_idx d N k) 1) = configBasis d N k := by
    rw [← d1_eucEquiv_configBasis]; simp
  rw [hb]
  have hcomp : fderiv ℝ (fun Z : Fin N → Euc d => (ζ (fun i => Torus.mk (Z i)) k.1).ofLp k.2)
      (fun i => Torus.rep (X i)) (configBasis d N k) =
      ((fderiv ℝ G (fun i => Torus.rep (X i)) (configBasis d N k)) k.1).ofLp k.2 := by
    let Λ : (Fin N → Euc d) →L[ℝ] ℝ :=
      (EuclideanSpace.proj k.2 : Euc d →L[ℝ] ℝ).comp (ContinuousLinearMap.proj k.1)
    have : (fun Z : Fin N → Euc d => (ζ (fun i => Torus.mk (Z i)) k.1).ofLp k.2) = Λ ∘ G := rfl
    rw [this, fderiv_comp _ Λ.differentiableAt (hζ _), Λ.fderiv]
    rfl
  rw [hcomp]
  simp [d1_eucEquiv_apply]

end HRS
