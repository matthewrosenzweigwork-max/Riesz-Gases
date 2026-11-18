/-
# HRS.Equilibrium.Q84dAuxA — packet Q84d helpers (measurability of derivatives off the diagonal)

Measurable surrogates for the gradient and Laplacian of a kernel `ψ` that is smooth off the
diagonal (`PsiSize.smooth`): the `m`-th component `gK ψ m x y` of `∇_xψ(x,y)` and `hK ψ m x y` of
`∂²_{x_m}ψ(x,y)` computed from `fderiv` of `lift2 ψ`.  They are jointly measurable
everywhere (`measurable_fderiv`) and agree with the actual derivatives off the diagonal.
-/
import HRS.Equilibrium.Q84aAuxA
import HRS.Equilibrium.LocalDivTorus
import HRS.Energy.Coercivity

open MeasureTheory Filter Topology

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {s : ℝ}

theorem q84d_measurable_rep (d : ℕ) : Measurable (Torus.rep : Torus d → Euc d) := by
  have h : Measurable (fun (x : Torus d) (i : Fin d) =>
      ((AddCircle.equivIco (1 : ℝ) 0 (x i) : Set.Ico (0 : ℝ) (0 + 1)) : ℝ)) :=
    measurable_pi_iff.2 fun i => measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp (measurable_pi_apply i))
  exact (WithLp.measurable_toLp 2 _).comp h

theorem q84d_measurable_grad (u : Torus d → ℝ) : Measurable (Torus.grad u) := by
  unfold Torus.grad gradient
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp
    ((measurable_fderiv ℝ (Torus.lift u)).comp (q84d_measurable_rep d))

/-- The diagonal of `𝕋^d × 𝕋^d` is null. -/
theorem q84d_ae_ne_diag (hd : 1 ≤ d) :
    ∀ᵐ p ∂(volume : Measure (Torus d × Torus d)), p.1 ≠ p.2 := by
  have hm : MeasurableSet {p : Torus d × Torus d | p.1 = p.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  rw [ae_iff]
  have : {p : Torus d × Torus d | ¬p.1 ≠ p.2} = {p : Torus d × Torus d | p.1 = p.2} := by
    ext p; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_apply hm]
  have h0 : ∀ x : Torus d, (volume : Measure (Torus d)) (Prod.mk x ⁻¹' {p : Torus d × Torus d | p.1 = p.2}) = 0 := by
    intro x
    have : Prod.mk x ⁻¹' {p : Torus d × Torus d | p.1 = p.2} = {x} := by
      ext y; simp [eq_comm]
    rw [this]
    exact volume_singleton_torus hd x
  simp_rw [h0]
  simp

/-- `∂_{x_m} ψ(x,y)` computed from the Fréchet derivative of the periodic lift of `ψ`. -/
def gK (ψ : Torus d → Torus d → ℝ) (m : Fin d) (x y : Torus d) : ℝ :=
  fderiv ℝ (lift2 ψ) (Torus.rep x, Torus.rep y) (EuclideanSpace.single m 1, 0)

/-- `∂²_{x_m} ψ(x,y)` computed from the second Fréchet derivative of the periodic lift. -/
def hK (ψ : Torus d → Torus d → ℝ) (m : Fin d) (x y : Torus d) : ℝ :=
  fderiv ℝ (fun p => fderiv ℝ (lift2 ψ) p (EuclideanSpace.single m 1, 0))
    (Torus.rep x, Torus.rep y) (EuclideanSpace.single m 1, 0)

theorem q84d_measurable_gK (ψ : Torus d → Torus d → ℝ) (m : Fin d) :
    Measurable (fun p : Torus d × Torus d => gK ψ m p.1 p.2) := by
  have h1 : Measurable fun p : Euc d × Euc d => fderiv ℝ (lift2 ψ) p (EuclideanSpace.single m 1, 0) :=
    measurable_fderiv_apply_const ℝ (lift2 ψ) _
  have h2 : Measurable fun p : Torus d × Torus d => (Torus.rep p.1, Torus.rep p.2) :=
    ((q84d_measurable_rep d).comp measurable_fst).prodMk ((q84d_measurable_rep d).comp measurable_snd)
  exact h1.comp h2

theorem q84d_measurable_hK (ψ : Torus d → Torus d → ℝ) (m : Fin d) :
    Measurable (fun p : Torus d × Torus d => hK ψ m p.1 p.2) := by
  have h1 : Measurable fun p : Euc d × Euc d =>
      fderiv ℝ (fun p => fderiv ℝ (lift2 ψ) p (EuclideanSpace.single m 1, 0)) p
        (EuclideanSpace.single m 1, 0) :=
    measurable_fderiv_apply_const ℝ _ _
  have h2 : Measurable fun p : Torus d × Torus d => (Torus.rep p.1, Torus.rep p.2) :=
    ((q84d_measurable_rep d).comp measurable_fst).prodMk ((q84d_measurable_rep d).comp measurable_snd)
  exact h1.comp h2

theorem q84d_mem_offDiag {x y : Torus d} (hxy : x ≠ y) : (Torus.rep x, Torus.rep y) ∈ offDiag d := by
  show Torus.mk (Torus.rep x) ≠ Torus.mk (Torus.rep y)
  rw [Torus.mk_rep, Torus.mk_rep]; exact hxy

theorem q84d_toDual_symm_apply (L : Euc d →L[ℝ] ℝ) (m : Fin d) :
    ((InnerProductSpace.toDual ℝ (Euc d)).symm L) m = L (EuclideanSpace.single m 1) := by
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := Euc d) (x := EuclideanSpace.single m 1) (y := L)
  rw [← h, EuclideanSpace.inner_single_right]
  simp

theorem q84d_contDiffAt_lift2 {ψ : Torus d → Torus d → ℝ}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) {p : Euc d × Euc d}
    (hp : p ∈ offDiag d) : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) p :=
  hsm.contDiffAt (Q84a.q84a_isOpen_offDiag.mem_nhds hp)

theorem q84d_grad_comp {ψ : Torus d → Torus d → ℝ}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) {x y : Torus d}
    (hxy : x ≠ y) (m : Fin d) : (Torus.grad (fun z => ψ z y) x) m = gK ψ m x y := by
  have e := Q84a.q84a_gradFst_eq hsm (q84d_mem_offDiag hxy)
  rw [Torus.mk_rep, Torus.mk_rep] at e
  have e' : Torus.grad (fun z => ψ z y) x = (InnerProductSpace.toDual ℝ (Euc d)).symm
      ((fderiv ℝ (lift2 ψ) (Torus.rep x, Torus.rep y)).comp (ContinuousLinearMap.inl ℝ (Euc d) (Euc d))) := e
  rw [e', q84d_toDual_symm_apply]
  simp [gK]

theorem q84d_lap_comp {ψ : Torus d → Torus d → ℝ}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) {x y : Torus d}
    (hxy : x ≠ y) : Torus.laplacian (fun z => ψ z y) x = ∑ m, hK ψ m x y := by
  have hp := q84d_mem_offDiag hxy
  set x0 : Euc d := Torus.rep x with hx0
  set y0 : Euc d := Torus.rep y with hy0
  have hφ : Torus.lift (fun z => ψ z y) = fun u : Euc d => lift2 ψ (u, y0) := by
    funext u; simp [Torus.lift, lift2, hy0, Torus.mk_rep]
  have hcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (x0, y0) := q84d_contDiffAt_lift2 hsm hp
  unfold Torus.laplacian
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin d) ℝ)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp only [EuclideanSpace.basisFun_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← hx0]
  set G : Euc d × Euc d → ℝ := fun p => fderiv ℝ (lift2 ψ) p (EuclideanSpace.single m 1, 0) with hG
  have hGd : DifferentiableAt ℝ G (x0, y0) := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ (lift2 ψ)) (x0, y0) :=
      hcd.fderiv_right (m := 1) (by norm_num)
    exact (h1.clm_apply contDiffAt_const).differentiableAt (by simp)
  have hφcd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift fun z => ψ z y) x0 := by
    rw [hφ]
    exact hcd.comp x0 (contDiffAt_id.prodMk contDiffAt_const)
  have hdiff1 : DifferentiableAt ℝ (fderiv ℝ (Torus.lift fun z => ψ z y)) x0 :=
    (hφcd.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hU : ∀ᶠ w in 𝓝 x0, fderiv ℝ (Torus.lift fun z => ψ z y) w (EuclideanSpace.single m 1) =
      G (w, y0) := by
    have hopen : IsOpen {w : Euc d | (w, y0) ∈ offDiag d} :=
      Q84a.q84a_isOpen_offDiag.preimage (continuous_id.prodMk continuous_const)
    filter_upwards [hopen.mem_nhds hp] with w hw
    have hd : DifferentiableAt ℝ (lift2 ψ) (w, y0) := (q84d_contDiffAt_lift2 hsm hw).differentiableAt (by simp)
    have hder := hd.hasFDerivAt.comp w (hasFDerivAt_prodMk_left (𝕜 := ℝ) w y0)
    rw [hφ]
    show (fderiv ℝ (fun u : Euc d => lift2 ψ (u, y0)) w) (EuclideanSpace.single m 1) = _
    have hfun : (fun u : Euc d => lift2 ψ (u, y0)) = lift2 ψ ∘ fun x : Euc d => (x, y0) := rfl
    rw [hfun, hder.fderiv]
    simp [hG]
  have e1 : fderiv ℝ (fderiv ℝ (Torus.lift fun z => ψ z y)) x0 (EuclideanSpace.single m 1)
      (EuclideanSpace.single m 1) =
      fderiv ℝ (fun w => fderiv ℝ (Torus.lift fun z => ψ z y) w (EuclideanSpace.single m 1)) x0
        (EuclideanSpace.single m 1) := by
    rw [fderiv_clm_apply hdiff1 (differentiableAt_const _)]
    simp
  rw [e1, Filter.EventuallyEq.fderiv_eq hU]
  have hcomp := hGd.hasFDerivAt.comp x0 (hasFDerivAt_prodMk_left (𝕜 := ℝ) x0 y0)
  have hfun : (fun w : Euc d => G (w, y0)) = G ∘ fun x : Euc d => (x, y0) := rfl
  rw [hfun, hcomp.fderiv]
  simp [hK, hG, hx0, hy0]

end HRS.Q84d

end
