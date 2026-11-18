import HRS.Equilibrium.Parametrix.PXFIDAuxA
import HRS.PDE.MeanFieldAux
import HRS.PDE.Fourier

/-!
# Packet PX-FID, file B: calculus of lifts and the vanishing divergence of cut-off fields
-/

open MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace HRS.Parx.PXFID

variable {d : ℕ}

/-! ### Periodicity of derivatives of lifts (no regularity needed) -/

theorem exists_lattice_of_mk_eq' {x y : Euc d} (h : Torus.mk x = Torus.mk y) :
    ∃ n : Lattice d, x = y + Lattice.toEuc n := by
  have : ∀ i, ∃ m : ℤ, x i = y i + m := by
    intro i
    have h1 : ((x i : ℝ) : UnitAddCircle) = ((y i : ℝ) : UnitAddCircle) := congrFun h i
    have h2 := (QuotientAddGroup.eq (a := x i) (b := y i)).1 h1
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.1 h2
    refine ⟨-m, ?_⟩
    simp at hm
    push_cast
    linarith
  choose n hn using this
  refine ⟨n, ?_⟩
  ext i
  simp [Lattice.toEuc, hn i]

theorem fderiv_lift_periodic (u : Torus d → ℝ) (p : Euc d) (n : Lattice d) :
    fderiv ℝ (Torus.lift u) (p + Lattice.toEuc n) = fderiv ℝ (Torus.lift u) p := by
  rw [← fderiv_comp_add_right]
  congr 1
  funext z
  exact Torus.lift_periodic u z n

theorem fderiv_lift_rep_mk (u : Torus d → ℝ) (p : Euc d) :
    fderiv ℝ (Torus.lift u) (Torus.rep (Torus.mk p)) = fderiv ℝ (Torus.lift u) p := by
  obtain ⟨n, hn⟩ := exists_lattice_of_mk_eq' (Torus.mk_rep (Torus.mk p))
  rw [hn, fderiv_lift_periodic]

theorem iteratedFDeriv_lift_rep_mk (u : Torus d → ℝ) (j : ℕ) (p : Euc d) :
    iteratedFDeriv ℝ j (Torus.lift u) (Torus.rep (Torus.mk p)) = iteratedFDeriv ℝ j (Torus.lift u) p := by
  obtain ⟨n, hn⟩ := exists_lattice_of_mk_eq' (Torus.mk_rep (Torus.mk p))
  rw [hn, Torus.iteratedFDeriv_lift_periodic]

theorem partialDeriv_eq_fderiv_lift (j : Fin d) (u : Torus d → ℝ) (p : Euc d) :
    Torus.partialDeriv j u (Torus.mk p) =
      fderiv ℝ (Torus.lift u) p (EuclideanSpace.single j 1) := by
  unfold Torus.partialDeriv
  rw [fderiv_lift_rep_mk]

theorem laplacian_eq_sum_fderiv (u : Torus d → ℝ) (x : Torus d) :
    Torus.laplacian u x = ∑ j : Fin d, fderiv ℝ (fderiv ℝ (Torus.lift u)) (Torus.rep x)
      (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) := by
  unfold Torus.laplacian
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (Torus.lift u)
    (EuclideanSpace.basisFun (Fin d) ℝ)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp [EuclideanSpace.basisFun_apply]

theorem isOpen_ne_pt (ã : Euc d) : IsOpen {p : Euc d | Torus.mk p ≠ Torus.mk ã} :=
  isOpen_ne_fun Torus.continuous_mk continuous_const

/-! ### The cut-off field is `C¹` and has vanishing integrated divergence -/

/-- `W_j = θ_ε ϕ ρ ∂_j u`. -/
def Wfield (ε : ℝ) (ã : Euc d) (ϕ ρ u : Torus d → ℝ) (j : Fin d) (x : Torus d) : ℝ :=
  theta ε ã x * ϕ x * ρ x * Torus.partialDeriv j u x

theorem lift_Wfield (ε : ℝ) (ã : Euc d) (ϕ ρ u : Torus d → ℝ) (j : Fin d) :
    Torus.lift (Wfield ε ã ϕ ρ u j) = fun p => Torus.lift (theta ε ã) p * Torus.lift ϕ p *
      Torus.lift ρ p * fderiv ℝ (Torus.lift u) p (EuclideanSpace.single j 1) := by
  funext p
  simp only [Torus.lift, Function.comp, Wfield]
  rw [partialDeriv_eq_fderiv_lift]
  rfl

theorem Wfield_isCk {ε : ℝ} (hε : 0 < ε) (ã : Euc d) {ϕ ρ u : Torus d → ℝ}
    (hϕ : Torus.IsSmooth ϕ) (hρ : Torus.IsSmooth ρ)
    (hsm : ContDiffOn ℝ 2 (Torus.lift u) {p : Euc d | Torus.mk p ≠ Torus.mk ã}) (j : Fin d) :
    Torus.IsCk 1 (Wfield ε ã ϕ ρ u j) := by
  unfold Torus.IsCk
  rw [lift_Wfield]
  have hθ : ContDiff ℝ 1 (Torus.lift (theta ε ã)) :=
    (show ContDiff ℝ ∞ (Torus.lift (theta ε ã)) from theta_isSmooth ε ã).of_le (by exact_mod_cast le_top)
  have hϕ' : ContDiff ℝ 1 (Torus.lift ϕ) :=
    (show ContDiff ℝ ∞ (Torus.lift ϕ) from hϕ).of_le (by exact_mod_cast le_top)
  have hρ' : ContDiff ℝ 1 (Torus.lift ρ) :=
    (show ContDiff ℝ ∞ (Torus.lift ρ) from hρ).of_le (by exact_mod_cast le_top)
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : Torus.mk p = Torus.mk ã
  · have hnhds : {q : Euc d | Torus.eucDist (Torus.mk q) (Torus.mk ã) < ε / 6} ∈ 𝓝 p := by
      refine (isOpen_lt (continuous_eucDist_mk ã) continuous_const).mem_nhds ?_
      show Torus.eucDist (Torus.mk p) (Torus.mk ã) < ε / 6
      rw [hp]
      have : Torus.eucDist (Torus.mk ã) (Torus.mk ã) = 0 := PairCorrAux.eucDist_self' _
      rw [this]; positivity
    have h0 : ContDiffAt ℝ 1 (fun _ : Euc d => (0 : ℝ)) p := contDiffAt_const
    refine h0.congr_of_eventuallyEq ?_
    filter_upwards [hnhds] with q hq
    have := theta_eq_zero hε ã q hq
    have h2 : Torus.lift (theta ε ã) q = 0 := this
    simp [h2]
  · have hU : ContDiffAt ℝ 2 (Torus.lift u) p := hsm.contDiffAt ((isOpen_ne_pt ã).mem_nhds hp)
    have hF : ContDiffAt ℝ 1 (fderiv ℝ (Torus.lift u)) p := hU.fderiv_right (by norm_num)
    exact (((hθ.contDiffAt.mul hϕ'.contDiffAt).mul hρ'.contDiffAt).mul
      (hF.clm_apply contDiffAt_const))

theorem integral_div_cutoff_eq_zero {ε : ℝ} (hε : 0 < ε) (ã : Euc d) {ϕ ρ u : Torus d → ℝ}
    (hϕ : Torus.IsSmooth ϕ) (hρ : Torus.IsSmooth ρ)
    (hsm : ContDiffOn ℝ 2 (Torus.lift u) {p : Euc d | Torus.mk p ≠ Torus.mk ã}) :
    ∫ x : Torus d, ∑ j : Fin d, Torus.partialDeriv j (Wfield ε ã ϕ ρ u j) x = 0 := by
  rw [integral_finsetSum]
  · exact Finset.sum_eq_zero fun j _ => PDE.MFAux.integral_partialDeriv_eq_zero j _
      (Wfield_isCk hε ã hϕ hρ hsm j)
  · intro j _
    exact (PDE.continuous_partialDeriv j _ (Wfield_isCk hε ã hϕ hρ hsm j)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- The divergence of the cut-off field, away from the singular point. -/
theorem partialDeriv_Wfield {ε : ℝ} (ã : Euc d) {ϕ ρ u : Torus d → ℝ}
    (hθ : Torus.IsSmooth (theta ε ã)) (hϕ : Torus.IsSmooth ϕ) (hρ : Torus.IsSmooth ρ)
    (hsm : ContDiffOn ℝ 2 (Torus.lift u) {p : Euc d | Torus.mk p ≠ Torus.mk ã})
    (x : Torus d) (hx : x ≠ Torus.mk ã) (j : Fin d) :
    Torus.partialDeriv j (Wfield ε ã ϕ ρ u j) x =
      theta ε ã x * ϕ x * ρ x * fderiv ℝ (fderiv ℝ (Torus.lift u)) (Torus.rep x)
        (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) +
      (Torus.partialDeriv j (theta ε ã) x * ϕ x * ρ x + theta ε ã x * Torus.partialDeriv j ϕ x * ρ x +
        theta ε ã x * ϕ x * Torus.partialDeriv j ρ x) * Torus.partialDeriv j u x := by
  set p := Torus.rep x with hpdef
  have hmk : Torus.mk p = x := Torus.mk_rep x
  have hp : Torus.mk p ≠ Torus.mk ã := by rw [hmk]; exact hx
  have hθ' : DifferentiableAt ℝ (Torus.lift (theta ε ã)) p :=
    (show ContDiff ℝ ∞ (Torus.lift (theta ε ã)) from hθ).differentiable (by simp) p
  have hϕ' : DifferentiableAt ℝ (Torus.lift ϕ) p :=
    (show ContDiff ℝ ∞ (Torus.lift ϕ) from hϕ).differentiable (by simp) p
  have hρ' : DifferentiableAt ℝ (Torus.lift ρ) p :=
    (show ContDiff ℝ ∞ (Torus.lift ρ) from hρ).differentiable (by simp) p
  have hU : ContDiffAt ℝ 2 (Torus.lift u) p := hsm.contDiffAt ((isOpen_ne_pt ã).mem_nhds hp)
  have hF : ContDiffAt ℝ 1 (fderiv ℝ (Torus.lift u)) p := hU.fderiv_right (by norm_num)
  have hFd : DifferentiableAt ℝ (fderiv ℝ (Torus.lift u)) p := hF.differentiableAt (by simp)
  have hD : HasFDerivAt (fun q => fderiv ℝ (Torus.lift u) q (EuclideanSpace.single j 1))
      ((fderiv ℝ (fderiv ℝ (Torus.lift u)) p).flip (EuclideanSpace.single j 1)) p := by
    have := (hFd.hasFDerivAt).clm_apply (hasFDerivAt_const (EuclideanSpace.single j (1 : ℝ)) p)
    simpa using this
  have h1 := ((hθ'.hasFDerivAt.fun_mul hϕ'.hasFDerivAt).fun_mul hρ'.hasFDerivAt).fun_mul hD
  unfold Torus.partialDeriv
  rw [lift_Wfield, ← hpdef]
  rw [h1.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.flip_apply]
  have e : ∀ f : Torus d → ℝ, Torus.lift f p = f x := fun f => by
    simp only [Torus.lift, Function.comp]; rw [hmk]
  simp only [e]
  have e2 : fderiv ℝ (Torus.lift u) p (EuclideanSpace.single j 1) =
      fderiv ℝ (Torus.lift u) (Torus.rep x) (EuclideanSpace.single j 1) := rfl
  ring

/-! ### Measurability and the pointwise divergence identity -/

theorem measurable_rep' (d : ℕ) : Measurable (Torus.rep : Torus d → Euc d) := by
  have h : Measurable (fun (x : Torus d) (i : Fin d) =>
      ((AddCircle.equivIco (1 : ℝ) 0 (x i) : Set.Ico (0 : ℝ) (0 + 1)) : ℝ)) :=
    measurable_pi_iff.2 fun i => measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp (measurable_pi_apply i))
  exact (WithLp.measurable_toLp 2 _).comp h

theorem measurable_grad (u : Torus d → ℝ) : Measurable (Torus.grad u) := by
  unfold Torus.grad
  have h : Measurable (gradient (Torus.lift u)) := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp
      (measurable_fderiv ℝ _)
  exact h.comp (measurable_rep' d)

theorem measurable_laplacian (u : Torus d → ℝ) : Measurable (Torus.laplacian u) := by
  have : Torus.laplacian u = fun x => ∑ j : Fin d, fderiv ℝ (fderiv ℝ (Torus.lift u)) (Torus.rep x)
      (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) := funext (laplacian_eq_sum_fderiv u)
  rw [this]
  refine Finset.measurable_sum _ fun j _ => ?_
  have h1 : Measurable (fun p : Euc d => fderiv ℝ (fderiv ℝ (Torus.lift u)) p
      (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)) :=
    (measurable_fderiv_apply_const ℝ (fderiv ℝ (Torus.lift u))
      (EuclideanSpace.single j 1)).apply_continuousLinearMap (EuclideanSpace.single j 1)
  exact h1.comp (measurable_rep' d)

theorem measurable_Bop {s β : ℝ} (V ρ u : Torus d → ℝ) : Measurable (Bop d s V β ρ u) := by
  unfold Bop forceField
  exact (measurable_const.mul (measurable_laplacian u)).sub
    (((measurable_grad V).add (measurable_grad _)).inner (measurable_grad u))

theorem inner_grad_eq_sum (f g : Torus d → ℝ) (x : Torus d) :
    inner ℝ (Torus.grad f x) (Torus.grad g x) =
      ∑ j : Fin d, Torus.partialDeriv j f x * Torus.partialDeriv j g x := by
  simp only [PiLp.inner_apply, PDE.MFAux.grad_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem div_cutoff_pointwise {s β : ℝ} {V ρ : Torus d → ℝ} (hβ : β ≠ 0)
    (hforce : ∀ x, ρ x • (Torus.grad V x + forceField d s ρ x) = -β⁻¹ • Torus.grad ρ x)
    {ε : ℝ} (ã : Euc d) {ϕ u : Torus d → ℝ}
    (hθ : Torus.IsSmooth (theta ε ã)) (hϕ : Torus.IsSmooth ϕ) (hρ : Torus.IsSmooth ρ)
    (hsm : ContDiffOn ℝ 2 (Torus.lift u) {p : Euc d | Torus.mk p ≠ Torus.mk ã})
    (x : Torus d) (hx : x ≠ Torus.mk ã) :
    ∑ j : Fin d, Torus.partialDeriv j (Wfield ε ã ϕ ρ u j) x =
      β * ρ x * (theta ε ã x * ϕ x * Bop d s V β ρ u x) +
      ρ x * (theta ε ã x * inner ℝ (Torus.grad ϕ x) (Torus.grad u x)) +
      ρ x * (ϕ x * inner ℝ (Torus.grad (theta ε ã) x) (Torus.grad u x)) := by
  simp_rw [partialDeriv_Wfield ã hθ hϕ hρ hsm x hx]
  rw [Finset.sum_add_distrib]
  have h1 : ∑ j : Fin d, theta ε ã x * ϕ x * ρ x * fderiv ℝ (fderiv ℝ (Torus.lift u)) (Torus.rep x)
      (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) =
      theta ε ã x * ϕ x * ρ x * Torus.laplacian u x := by
    rw [laplacian_eq_sum_fderiv, Finset.mul_sum]
  have h2 : ∑ j : Fin d, (Torus.partialDeriv j (theta ε ã) x * ϕ x * ρ x +
      theta ε ã x * Torus.partialDeriv j ϕ x * ρ x + theta ε ã x * ϕ x * Torus.partialDeriv j ρ x) *
        Torus.partialDeriv j u x =
      ϕ x * ρ x * inner ℝ (Torus.grad (theta ε ã) x) (Torus.grad u x) +
      theta ε ã x * ρ x * inner ℝ (Torus.grad ϕ x) (Torus.grad u x) +
      theta ε ã x * ϕ x * inner ℝ (Torus.grad ρ x) (Torus.grad u x) := by
    simp only [inner_grad_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h3 : inner ℝ (Torus.grad ρ x) (Torus.grad u x) =
      -β * ρ x * inner ℝ (Torus.grad V x + forceField d s ρ x) (Torus.grad u x) := by
    have := hforce x
    have h4 : Torus.grad ρ x = (-β * ρ x) • (Torus.grad V x + forceField d s ρ x) := by
      calc Torus.grad ρ x = (-β * -β⁻¹) • Torus.grad ρ x := by
            rw [neg_mul_neg, mul_inv_cancel₀ hβ, one_smul]
        _ = (-β) • (-β⁻¹ • Torus.grad ρ x) := by rw [smul_smul]
        _ = (-β) • (ρ x • (Torus.grad V x + forceField d s ρ x)) := by rw [this]
        _ = (-β * ρ x) • (Torus.grad V x + forceField d s ρ x) := by rw [smul_smul]
    rw [h4, inner_smul_left]
    simp
  rw [h1, h2, h3]
  unfold Bop
  field_simp
  ring

end HRS.Parx.PXFID

end
