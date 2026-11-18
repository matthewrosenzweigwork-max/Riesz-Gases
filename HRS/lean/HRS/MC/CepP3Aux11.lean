import HRS.MC.CepP3Aux10

/-!
# Packet P3, Aux11: the linear isomorphism `ℝ^{N d} ≃ (Fin N → Euc d)` and the second derivative of
a composition with a continuous linear map
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP3

open HRS

variable {d N : ℕ}

/-- The linear identification of `ℝ^{N d}` with `Fin N → Euc d`. -/
def Jlin (d N : ℕ) : EuclideanSpace ℝ (Fin (N * d)) ≃ₗ[ℝ] (Fin N → Euc d) where
  toFun z := fun i => WithLp.toLp 2 (fun j => z (finProdFinEquiv (i, j)))
  invFun Y := WithLp.toLp 2 (fun m => Y (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2)
  map_add' z z' := by
    funext i; ext j; simp
  map_smul' c z := by
    funext i; ext j; simp
  left_inv z := by
    ext m
    simp only [Prod.mk.eta, Equiv.apply_symm_apply]
  right_inv Y := by
    funext i; ext j; simp only [Equiv.symm_apply_apply]

/-- The continuous linear equivalence `ℝ^{N d} ≃L (Fin N → Euc d)`. -/
def Jc (d N : ℕ) : EuclideanSpace ℝ (Fin (N * d)) ≃L[ℝ] (Fin N → Euc d) :=
  (Jlin d N).toContinuousLinearEquiv

theorem Jc_apply (z : EuclideanSpace ℝ (Fin (N * d))) (i : Fin N) (j : Fin d) :
    Jc d N z i j = z (finProdFinEquiv (i, j)) := rfl

theorem Jc_single (m : Fin (N * d)) :
    Jc d N (EuclideanSpace.single m 1) = configBasis d N (finProdFinEquiv.symm m) := by
  have key : ∀ (i : Fin N) (j : Fin d), finProdFinEquiv (i, j) = m ↔
      (i = (finProdFinEquiv.symm m).1 ∧ j = (finProdFinEquiv.symm m).2) := by
    intro i j
    rw [Equiv.apply_eq_iff_eq_symm_apply, Prod.ext_iff]
  funext i
  ext j
  rw [Jc_apply]
  simp only [configBasis, EuclideanSpace.single_apply, Pi.single_apply]
  by_cases h : i = (finProdFinEquiv.symm m).1
  · by_cases h2 : j = (finProdFinEquiv.symm m).2
    · rw [if_pos ((key i j).2 ⟨h, h2⟩), if_pos h, EuclideanSpace.single_apply, if_pos h2]
    · rw [if_neg (fun hh => h2 ((key i j).1 hh).2), if_pos h, EuclideanSpace.single_apply, if_neg h2]
  · rw [if_neg (fun hh => h ((key i j).1 hh).1), if_neg h]
    rfl

/-- Second derivative of a composition with a continuous linear map. -/
theorem fderiv2_comp_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E →L[ℝ] F) {G : F → ℝ} (hG : ContDiff ℝ 2 G)
    (x v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => G (A y))) x v w = fderiv ℝ (fderiv ℝ G) (A x) (A v) (A w) := by
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hD : Differentiable ℝ (fderiv ℝ G) :=
    (hG.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have e1 : fderiv ℝ (fun y => G (A y)) = fun y =>
      (ContinuousLinearMap.compL ℝ E F ℝ).flip A (fderiv ℝ G (A y)) := by
    funext y
    exact ((hGd (A y)).hasFDerivAt.comp y A.hasFDerivAt).fderiv
  have h3 : HasFDerivAt (fun y => fderiv ℝ G (A y)) ((fderiv ℝ (fderiv ℝ G) (A x)).comp A) x :=
    (hD (A x)).hasFDerivAt.comp x A.hasFDerivAt
  have h4 := ((ContinuousLinearMap.compL ℝ E F ℝ).flip A).hasFDerivAt.comp x h3
  rw [e1]
  exact congrArg (fun L => L v w) h4.fderiv

end HRS.MC.CepP3
