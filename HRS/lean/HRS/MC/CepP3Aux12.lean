import HRS.MC.CepP3Aux11

/-!
# Packet P3, Aux12: the operator of P2 transported to the covering coordinates
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP3

open HRS

variable {d N : ℕ}

/-- `(t, z) ↦ (t, J z)`. -/
def Acl (d N : ℕ) : (ℝ × EuclideanSpace ℝ (Fin (N * d))) ≃L[ℝ] (ℝ × (Fin N → Euc d)) :=
  ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ) (Jc d N)

theorem Acl_apply (p : ℝ × EuclideanSpace ℝ (Fin (N * d))) : Acl d N p = (p.1, Jc d N p.2) := rfl

/-- The operator of P2 (verbatim shape of the `heq` integrand of `cep_P2_parabolic_weyl`). -/
def Lp2 (invβ : ℝ) (b : ℝ × EuclideanSpace ℝ (Fin (N * d)) → EuclideanSpace ℝ (Fin (N * d)))
    (Φ : ℝ × EuclideanSpace ℝ (Fin (N * d)) → ℝ) (p : ℝ × EuclideanSpace ℝ (Fin (N * d))) : ℝ :=
  fderiv ℝ Φ p (1, 0)
    + invβ * ∑ k : Fin (N * d), fderiv ℝ (fderiv ℝ Φ) p (0, EuclideanSpace.single k 1)
        (0, EuclideanSpace.single k 1)
    + fderiv ℝ Φ p (0, b p)

theorem Lp2_comp (invβ : ℝ) (b : ℝ × (Fin N → Euc d) → Fin N → Euc d)
    {F : ℝ × (Fin N → Euc d) → ℝ} (hF : ContDiff ℝ 2 F) (p : ℝ × EuclideanSpace ℝ (Fin (N * d))) :
    Lp2 invβ (fun q => (Jc d N).symm (b (Acl d N q))) (fun q => F (Acl d N q)) p
      = Lop invβ b F (Acl d N p) := by
  have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have h1 : ∀ v, fderiv ℝ (fun q => F (Acl d N q)) p v = fderiv ℝ F (Acl d N p) (Acl d N v) := by
    intro v
    have := ((hFd (Acl d N p)).hasFDerivAt.comp p (Acl d N).hasFDerivAt).fderiv
    exact congrArg (fun L => L v) this
  unfold Lp2 Lop
  rw [h1, h1]
  have e1 : Acl d N (1, 0) = (1, 0) := by simp [Acl_apply]
  have e3 : Acl d N (0, (Jc d N).symm (b (Acl d N p))) = (0, b (Acl d N p)) := by
    simp [Acl_apply]
  have e2 : ∀ k : Fin (N * d), fderiv ℝ (fderiv ℝ (fun q => F (Acl d N q))) p
        (0, EuclideanSpace.single k 1) (0, EuclideanSpace.single k 1)
      = fderiv ℝ (fderiv ℝ F) (Acl d N p) (0, configBasis d N (finProdFinEquiv.symm k))
        (0, configBasis d N (finProdFinEquiv.symm k)) := by
    intro k
    have h := fderiv2_comp_clm
      (Acl d N : (ℝ × EuclideanSpace ℝ (Fin (N * d))) →L[ℝ] (ℝ × (Fin N → Euc d))) hF p
      (0, EuclideanSpace.single k 1) (0, EuclideanSpace.single k 1)
    have this : Acl d N (0, EuclideanSpace.single k (1 : ℝ)) = (0, configBasis d N (finProdFinEquiv.symm k)) := by
      rw [Acl_apply]
      simp only
      rw [Jc_single]
    refine h.trans ?_
    show fderiv ℝ (fderiv ℝ F) (Acl d N p) (Acl d N (0, EuclideanSpace.single k 1))
      (Acl d N (0, EuclideanSpace.single k 1)) = _
    rw [this]
  rw [e1, e3]
  simp only [e2]
  rw [Equiv.sum_comp (finProdFinEquiv.symm : Fin (N * d) ≃ Fin N × Fin d)
    (fun k => fderiv ℝ (fderiv ℝ F) (Acl d N p) (0, configBasis d N k) (0, configBasis d N k))]

end HRS.MC.CepP3
