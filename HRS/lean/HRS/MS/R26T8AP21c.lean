import HRS.MS.R26T8AP21b
import HRS.MS.R26T8AMix

/-!
# S8.2 local Newton layer, packet T8A.P21 (part c): nested jets of affine compositions and isometric images
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

section Gen

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem r26t8a_norm_iter_iter : ∀ (m : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (g : E → V) (p : ℕ)
    (x : E), ‖iteratedFDeriv ℝ p (iteratedFDeriv ℝ m g) x‖ = ‖iteratedFDeriv ℝ (p + m) g x‖ := by
  intro m
  induction m with
  | zero =>
    intro V _ _ g p x
    have h : iteratedFDeriv ℝ 0 g = (continuousMultilinearCurryFin0 ℝ E V).symm ∘ g := by
      funext y; rw [iteratedFDeriv_zero_eq_comp]
    rw [h]
    exact LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (continuousMultilinearCurryFin0 ℝ E V).symm g x p
  | succ m ih =>
    intro V _ _ g p x
    have h : iteratedFDeriv ℝ (m + 1) g = (continuousMultilinearCurryRightEquiv' ℝ m E V).symm ∘
        iteratedFDeriv ℝ m (fun y => fderiv ℝ g y) := by
      funext y; rw [iteratedFDeriv_succ_eq_comp_right]
    rw [h, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (continuousMultilinearCurryRightEquiv' ℝ m E V).symm
      (iteratedFDeriv ℝ m (fun y => fderiv ℝ g y)) x p, ih (fun y => fderiv ℝ g y) p x,
      norm_iteratedFDeriv_fderiv, ← add_assoc]

theorem r26t8a_nest_affine : ∀ (q p : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (g : E → V) (τ : ℝ)
    (X z : E), ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) g →
    ‖r26t8a_nest p q (fun Yw : E × E => g (Yw.1 + τ • Yw.2)) X z‖ ≤
      |τ| ^ q * ‖iteratedFDeriv ℝ (p + q) g (X + τ • z)‖ := by
  intro q
  induction q with
  | zero =>
    intro p V _ _ g τ X z hg
    rw [r26t8a_nest_zero, pow_zero, one_mul, add_zero]
    show ‖iteratedFDeriv ℝ p (fun Y => g (Y + τ • z)) X‖ ≤ _
    rw [iteratedFDeriv_comp_add_right]
  | succ q ih =>
    intro p V _ _ g τ X z hg
    rw [r26t8a_nest_succ]
    have hgd : Differentiable ℝ g := hg.differentiable (by simp)
    have hdw : r26t8a_dw (fun Yw : E × E => g (Yw.1 + τ • Yw.2)) = fun Yw : E × E => τ • fderiv ℝ g (Yw.1 + τ • Yw.2) := by
      funext Yw
      unfold r26t8a_dw
      have h1 : HasFDerivAt (fun w : E => Yw.1 + τ • w) (τ • ContinuousLinearMap.id ℝ E) Yw.2 :=
        ((hasFDerivAt_id Yw.2).const_smul τ).const_add Yw.1
      have h2 := (hgd (Yw.1 + τ • Yw.2)).hasFDerivAt.comp Yw.2 h1
      change fderiv ℝ (g ∘ fun w : E => Yw.1 + τ • w) Yw.2 = _
      rw [h2.fderiv]
      ext v
      simp
    rw [hdw]
    have hg' : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun v => τ • fderiv ℝ g v) :=
      (hg.fderiv_right (by push_cast; exact le_rfl)).const_smul τ |>.of_le le_rfl
    have key := ih p (fun v => τ • fderiv ℝ g v) τ X z hg'
    refine key.trans ?_
    have hc : ContDiffAt ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun v => fderiv ℝ g v) (X + τ • z) :=
      (hg.fderiv_right (by push_cast; exact le_rfl)).contDiffAt
    have e : iteratedFDeriv ℝ (p + q) (fun v => τ • fderiv ℝ g v) (X + τ • z) =
        τ • iteratedFDeriv ℝ (p + q) (fun v => fderiv ℝ g v) (X + τ • z) :=
      iteratedFDeriv_const_smul_apply' hc
    rw [e, norm_smul, Real.norm_eq_abs, norm_iteratedFDeriv_fderiv]
    have : p + (q + 1) = p + q + 1 := by omega
    rw [this, pow_succ]
    apply le_of_eq; ring

theorem r26t8a_nest_clm {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] (L : V →L[ℝ] W) (hL : ‖L‖ ≤ 1) (p q : ℕ) (Φ : E × E → V) (X z : E)
    (hΦ : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) Φ) :
    ‖r26t8a_nest p q (fun Yw => L (Φ Yw)) X z‖ ≤ ‖r26t8a_nest p q Φ X z‖ := by
  unfold r26t8a_nest
  have hq : ∀ Y : E, ContDiffAt ℝ (q : WithTop ℕ∞) (fun w => Φ (Y, w)) z := fun Y =>
    ((hΦ.comp (contDiff_const.prodMk contDiff_id)).of_le (by exact_mod_cast Nat.le_add_left q p)).contDiffAt
  set Lm := ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin q => E) V W L with hLm
  have h : (fun Y => iteratedFDeriv ℝ q (fun w => L (Φ (Y, w))) z) =
      Lm ∘ (fun Y => iteratedFDeriv ℝ q (fun w => Φ (Y, w)) z) := by
    funext Y
    exact ContinuousLinearMap.iteratedFDeriv_comp_left L (hq Y) le_rfl
  rw [h]
  have hM : ContDiff ℝ (p : WithTop ℕ∞) (fun Y => iteratedFDeriv ℝ q (fun w => Φ (Y, w)) z) :=
    r26t8a_nest_contDiff q p Φ z hΦ
  have hLm1 : ‖Lm‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun m => ?_)
    rw [one_mul]
    exact (ContinuousLinearMap.norm_compContinuousMultilinearMap_le L m).trans
      (mul_le_of_le_one_left (norm_nonneg _) hL)
  refine (Lm.norm_iteratedFDeriv_comp_left hM.contDiffAt le_rfl).trans ?_
  exact mul_le_of_le_one_left (norm_nonneg _) hLm1

end Gen

end HRS.MS.R26T8A
