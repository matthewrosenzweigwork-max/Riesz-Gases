import HRS.MS.R26T8AP17a
import HRS.MS.R26T8AP06b

/-!
# S8.2 local Newton layer, packet T8A.P17 (part b): nested jets of an affine pull-back
`r26t8a_p17_nest_clm_bound`: `‖nest p q (L ∘ Φ)‖ <= c ‖nest p q Φ‖` for a `c`-Lipschitz linear `L`.
`r26t8a_p17_nest_affine`: `‖nest p q (Y,w |-> φ(Y + a w)) X z‖ <= |a|^q ‖D^(p+q) φ (X + a z)‖`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82

namespace HRS.MS.R26T8A

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem r26t8a_p17_nest_clm_bound {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] (L : V →L[ℝ] W) {c : ℝ} (hc : 0 ≤ c) (hL : ∀ v, ‖L v‖ ≤ c * ‖v‖) (p q : ℕ)
    (Φ : E × E → V) (X z : E) (hΦ : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) Φ) :
    ‖r26t8a_nest p q (fun Yw => L (Φ Yw)) X z‖ ≤ c * ‖r26t8a_nest p q Φ X z‖ := by
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
  have hLm1 : ‖Lm‖ ≤ c := by
    refine ContinuousLinearMap.opNorm_le_bound _ hc (fun m => ?_)
    refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) (fun x => ?_)
    show ‖L (m x)‖ ≤ _
    calc ‖L (m x)‖ ≤ c * ‖m x‖ := hL _
      _ ≤ c * (‖m‖ * ∏ i, ‖x i‖) := mul_le_mul_of_nonneg_left (m.le_opNorm x) hc
      _ = _ := by ring
  refine (Lm.norm_iteratedFDeriv_comp_left hM.contDiffAt le_rfl).trans ?_
  calc ‖Lm‖ * ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (fun w => Φ (Y, w)) z) X‖
      ≤ c * ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (fun w => Φ (Y, w)) z) X‖ :=
        mul_le_mul_of_nonneg_right hLm1 (norm_nonneg _)

theorem r26t8a_p17_nest_affine (a : ℝ) : ∀ (q p : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (φ : E → V) (X z : E), ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) φ →
    ‖r26t8a_nest p q (fun Yw : E × E => φ (Yw.1 + a • Yw.2)) X z‖ ≤ |a| ^ q * ‖iteratedFDeriv ℝ (p + q) φ (X + a • z)‖ := by
  intro q
  induction q with
  | zero =>
    intro p V _ _ φ X z hφ
    rw [r26t8a_nest_zero]
    have : iteratedFDeriv ℝ p (fun Y : E => φ (Y + a • z)) X = iteratedFDeriv ℝ p φ (X + a • z) :=
      iteratedFDeriv_comp_add_right (𝕜 := ℝ) p (a • z) X
    simp only [this, pow_zero, one_mul, Nat.add_zero]
    exact le_rfl
  | succ q ih =>
    intro p V _ _ φ X z hφ
    have hd : Differentiable ℝ φ := hφ.differentiable (by exact_mod_cast (by omega : p + (q + 1) ≠ 0))
    rw [r26t8a_nest_succ]
    have hdw : r26t8a_dw (fun Yw : E × E => φ (Yw.1 + a • Yw.2)) =
        fun Yw : E × E => (a • ContinuousLinearMap.id ℝ (E →L[ℝ] V)) (fderiv ℝ φ (Yw.1 + a • Yw.2)) := by
      funext Yw
      unfold r26t8a_dw
      have hh : HasFDerivAt (fun w : E => Yw.1 + a • w) (a • ContinuousLinearMap.id ℝ E) Yw.2 :=
        ((hasFDerivAt_id Yw.2).const_smul a).const_add Yw.1
      have h2 := ((hd (Yw.1 + a • Yw.2)).hasFDerivAt.comp Yw.2 hh).fderiv
      rw [show (fun w : E => φ (Yw.1 + a • w)) = φ ∘ (fun w : E => Yw.1 + a • w) from rfl, h2]
      ext v
      simp [mul_comm]
    rw [hdw]
    have hφ' : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fderiv ℝ φ) := hφ.fderiv_right (by
      push_cast; exact le_of_eq (by norm_cast))
    have h1 := r26t8a_p17_nest_clm_bound (E := E) (a • ContinuousLinearMap.id ℝ (E →L[ℝ] V)) (abs_nonneg a)
      (fun v => by simp [norm_smul]) p q (fun Yw : E × E => fderiv ℝ φ (Yw.1 + a • Yw.2)) X z
      (by
        have hl : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun Yw : E × E => Yw.1 + a • Yw.2) :=
          contDiff_fst.add (contDiff_snd.const_smul a)
        exact hφ'.comp hl)
    refine h1.trans ?_
    have h2 := ih p (fderiv ℝ φ) X z hφ'
    have h3 : ‖iteratedFDeriv ℝ (p + q) (fderiv ℝ φ) (X + a • z)‖ = ‖iteratedFDeriv ℝ (p + q + 1) φ (X + a • z)‖ :=
      norm_iteratedFDeriv_fderiv
    rw [h3] at h2
    calc |a| * ‖r26t8a_nest p q (fun Yw : E × E => fderiv ℝ φ (Yw.1 + a • Yw.2)) X z‖
        ≤ |a| * (|a| ^ q * ‖iteratedFDeriv ℝ (p + q + 1) φ (X + a • z)‖) :=
          mul_le_mul_of_nonneg_left h2 (abs_nonneg a)
      _ = |a| ^ (q + 1) * ‖iteratedFDeriv ℝ (p + (q + 1)) φ (X + a • z)‖ := by
          rw [show p + (q + 1) = p + q + 1 by ring, pow_succ]; ring

end HRS.MS.R26T8A
