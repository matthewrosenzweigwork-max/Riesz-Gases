import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Data.Nat.Choose.Sum

/-!
# S8.2 local Newton layer: nested (mixed) jets and the nested Leibniz rule
`r26t8a_nest p q Phi X z = D^p_Y (Y |-> D^q_w (w |-> Phi (Y,w)) z) X` is the object behind `mixedJet`.  We prove (norm identities,
no symmetry of higher derivatives needed):
* `r26t8a_nest_succ`: `||nest p (q+1) Phi|| = ||nest p q Phi_w||` with `Phi_w (Y,w) = fderiv (Phi (Y,.)) w`;
* `r26t8a_nest_bilinear`: the Leibniz bound for `Phi (Y,w) = B (f w) (G (Y,w))` with `f` depending on `w` only, by the induction of
  Mathlib's `norm_iteratedFDerivWithin_le_of_bilinear_aux` (all spaces in `Type`).
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A

section Mix

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `D^p_Y (Y |-> D^q_w Phi(Y,w) |_{w=z}) |_{Y=X}`. -/
def r26t8a_nest {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (p q : ℕ) (Φ : E × E → V) (X z : E) :=
  iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (fun w => Φ (Y, w)) z) X

/-- `w`-partial derivative of a two-variable function. -/
def r26t8a_dw {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (Φ : E × E → V) (Yw : E × E) : E →L[ℝ] V :=
  fderiv ℝ (fun w => Φ (Yw.1, w)) Yw.2

theorem r26t8a_nest_zero {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (p : ℕ) (Φ : E × E → V) (X z : E) :
    ‖r26t8a_nest p 0 Φ X z‖ = ‖iteratedFDeriv ℝ p (fun Y => Φ (Y, z)) X‖ := by
  unfold r26t8a_nest
  have h : (fun Y => iteratedFDeriv ℝ 0 (fun w => Φ (Y, w)) z) =
      (continuousMultilinearCurryFin0 ℝ E V).symm ∘ (fun Y => Φ (Y, z)) := by
    funext Y
    rw [iteratedFDeriv_zero_eq_comp]
    rfl
  rw [h]
  exact LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (continuousMultilinearCurryFin0 ℝ E V).symm
    (fun Y => Φ (Y, z)) X p

theorem r26t8a_nest_succ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (p q : ℕ) (Φ : E × E → V) (X z : E) :
    ‖r26t8a_nest p (q + 1) Φ X z‖ = ‖r26t8a_nest p q (r26t8a_dw Φ) X z‖ := by
  unfold r26t8a_nest
  have h : (fun Y => iteratedFDeriv ℝ (q + 1) (fun w => Φ (Y, w)) z) =
      (continuousMultilinearCurryRightEquiv' ℝ q E V).symm ∘
        (fun Y => iteratedFDeriv ℝ q (fun w => r26t8a_dw Φ (Y, w)) z) := by
    funext Y
    rw [iteratedFDeriv_succ_eq_comp_right]
    rfl
  rw [h]
  have key := LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (𝕜 := ℝ)
    (continuousMultilinearCurryRightEquiv' ℝ q E V).symm
    (fun Y => iteratedFDeriv ℝ q (fun w => r26t8a_dw Φ (Y, w)) z) X (i := p)
  exact key

theorem r26t8a_dw_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Φ : E × E → V} (hΦ : Differentiable ℝ Φ)
    (Yw : E × E) : r26t8a_dw Φ Yw = (fderiv ℝ Φ Yw).comp (ContinuousLinearMap.inr ℝ E E) := by
  unfold r26t8a_dw
  have := ((hΦ Yw).hasFDerivAt).comp Yw.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) Yw.1 Yw.2)
  exact this.fderiv

theorem r26t8a_dw_contDiff {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Φ : E × E → V} {n : ℕ}
    (hΦ : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) Φ) : ContDiff ℝ (n : WithTop ℕ∞) (r26t8a_dw Φ) := by
  have hd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have : r26t8a_dw Φ = fun Yw => (fderiv ℝ Φ Yw).comp (ContinuousLinearMap.inr ℝ E E) :=
    funext (r26t8a_dw_eq hd)
  rw [this]
  exact (hΦ.fderiv_right (by push_cast; exact le_rfl)).clm_comp contDiff_const

theorem r26t8a_nest_contDiff : ∀ (q p : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (Φ : E × E → V) (z : E),
    ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) Φ → ContDiff ℝ (p : WithTop ℕ∞) (fun Y => iteratedFDeriv ℝ q (fun w => Φ (Y, w)) z) := by
  intro q
  induction q with
  | zero =>
    intro p V _ _ Φ z hΦ
    have h : (fun Y => iteratedFDeriv ℝ 0 (fun w => Φ (Y, w)) z) =
        (continuousMultilinearCurryFin0 ℝ E V).symm ∘ (fun Y => Φ (Y, z)) := by
      funext Y
      rw [iteratedFDeriv_zero_eq_comp]
      rfl
    rw [h]
    exact (LinearIsometryEquiv.contDiff _).comp ((by simpa using hΦ : ContDiff ℝ (p : WithTop ℕ∞) Φ).comp
      (contDiff_id.prodMk contDiff_const))
  | succ q ih =>
    intro p V _ _ Φ z hΦ
    have h : (fun Y => iteratedFDeriv ℝ (q + 1) (fun w => Φ (Y, w)) z) =
        (continuousMultilinearCurryRightEquiv' ℝ q E V).symm ∘
          (fun Y => iteratedFDeriv ℝ q (fun w => r26t8a_dw Φ (Y, w)) z) := by
      funext Y
      rw [iteratedFDeriv_succ_eq_comp_right]
      rfl
    rw [h]
    refine (LinearIsometryEquiv.contDiff _).comp (ih p (r26t8a_dw Φ) z ?_)
    exact r26t8a_dw_contDiff (n := p + q) (by simpa [add_assoc] using hΦ)

theorem r26t8a_nest_add {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (p q : ℕ) (z X : E)
    {Φ Ψ : E × E → V} (hΦ : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) Φ) (hΨ : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) Ψ) :
    r26t8a_nest p q (fun Yw => Φ Yw + Ψ Yw) X z = r26t8a_nest p q Φ X z + r26t8a_nest p q Ψ X z := by
  unfold r26t8a_nest
  have hq : (q : WithTop ℕ∞) ≤ ((p + q : ℕ) : WithTop ℕ∞) := by exact_mod_cast Nat.le_add_left q p
  have h : (fun Y => iteratedFDeriv ℝ q (fun w => Φ (Y, w) + Ψ (Y, w)) z) =
      (fun Y => iteratedFDeriv ℝ q (fun w => Φ (Y, w)) z) + (fun Y => iteratedFDeriv ℝ q (fun w => Ψ (Y, w)) z) := by
    funext Y
    exact fun_iteratedFDeriv_add_apply
      (((hΦ.of_le hq).comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ (q : WithTop ℕ∞) fun w : E => (Y, w))).contDiffAt)
      (((hΨ.of_le hq).comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ (q : WithTop ℕ∞) fun w : E => (Y, w))).contDiffAt)
  rw [h]
  exact iteratedFDeriv_add_apply
    ((r26t8a_nest_contDiff q p Φ z hΦ).of_le (le_refl _) |>.contDiffAt)
    ((r26t8a_nest_contDiff q p Ψ z hΨ).of_le (le_refl _) |>.contDiffAt)

theorem r26t8a_nest_bilinear : ∀ (q p : ℕ) {F1 F2 F3 : Type} [NormedAddCommGroup F1] [NormedSpace ℝ F1]
    [NormedAddCommGroup F2] [NormedSpace ℝ F2] [NormedAddCommGroup F3] [NormedSpace ℝ F3]
    (B : F1 →L[ℝ] F2 →L[ℝ] F3) (f : E → F1) (G : E × E → F2) (X z : E),
    ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) f → ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) G →
    ‖r26t8a_nest p q (fun Yw => B (f Yw.2) (G Yw)) X z‖ ≤
      ‖B‖ * ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i f z‖ *
        ‖r26t8a_nest p (q - i) G X z‖ := by
  intro q
  induction q with
  | zero =>
    intro p F1 F2 F3 _ _ _ _ _ _ B f G X z hf hG
    rw [r26t8a_nest_zero]
    have hGz : ContDiff ℝ (p : WithTop ℕ∞) (fun Y => G (Y, z)) :=
      (by simpa using hG : ContDiff ℝ (p : WithTop ℕ∞) G).comp (contDiff_id.prodMk contDiff_const)
    have h1 : (fun Y => B (f z) (G (Y, z))) = (B (f z)) ∘ (fun Y => G (Y, z)) := rfl
    have h2 := (B (f z)).norm_iteratedFDeriv_comp_left (f := fun Y => G (Y, z)) (x := X) (N := (p : WithTop ℕ∞))
      hGz.contDiffAt (le_refl _) (n := p)
    have h3 : ‖B (f z)‖ ≤ ‖B‖ * ‖f z‖ := B.le_opNorm (f z)
    rw [zero_add, Finset.sum_range_one, Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_zero,
      norm_iteratedFDeriv_zero, r26t8a_nest_zero]
    show ‖iteratedFDeriv ℝ p (fun Y => B (f z) (G (Y, z))) X‖ ≤ _
    rw [h1]
    calc _ ≤ ‖B (f z)‖ * ‖iteratedFDeriv ℝ p (fun Y => G (Y, z)) X‖ := h2
      _ ≤ ‖B‖ * ‖f z‖ * ‖iteratedFDeriv ℝ p (fun Y => G (Y, z)) X‖ :=
          mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      _ = _ := by ring
  | succ q ih =>
    intro p F1 F2 F3 _ _ _ _ _ _ B f G X z hf hG
    rw [r26t8a_nest_succ]
    have hfd : Differentiable ℝ f := hf.differentiable (by simp)
    have hGd : Differentiable ℝ G := hG.differentiable (by simp)
    have hdw : r26t8a_dw (fun Yw => B (f Yw.2) (G Yw)) = fun Yw =>
        B.precompR E (f Yw.2) (r26t8a_dw G Yw) + B.precompL E (fderiv ℝ f Yw.2) (G Yw) := by
      funext Yw
      unfold r26t8a_dw
      exact B.fderiv_of_bilinear (hfd.differentiableAt) ((hGd.comp
        ((differentiable_const _).prodMk differentiable_id) : Differentiable ℝ fun w : E => G (Yw.1, w)).differentiableAt)
    rw [hdw]
    have hf1 : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) f := hf.of_le (by exact_mod_cast Nat.le_succ (p + q))
    have hf2 : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by push_cast; exact le_rfl)
    have hG1 : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) G := hG.of_le (by exact_mod_cast Nat.le_succ (p + q))
    have hGw : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (r26t8a_dw G) :=
      r26t8a_dw_contDiff (n := p + q) (by simpa [add_assoc] using hG)
    have hT1 : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun Yw : E × E => B.precompR E (f Yw.2) (r26t8a_dw G Yw)) :=
      (B.precompR E).isBoundedBilinearMap.contDiff.comp
        ((hf1.comp contDiff_snd).prodMk hGw)
    have hT2 : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun Yw : E × E => B.precompL E (fderiv ℝ f Yw.2) (G Yw)) :=
      (B.precompL E).isBoundedBilinearMap.contDiff.comp
        ((hf2.comp contDiff_snd).prodMk hG1)
    have hadd : ‖r26t8a_nest p q (fun Yw => B.precompR E (f Yw.2) (r26t8a_dw G Yw) +
          B.precompL E (fderiv ℝ f Yw.2) (G Yw)) X z‖ ≤
        ‖r26t8a_nest p q (fun Yw => B.precompR E (f Yw.2) (r26t8a_dw G Yw)) X z‖ +
        ‖r26t8a_nest p q (fun Yw => B.precompL E (fderiv ℝ f Yw.2) (G Yw)) X z‖ := by
      refine le_trans (le_of_eq ?_) (norm_add_le _ _)
      congr 1
      exact r26t8a_nest_add p q z X hT1 hT2
    have hq1 : ∀ i ∈ Finset.range (q + 1), ‖r26t8a_nest p (q - i) (r26t8a_dw G) X z‖ =
        ‖r26t8a_nest p (q + 1 - i) G X z‖ := by
      intro i hi
      have : q + 1 - i = (q - i) + 1 := by have := Finset.mem_range.1 hi; omega
      rw [this, r26t8a_nest_succ]
    have I1 := ih p (B.precompR E) f (r26t8a_dw G) X z hf1 hGw
    have I2 := ih p (B.precompL E) (fderiv ℝ f) G X z hf2 hG1
    have hsn1 : 0 ≤ ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i f z‖ *
        ‖r26t8a_nest p (q - i) (r26t8a_dw G) X z‖ :=
      Finset.sum_nonneg fun i _ => by positivity
    have hsn2 : 0 ≤ ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fderiv ℝ f) z‖ *
        ‖r26t8a_nest p (q - i) G X z‖ :=
      Finset.sum_nonneg fun i _ => by positivity
    have J1 := I1.trans (mul_le_mul_of_nonneg_right (B.norm_precompR_le E) hsn1)
    have J2 := I2.trans (mul_le_mul_of_nonneg_right (B.norm_precompL_le E) hsn2)
    have e1 : ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i f z‖ *
        ‖r26t8a_nest p (q - i) (r26t8a_dw G) X z‖ =
        ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) *
          (‖iteratedFDeriv ℝ i f z‖ * ‖r26t8a_nest p (q + 1 - i) G X z‖) :=
      Finset.sum_congr rfl fun i hi => by rw [hq1 i hi, mul_assoc]
    have e2 : ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fderiv ℝ f) z‖ *
        ‖r26t8a_nest p (q - i) G X z‖ =
        ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) *
          (‖iteratedFDeriv ℝ (i + 1) f z‖ * ‖r26t8a_nest p (q - i) G X z‖) :=
      Finset.sum_congr rfl fun i hi => by rw [norm_iteratedFDeriv_fderiv, mul_assoc]
    rw [e1] at J1
    rw [e2] at J2
    have hpas := Finset.sum_choose_succ_mul
      (fun i j => ‖iteratedFDeriv ℝ i f z‖ * ‖r26t8a_nest p j G X z‖) q
    calc _ ≤ _ := hadd
      _ ≤ ‖B‖ * (∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) *
            (‖iteratedFDeriv ℝ i f z‖ * ‖r26t8a_nest p (q + 1 - i) G X z‖)) +
          ‖B‖ * (∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) *
            (‖iteratedFDeriv ℝ (i + 1) f z‖ * ‖r26t8a_nest p (q - i) G X z‖)) := add_le_add J1 J2
      _ = _ := by
          rw [← mul_add]
          congr 1
          rw [← hpas]
          exact Finset.sum_congr rfl fun i _ => by ring

end Mix

end HRS.MS.R26T8A
