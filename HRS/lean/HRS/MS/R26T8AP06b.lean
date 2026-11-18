import HRS.MS.R26T8AP06b1

/-!
# S8.2 local Newton layer, packet T8A.P06b: nested-to-joint jet bound
`r26t8a_joint_le_nest`: for `Psi : E x E -> V` of class `C^j`,
`|D^j Psi (X,z)| <= sum_{q <= j} C(j,q) |nest (j-q) q Psi X z|`, where `nest p q Psi X z = D^p_Y D^q_w Psi` is the nested jet underlying `mixedJet`
(`r26t8a_nest`, `R26T8AMix`).  Proof: induction on `j` through `D^(j+1) Psi = D^j (dY Psi) (+) D^j (dw Psi)`, the key estimate
`|nest p q (dY Psi)| <= |nest (p+1) q Psi|` coming from the symmetry of the second derivative and `nest_succ`.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A

/-- `flip` as a linear isometry equivalence (with the standard normed-space instances on `E ->L E ->L V`). -/
def r26t8a_flipIso (E V : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] :
    (E →L[ℝ] E →L[ℝ] V) ≃ₗᵢ[ℝ] (E →L[ℝ] E →L[ℝ] V) where
  toFun := ContinuousLinearMap.flip
  invFun := ContinuousLinearMap.flip
  map_add' := ContinuousLinearMap.flip_add
  map_smul' := ContinuousLinearMap.flip_smul
  left_inv := ContinuousLinearMap.flip_flip
  right_inv := ContinuousLinearMap.flip_flip
  norm_map' := ContinuousLinearMap.opNorm_flip

section Conv

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem r26t8a_nest_clm' {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
    [NormedSpace ℝ W] (L : V →L[ℝ] W) (hL : ∀ v, ‖L v‖ ≤ ‖v‖) (p q : ℕ) (Φ : E × E → V) (X z : E)
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
    refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) (fun x => ?_)
    show ‖L (m x)‖ ≤ _
    exact (hL _).trans (m.le_opNorm x)
  refine (Lm.norm_iteratedFDeriv_comp_left hM.contDiffAt le_rfl).trans ?_
  exact mul_le_of_le_one_left (norm_nonneg _) hLm1

theorem r26t8a_dY_eq_slice {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Φ : E × E → V}
    (hΦ : Differentiable ℝ Φ) (Y z : E) :
    r26t8a_dY Φ (Y, z) = fderiv ℝ (fun Y' => Φ (Y', z)) Y := by
  have := ((hΦ (Y, z)).hasFDerivAt).comp Y (hasFDerivAt_prodMk_left (𝕜 := ℝ) Y z)
  exact this.fderiv.symm

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] in
theorem r26t8a_nest_flip (Φ : E × E → (E →L[ℝ] E →L[ℝ] V)) (p q : ℕ) (X z : E)
    (hΦ : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) Φ) :
    ‖r26t8a_nest p q (fun Yw => (r26t8a_flipIso E V) (Φ Yw)) X z‖ ≤ ‖r26t8a_nest p q Φ X z‖ := by
  have hL : ∀ T : E →L[ℝ] E →L[ℝ] V, ‖(r26t8a_flipIso E V).toLinearIsometry.toContinuousLinearMap T‖ ≤ ‖T‖ :=
    fun T => ((r26t8a_flipIso E V).norm_map T).le
  have := r26t8a_nest_clm' (V := E →L[ℝ] E →L[ℝ] V) (W := E →L[ℝ] E →L[ℝ] V)
    (r26t8a_flipIso E V).toLinearIsometry.toContinuousLinearMap hL p q Φ X z hΦ
  exact this

theorem r26t8a_nest_dY_le : ∀ (q p : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (Ψ : E × E → V) (X z : E),
    ContDiff ℝ ((p + q + 1 : ℕ) : WithTop ℕ∞) Ψ →
    ‖r26t8a_nest p q (r26t8a_dY Ψ) X z‖ ≤ ‖r26t8a_nest (p + 1) q Ψ X z‖ := by
  intro q
  induction q with
  | zero =>
    intro p V _ _ Ψ X z hΨ
    have hd : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
    rw [r26t8a_nest_zero, r26t8a_nest_zero]
    have : (fun Y => r26t8a_dY Ψ (Y, z)) = fun Y => fderiv ℝ (fun Y' => Ψ (Y', z)) Y :=
      funext fun Y => r26t8a_dY_eq_slice hd Y z
    rw [this, norm_iteratedFDeriv_fderiv]
  | succ q ih =>
    intro p V _ _ Ψ X z hΨ
    have e0 : p + (q + 1) + 1 = p + q + 1 + 1 := by omega
    rw [e0] at hΨ
    rw [r26t8a_nest_succ p q (r26t8a_dY Ψ), r26t8a_nest_succ (p + 1) q Ψ]
    have hd : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
    have hdY : ContDiff ℝ ((p + q + 1 : ℕ) : WithTop ℕ∞) (r26t8a_dY Ψ) := r26t8a_p06b_dY_contDiff hΨ
    have hdw : ContDiff ℝ ((p + q + 1 : ℕ) : WithTop ℕ∞) (r26t8a_dw Ψ) := r26t8a_dw_contDiff hΨ
    have hdYd : Differentiable ℝ (r26t8a_dY Ψ) := hdY.differentiable (by simp)
    have hdwd : Differentiable ℝ (r26t8a_dw Ψ) := hdw.differentiable (by simp)
    set Il : (E × E →L[ℝ] V) →L[ℝ] (E →L[ℝ] V) :=
      (ContinuousLinearMap.compL ℝ E (E × E) V).flip (ContinuousLinearMap.inl ℝ E E) with hIl
    set Ir : (E × E →L[ℝ] V) →L[ℝ] (E →L[ℝ] V) :=
      (ContinuousLinearMap.compL ℝ E (E × E) V).flip (ContinuousLinearMap.inr ℝ E E) with hIr
    have hdYf : r26t8a_dY Ψ = fun y => Il (fderiv ℝ Ψ y) := rfl
    have hdwf : r26t8a_dw Ψ = fun y => Ir (fderiv ℝ Ψ y) := by
      funext y; rw [r26t8a_dw_eq hd]; rfl
    have hsymm : ∀ y : E × E, ∀ a b : E × E, fderiv ℝ (fderiv ℝ Ψ) y a b = fderiv ℝ (fderiv ℝ Ψ) y b a := fun y a b => by
      have hy : ContDiffAt ℝ (2 : WithTop ℕ∞) Ψ y :=
        (hΨ.of_le (by exact_mod_cast (by omega : 2 ≤ p + q + 1 + 1))).contDiffAt
      exact hy.isSymmSndFDerivAt (by simp) a b
    have hfd2 : Differentiable ℝ (fderiv ℝ Ψ) := (hΨ.fderiv_right (m := p + q + 1)
      (by push_cast; exact le_rfl)).differentiable (by simp)
    have hflip : r26t8a_dw (r26t8a_dY Ψ) =
        fun y => (r26t8a_flipIso E V) (r26t8a_dY (r26t8a_dw Ψ) y) := by
      funext y
      rw [r26t8a_dw_eq hdYd]
      have h1 : fderiv ℝ (r26t8a_dY Ψ) y = Il.comp (fderiv ℝ (fderiv ℝ Ψ) y) := by
        rw [hdYf]; exact (Il.hasFDerivAt.comp y (hfd2 y).hasFDerivAt).fderiv
      have h2 : fderiv ℝ (r26t8a_dw Ψ) y = Ir.comp (fderiv ℝ (fderiv ℝ Ψ) y) := by
        rw [hdwf]; exact (Ir.hasFDerivAt.comp y (hfd2 y).hasFDerivAt).fderiv
      rw [h1]
      show _ = (r26t8a_flipIso E V) ((fderiv ℝ (r26t8a_dw Ψ) y).comp (ContinuousLinearMap.inl ℝ E E))
      rw [h2]
      ext v u
      simp only [hIl, hIr, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.compL_apply, ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
      exact hsymm y _ _
    rw [hflip]
    have hdYw : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (r26t8a_dY (r26t8a_dw Ψ)) :=
      r26t8a_p06b_dY_contDiff (n := p + q) (hdw.of_le (by exact_mod_cast le_rfl))
    exact (r26t8a_nest_flip (r26t8a_dY (r26t8a_dw Ψ)) p q X z hdYw).trans (ih p (r26t8a_dw Ψ) X z hdw)

theorem r26t8a_joint_le_nest : ∀ (j : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (Ψ : E × E → V) (X z : E),
    ContDiff ℝ (j : WithTop ℕ∞) Ψ →
    ‖iteratedFDeriv ℝ j Ψ (X, z)‖ ≤
      ∑ q ∈ Finset.range (j + 1), (j.choose q : ℝ) * ‖r26t8a_nest (j - q) q Ψ X z‖ := by
  intro j
  induction j with
  | zero =>
    intro V _ _ Ψ X z hΨ
    rw [norm_iteratedFDeriv_zero, Finset.sum_range_one, r26t8a_nest_zero, norm_iteratedFDeriv_zero]
    simp
  | succ j ih =>
    intro V _ _ Ψ X z hΨ
    refine (r26t8a_joint_step j hΨ (X, z)).trans ?_
    have hA := ih (r26t8a_dY Ψ) X z (r26t8a_p06b_dY_contDiff hΨ)
    have hB := ih (r26t8a_dw Ψ) X z (r26t8a_dw_contDiff hΨ)
    have hA' : ∀ q ∈ Finset.range (j + 1), ‖r26t8a_nest (j - q) q (r26t8a_dY Ψ) X z‖ ≤
        ‖r26t8a_nest (j + 1 - q) q Ψ X z‖ := fun q hq => by
      have hq' : q ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
      have e : j - q + q + 1 = j + 1 := by omega
      have := r26t8a_nest_dY_le q (j - q) Ψ X z (by rw [e]; exact hΨ)
      rwa [show j + 1 - q = j - q + 1 by omega]
    have hB' : ∀ q ∈ Finset.range (j + 1), ‖r26t8a_nest (j - q) q (r26t8a_dw Ψ) X z‖ =
        ‖r26t8a_nest (j - q) (q + 1) Ψ X z‖ := fun q _ => (r26t8a_nest_succ (j - q) q Ψ X z).symm
    calc _ ≤ _ := add_le_add hA hB
      _ ≤ ∑ q ∈ Finset.range (j + 1), (j.choose q : ℝ) * ‖r26t8a_nest (j + 1 - q) q Ψ X z‖ +
          ∑ q ∈ Finset.range (j + 1), (j.choose q : ℝ) * ‖r26t8a_nest (j - q) (q + 1) Ψ X z‖ :=
        add_le_add (Finset.sum_le_sum fun q hq =>
            mul_le_mul_of_nonneg_left (hA' q hq) (Nat.cast_nonneg _))
          (Finset.sum_le_sum fun q hq => by rw [hB' q hq])
      _ = _ := (Finset.sum_choose_succ_mul (fun i k => ‖r26t8a_nest k i Ψ X z‖) j).symm

end Conv

end HRS.MS.R26T8A
