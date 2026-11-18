import HRS.MS.R26T8AMix

/-!
# S8.2 nonlocal layer: continuity and support of partial iterated derivatives
For `Phi : E x E -> V` of class `C^(p+q)`: `(Y,w) |-> nest p q Phi Y w` is continuous
(needed for measurability in the differentiation-under-the-integral lemma), the nested jets
vanish where `Phi` vanishes near `w` for all `Y`, and are compatible with translation in `w`.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A

section Pot2

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `D^q_w Phi (Y,w)` is `C^p` jointly when `Phi` is `C^(p+q)`. -/
theorem r26t8a_Jq_contDiff : ∀ (q p : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Φ : E × E → V), ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) Φ →
    ContDiff ℝ (p : WithTop ℕ∞) (fun Yw : E × E => iteratedFDeriv ℝ q (fun w => Φ (Yw.1, w)) Yw.2) := by
  intro q
  induction q with
  | zero =>
    intro p V _ _ Φ hΦ
    have h : (fun Yw : E × E => iteratedFDeriv ℝ 0 (fun w => Φ (Yw.1, w)) Yw.2) =
        (continuousMultilinearCurryFin0 ℝ E V).symm ∘ Φ := by
      funext Yw
      rw [iteratedFDeriv_zero_eq_comp]
      rfl
    rw [h]
    exact (LinearIsometryEquiv.contDiff _).comp (by simpa using hΦ)
  | succ q ih =>
    intro p V _ _ Φ hΦ
    have h : (fun Yw : E × E => iteratedFDeriv ℝ (q + 1) (fun w => Φ (Yw.1, w)) Yw.2) =
        (continuousMultilinearCurryRightEquiv' ℝ q E V).symm ∘
          (fun Yw : E × E => iteratedFDeriv ℝ q (fun w => r26t8a_dw Φ (Yw.1, w)) Yw.2) := by
      funext Yw
      rw [iteratedFDeriv_succ_eq_comp_right]
      rfl
    rw [h]
    refine (LinearIsometryEquiv.contDiff _).comp (ih p (r26t8a_dw Φ) ?_)
    exact r26t8a_dw_contDiff (n := p + q) (by simpa [add_assoc] using hΦ)

/-- `dY`: the `Y`-partial derivative of a two-variable function. -/
theorem r26t8a_dY_contDiff {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Ψ : E × E → V} {n : ℕ}
    (hΨ : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) Ψ) :
    ContDiff ℝ (n : WithTop ℕ∞) (fun Yw : E × E => (fderiv ℝ Ψ Yw).comp (ContinuousLinearMap.inl ℝ E E)) :=
  (hΨ.fderiv_right (by push_cast; exact le_rfl)).clm_comp contDiff_const

theorem r26t8a_dY_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Ψ : E × E → V}
    (hΨ : Differentiable ℝ Ψ) (Y w : E) :
    fderiv ℝ (fun Y' => Ψ (Y', w)) Y = (fderiv ℝ Ψ (Y, w)).comp (ContinuousLinearMap.inl ℝ E E) := by
  have := ((hΨ (Y, w)).hasFDerivAt).comp Y (hasFDerivAt_prodMk_left (𝕜 := ℝ) Y w)
  exact this.fderiv

/-- Joint continuity of the `p`-th derivative in `Y` of a `C^p` function. -/
theorem r26t8a_partialY_continuous : ∀ (p : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Ψ : E × E → V), ContDiff ℝ (p : WithTop ℕ∞) Ψ →
    Continuous (fun Yw : E × E => iteratedFDeriv ℝ p (fun Y => Ψ (Y, Yw.2)) Yw.1) := by
  intro p
  induction p with
  | zero =>
    intro V _ _ Ψ hΨ
    have h : (fun Yw : E × E => iteratedFDeriv ℝ 0 (fun Y => Ψ (Y, Yw.2)) Yw.1) =
        (continuousMultilinearCurryFin0 ℝ E V).symm ∘ Ψ := by
      funext Yw
      rw [iteratedFDeriv_zero_eq_comp]
      rfl
    rw [h]
    exact (LinearIsometryEquiv.continuous _).comp (by simpa using hΨ.continuous)
  | succ p ih =>
    intro V _ _ Ψ hΨ
    have hd : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
    have h : (fun Yw : E × E => iteratedFDeriv ℝ (p + 1) (fun Y => Ψ (Y, Yw.2)) Yw.1) =
        (continuousMultilinearCurryRightEquiv' ℝ p E V).symm ∘
          (fun Yw : E × E => iteratedFDeriv ℝ p
            (fun Y => (fderiv ℝ Ψ (Y, Yw.2)).comp (ContinuousLinearMap.inl ℝ E E)) Yw.1) := by
      funext Yw
      rw [iteratedFDeriv_succ_eq_comp_right]
      simp only [Function.comp]
      congr 2
      funext Y
      exact r26t8a_dY_eq hd Y Yw.2
    rw [h]
    exact (LinearIsometryEquiv.continuous _).comp
      (ih (V := E →L[ℝ] V) (fun Yw : E × E => (fderiv ℝ Ψ Yw).comp (ContinuousLinearMap.inl ℝ E E))
        (r26t8a_dY_contDiff (n := p) hΨ))

theorem r26t8a_nest_continuous (p q : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Φ : E × E → V) (hΦ : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) Φ) :
    Continuous (fun Yw : E × E => r26t8a_nest p q Φ Yw.1 Yw.2) := by
  have h1 := r26t8a_Jq_contDiff q p Φ hΦ
  exact r26t8a_partialY_continuous p _ h1

theorem r26t8a_nest_eq_zero (p q : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Φ : E × E → V) (X z : E) (hz : ∀ᶠ w in 𝓝 z, ∀ Y, Φ (Y, w) = 0) :
    r26t8a_nest p q Φ X z = 0 := by
  unfold r26t8a_nest
  have h : ∀ Y, iteratedFDeriv ℝ q (fun w => Φ (Y, w)) z = 0 := by
    intro Y
    have hev : (fun w => Φ (Y, w)) =ᶠ[𝓝 z] fun _ => (0 : V) := hz.mono fun w hw => hw Y
    rw [(hev.iteratedFDeriv ℝ q).self_of_nhds, iteratedFDeriv_zero_fun]
    rfl
  have : (fun Y => iteratedFDeriv ℝ q (fun w => Φ (Y, w)) z) = fun _ => 0 := funext h
  rw [this]
  simp [iteratedFDeriv_zero_fun]

theorem r26t8a_nest_sub_right (p q : ℕ) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Φ : E × E → V) (u X z : E) :
    r26t8a_nest p q (fun Yw => Φ (Yw.1, Yw.2 - u)) X z = r26t8a_nest p q Φ X (z - u) := by
  unfold r26t8a_nest
  congr 1
  funext Y
  exact iteratedFDeriv_comp_sub (f := fun w => Φ (Y, w)) q u z

end Pot2

end HRS.MS.R26T8A
