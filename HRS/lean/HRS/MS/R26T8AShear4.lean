import HRS.MS.R26T8AShear3
import HRS.MS.R26T8AMix

/-!
# S8.2 shear calculus (4): nested jets and the shear bound
`r26t8a_nest_eq_word`: `nest p q Psi X z y w = sh_N p q y w Psi (X, z)`.
`r26t8a_shear`: `‖nest p q (Psi ∘ S_l) X z‖ <= sum_t C(q,t) |l|^t ‖nest (p+t) (q-t) Psi (X + l z) z‖`.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology

namespace HRS.MS.R26T8A

section Shear4

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem r26t8a_sh_slice_fderiv {Ψ : E × E → ℝ} (hΨ : Differentiable ℝ Ψ) (Y y u : E) :
    fderiv ℝ (fun w => Ψ (Y, w)) y u = fderiv ℝ Ψ (Y, y) (0, u) := by
  have := (hΨ (Y, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right (𝕜 := ℝ) Y y)
  rw [show (fun w => Ψ (Y, w)) = Ψ ∘ (fun w => (Y, w)) from rfl, this.fderiv]
  rfl

theorem r26t8a_sh_slice : ∀ (q : ℕ) (w : Fin q → E) (Ψ : E × E → ℝ),
    ContDiff ℝ (q : WithTop ℕ∞) Ψ → ∀ Y z : E,
    iteratedFDeriv ℝ q (fun u => Ψ (Y, u)) z w = r26t8a_sh_Nw q w Ψ (Y, z) := by
  intro q
  induction q with
  | zero => intro w Ψ _ Y z; simp [r26t8a_sh_Nw, iteratedFDeriv_zero_apply]
  | succ q ih =>
    intro w Ψ hΨ Y z
    have hsl : ContDiff ℝ ((q + 1 : ℕ) : WithTop ℕ∞) (fun u => Ψ (Y, u)) :=
      hΨ.comp (contDiff_const.prodMk contDiff_id)
    have hc : ContDiff ℝ (q : WithTop ℕ∞) (fderiv ℝ (fun u => Ψ (Y, u))) :=
      hsl.fderiv_right (by push_cast; exact le_rfl)
    rw [iteratedFDeriv_succ_apply_right]
    rw [← iteratedFDeriv_clm_apply_const_apply (u := w (Fin.last q)) hc le_rfl]
    have hd : Differentiable ℝ Ψ := hΨ.differentiable (Nat.cast_ne_zero.2 (by omega))
    have hfun : (fun y => (fderiv ℝ (fun u => Ψ (Y, u)) y) (w (Fin.last q))) =
        fun y => r26t8a_sh_DW (w (Fin.last q)) Ψ (Y, y) := by
      funext y; rw [r26t8a_sh_slice_fderiv hd]; rfl
    rw [hfun]
    exact ih (Fin.init w) _ (r26t8a_sh_contDiff_DW _ hΨ) Y z

theorem r26t8a_nest_eq_word : ∀ (p q : ℕ) (Ψ : E × E → ℝ),
    ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) Ψ → ∀ (X z : E) (y : Fin p → E) (w : Fin q → E),
    r26t8a_nest p q Ψ X z y w = r26t8a_sh_Ny p y (r26t8a_sh_Nw q w Ψ) (X, z) := by
  intro p
  induction p with
  | zero =>
    intro q Ψ hΨ X z y w
    have h := r26t8a_sh_slice q w Ψ (by simpa using hΨ) X z
    unfold r26t8a_nest
    simpa [r26t8a_sh_Ny, iteratedFDeriv_zero_apply] using h
  | succ p ih =>
    intro q Ψ hΨ X z y w
    have hΨ' : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) Ψ :=
      hΨ.of_le (by exact_mod_cast (by omega : p + q ≤ p + 1 + q))
    have hJ := r26t8a_nest_contDiff q (p + 1) Ψ z hΨ
    set J : E → ContinuousMultilinearMap ℝ (fun _ : Fin q => E) ℝ :=
      fun Y => iteratedFDeriv ℝ q (fun u => Ψ (Y, u)) z with hJdef
    have hd1 : DifferentiableAt ℝ (iteratedFDeriv ℝ p J) X :=
      (hJ.differentiable_iteratedFDeriv (m := p) (by exact_mod_cast Nat.lt_succ_self p)) X
    set G : E × E → ℝ := r26t8a_sh_Nw q w Ψ with hG
    have hGc : ContDiff ℝ ((p + 1 : ℕ) : WithTop ℕ∞) G :=
      r26t8a_sh_contDiff_Nw q (p + 1) w Ψ (by rwa [add_comm])
    have hH : Differentiable ℝ (r26t8a_sh_Ny p (Fin.tail y) G) :=
      (r26t8a_sh_contDiff_Ny p 1 (Fin.tail y) G (by simpa using hGc)).differentiable (by simp)
    have e1 : r26t8a_nest (p + 1) q Ψ X z y w =
        (fderiv ℝ (iteratedFDeriv ℝ p J) X (y 0) (Fin.tail y)) w := by
      unfold r26t8a_nest
      rw [iteratedFDeriv_succ_apply_left]
    rw [e1]
    have e2 := fderiv_continuousMultilinear_apply_const_apply hd1 (Fin.tail y) (y 0)
    have hd2 : DifferentiableAt ℝ (fun X' => (iteratedFDeriv ℝ p J X') (Fin.tail y)) X :=
      hd1.continuousMultilinear_apply_const _
    have e3 := fderiv_continuousMultilinear_apply_const_apply hd2 w (y 0)
    rw [← e2, ← e3]
    have hfun : (fun X' => ((iteratedFDeriv ℝ p J X') (Fin.tail y)) w) =
        fun X' => r26t8a_sh_Ny p (Fin.tail y) G (X', z) := by
      funext X'
      exact ih q Ψ hΨ' X' z (Fin.tail y) w
    rw [hfun]
    have := (hH (X, z)).hasFDerivAt.comp X (hasFDerivAt_prodMk_left (𝕜 := ℝ) X z)
    rw [show (fun X' => r26t8a_sh_Ny p (Fin.tail y) G (X', z)) =
      (r26t8a_sh_Ny p (Fin.tail y) G) ∘ (fun X' => (X', z)) from rfl, this.fderiv]
    rfl

theorem r26t8a_sh_eval_le {p q : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin p => E)
    (ContinuousMultilinearMap ℝ (fun _ : Fin q => E) ℝ)) (y : Fin p → E) (w : Fin q → E) :
    |M y w| ≤ ‖M‖ * (∏ i, ‖y i‖) * ∏ j, ‖w j‖ := by
  have h1 := (M y).le_opNorm w
  have h2 := M.le_opNorm y
  rw [← Real.norm_eq_abs]
  calc ‖M y w‖ ≤ ‖M y‖ * ∏ j, ‖w j‖ := h1
    _ ≤ (‖M‖ * ∏ i, ‖y i‖) * ∏ j, ‖w j‖ :=
        mul_le_mul_of_nonneg_right h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _)

theorem r26t8a_sh_norm_le {p q : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin p => E)
    (ContinuousMultilinearMap ℝ (fun _ : Fin q => E) ℝ)) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ (y : Fin p → E) (w : Fin q → E), |M y w| ≤ C * (∏ i, ‖y i‖) * ∏ j, ‖w j‖) : ‖M‖ ≤ C := by
  refine M.opNorm_le_bound hC (fun y => ?_)
  refine (M y).opNorm_le_bound (by positivity) (fun w => ?_)
  rw [Real.norm_eq_abs]
  exact h y w

/-- The shear bound for nested jets. -/
theorem r26t8a_shear (l : ℝ) (p q : ℕ) (Ψ : E × E → ℝ)
    (hΨ : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) Ψ) (X z : E) :
    ‖r26t8a_nest p q (fun Yw : E × E => Ψ (Yw.1 + l • Yw.2, Yw.2)) X z‖ ≤
      ∑ t ∈ Finset.range (q + 1), (q.choose t : ℝ) * |l| ^ t * ‖r26t8a_nest (p + t) (q - t) Ψ (X + l • z) z‖ := by
  set B : ℕ → ℕ → ℝ := fun a b => ‖r26t8a_nest a b Ψ (X + l • z) z‖ with hB
  have hS : ContDiff ℝ ⊤ (r26t8a_sh_S (E := E) l) := ContinuousLinearMap.contDiff (𝕜 := ℝ) (r26t8a_sh_S (E := E) l)
  have hΨs : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun Yw : E × E => Ψ (Yw.1 + l • Yw.2, Yw.2)) :=
    hΨ.comp (hS.of_le le_top)
  have hsum : 0 ≤ ∑ t ∈ Finset.range (q + 1), (q.choose t : ℝ) * |l| ^ t * B (p + t) (q - t) :=
    Finset.sum_nonneg fun t _ => by positivity
  refine r26t8a_sh_norm_le _ hsum (fun y w => ?_)
  rw [r26t8a_nest_eq_word p q _ hΨs X z y w]
  have := r26t8a_sh_bound l q p Ψ hΨ (X, z) B ?_ y w
  · exact this
  · intro a b hab y' w''
    have hΨab : ContDiff ℝ ((a + b : ℕ) : WithTop ℕ∞) Ψ :=
      hΨ.of_le (by exact_mod_cast hab)
    have e := r26t8a_nest_eq_word a b Ψ hΨab (X + l • z) z y' w''
    have e' : r26t8a_sh_S l (X, z) = (X + l • z, z) := rfl
    rw [e']
    show |r26t8a_sh_Ny a y' (r26t8a_sh_Nw b w'' Ψ) (X + l • z, z)| ≤ _
    rw [← e]
    exact r26t8a_sh_eval_le _ y' w''

end Shear4

end HRS.MS.R26T8A
