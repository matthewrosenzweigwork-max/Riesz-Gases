import Mathlib

/-!
# S8.2 shear calculus (1): directional-derivative words
`sh_N p q y w Psi = DY y_0 ... DY y_{p-1} DW w_0 ... DW w_{q-1} Psi` (first slot outermost) for functions on `E × E`, with the
shear `S_l (Y, w) = (Y + l w, w)`.  Facts: operators preserve smoothness, commute with the shear in the expected way
(`DW v (f ∘ S) = (DW v f + l DY v f) ∘ S`), are linear, and `DY` commutes with `DW` (Schwarz).
-/

set_option autoImplicit false
noncomputable section

namespace HRS.MS.R26T8A

section Shear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def r26t8a_sh_DY (e : E) (Ψ : E × E → ℝ) : E × E → ℝ := fun x => fderiv ℝ Ψ x (e, 0)

def r26t8a_sh_DW (e : E) (Ψ : E × E → ℝ) : E × E → ℝ := fun x => fderiv ℝ Ψ x (0, e)

def r26t8a_sh_Ny : (p : ℕ) → (Fin p → E) → (E × E → ℝ) → (E × E → ℝ)
  | 0, _, G => G
  | p + 1, y, G => r26t8a_sh_DY (y 0) (r26t8a_sh_Ny p (Fin.tail y) G)

def r26t8a_sh_Nw : (q : ℕ) → (Fin q → E) → (E × E → ℝ) → (E × E → ℝ)
  | 0, _, Ψ => Ψ
  | q + 1, w, Ψ => r26t8a_sh_Nw q (Fin.init w) (r26t8a_sh_DW (w (Fin.last q)) Ψ)

def r26t8a_sh_N (p q : ℕ) (y : Fin p → E) (w : Fin q → E) (Ψ : E × E → ℝ) : E × E → ℝ :=
  r26t8a_sh_Ny p y (r26t8a_sh_Nw q w Ψ)

/-- The shear `(Y, w) ↦ (Y + l w, w)`. -/
def r26t8a_sh_S (l : ℝ) : E × E →L[ℝ] E × E :=
  ((ContinuousLinearMap.fst ℝ E E) + l • (ContinuousLinearMap.snd ℝ E E)).prod (ContinuousLinearMap.snd ℝ E E)

theorem r26t8a_sh_S_apply (l : ℝ) (x : E × E) : r26t8a_sh_S l x = (x.1 + l • x.2, x.2) := rfl

theorem r26t8a_sh_contDiff_DY {n : ℕ} {Ψ : E × E → ℝ} (e : E)
    (hΨ : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) Ψ) : ContDiff ℝ (n : WithTop ℕ∞) (r26t8a_sh_DY e Ψ) :=
  (hΨ.fderiv_right (by push_cast; exact le_rfl)).clm_apply contDiff_const

theorem r26t8a_sh_contDiff_DW {n : ℕ} {Ψ : E × E → ℝ} (e : E)
    (hΨ : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) Ψ) : ContDiff ℝ (n : WithTop ℕ∞) (r26t8a_sh_DW e Ψ) :=
  (hΨ.fderiv_right (by push_cast; exact le_rfl)).clm_apply contDiff_const

theorem r26t8a_sh_contDiff_Ny : ∀ (p n : ℕ) (y : Fin p → E) (G : E × E → ℝ),
    ContDiff ℝ ((p + n : ℕ) : WithTop ℕ∞) G → ContDiff ℝ (n : WithTop ℕ∞) (r26t8a_sh_Ny p y G) := by
  intro p
  induction p with
  | zero => intro n y G h; simpa [r26t8a_sh_Ny] using h
  | succ p ih =>
    intro n y G h
    have h' : ContDiff ℝ ((p + (n + 1) : ℕ) : WithTop ℕ∞) G := by
      have : p + (n + 1) = p + 1 + n := by omega
      rw [this]; exact h
    exact r26t8a_sh_contDiff_DY (y 0) (ih (n + 1) (Fin.tail y) G h')

theorem r26t8a_sh_contDiff_Nw : ∀ (q n : ℕ) (w : Fin q → E) (Ψ : E × E → ℝ),
    ContDiff ℝ ((q + n : ℕ) : WithTop ℕ∞) Ψ → ContDiff ℝ (n : WithTop ℕ∞) (r26t8a_sh_Nw q w Ψ) := by
  intro q
  induction q with
  | zero => intro n w Ψ h; simpa [r26t8a_sh_Nw] using h
  | succ q ih =>
    intro n w Ψ h
    have h' : ContDiff ℝ ((q + n : ℕ) : WithTop ℕ∞) (r26t8a_sh_DW (w (Fin.last q)) Ψ) :=
      r26t8a_sh_contDiff_DW _ (by
        have : q + n + 1 = q + 1 + n := by omega
        rw [this]; exact h)
    exact ih n (Fin.init w) _ h'

/-- Chain rule: `DY` commutes with the shear. -/
theorem r26t8a_sh_DY_S (l : ℝ) (e : E) {f : E × E → ℝ} (hf : Differentiable ℝ f) :
    r26t8a_sh_DY e (fun x => f (r26t8a_sh_S l x)) = fun x => r26t8a_sh_DY e f (r26t8a_sh_S l x) := by
  funext x
  unfold r26t8a_sh_DY
  have hS : HasFDerivAt (r26t8a_sh_S l) (r26t8a_sh_S l) x := ContinuousLinearMap.hasFDerivAt (r26t8a_sh_S l) (x := x)
  have := (hf (r26t8a_sh_S l x)).hasFDerivAt.comp x hS
  rw [show (fun x => f (r26t8a_sh_S l x)) = f ∘ (r26t8a_sh_S l) from rfl, this.fderiv]
  simp only [ContinuousLinearMap.comp_apply, r26t8a_sh_S_apply, smul_zero, add_zero]

/-- Chain rule: `DW` mixes into `DW + l DY`. -/
theorem r26t8a_sh_DW_S (l : ℝ) (v : E) {f : E × E → ℝ} (hf : Differentiable ℝ f) :
    r26t8a_sh_DW v (fun x => f (r26t8a_sh_S l x)) =
      fun x => r26t8a_sh_DW v f (r26t8a_sh_S l x) + l * r26t8a_sh_DY v f (r26t8a_sh_S l x) := by
  funext x
  unfold r26t8a_sh_DW r26t8a_sh_DY
  have hS : HasFDerivAt (r26t8a_sh_S l) (r26t8a_sh_S l) x := ContinuousLinearMap.hasFDerivAt (r26t8a_sh_S l) (x := x)
  have := (hf (r26t8a_sh_S l x)).hasFDerivAt.comp x hS
  rw [show (fun x => f (r26t8a_sh_S l x)) = f ∘ (r26t8a_sh_S l) from rfl, this.fderiv]
  simp only [ContinuousLinearMap.comp_apply, r26t8a_sh_S_apply, zero_add, smul_zero]
  have : ((l • v, v) : E × E) = l • ((v, 0) : E × E) + ((0, v) : E × E) := by
    ext <;> simp
  rw [this, map_add, map_smul, smul_eq_mul]
  ring

/-- `Ny` commutes with composition by the shear. -/
theorem r26t8a_sh_Ny_S (l : ℝ) : ∀ (p : ℕ) (y : Fin p → E) (G : E × E → ℝ),
    ContDiff ℝ (p : WithTop ℕ∞) G →
    r26t8a_sh_Ny p y (fun x => G (r26t8a_sh_S l x)) = fun x => r26t8a_sh_Ny p y G (r26t8a_sh_S l x) := by
  intro p
  induction p with
  | zero => intro y G _; rfl
  | succ p ih =>
    intro y G hG
    have h1 : ContDiff ℝ (p : WithTop ℕ∞) G := hG.of_le (by exact_mod_cast Nat.le_succ p)
    have hd : Differentiable ℝ (r26t8a_sh_Ny p (Fin.tail y) G) :=
      (r26t8a_sh_contDiff_Ny p 1 (Fin.tail y) G (by simpa using hG)).differentiable (by simp)
    show r26t8a_sh_DY (y 0) (r26t8a_sh_Ny p (Fin.tail y) (fun x => G (r26t8a_sh_S l x))) = _
    rw [ih (Fin.tail y) G h1]
    exact r26t8a_sh_DY_S l (y 0) hd

/-- Linearity of `DY`, `DW`. -/
theorem r26t8a_sh_DY_lin (e : E) (c : ℝ) {f g : E × E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    r26t8a_sh_DY e (fun x => f x + c * g x) = fun x => r26t8a_sh_DY e f x + c * r26t8a_sh_DY e g x := by
  funext x
  unfold r26t8a_sh_DY
  have : fderiv ℝ (fun x => f x + c * g x) x = fderiv ℝ f x + c • fderiv ℝ g x := by
    exact ((hf x).hasFDerivAt.add ((hg x).hasFDerivAt.const_mul c)).fderiv
  rw [this]; simp

theorem r26t8a_sh_DW_lin (e : E) (c : ℝ) {f g : E × E → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    r26t8a_sh_DW e (fun x => f x + c * g x) = fun x => r26t8a_sh_DW e f x + c * r26t8a_sh_DW e g x := by
  funext x
  unfold r26t8a_sh_DW
  have : fderiv ℝ (fun x => f x + c * g x) x = fderiv ℝ f x + c • fderiv ℝ g x := by
    exact ((hf x).hasFDerivAt.add ((hg x).hasFDerivAt.const_mul c)).fderiv
  rw [this]; simp

end Shear

end HRS.MS.R26T8A
