import HRS.MS.R26T8AShear1

/-!
# S8.2 shear calculus (2): commutation and the shear bound for derivative words
`r26t8a_sh_bound`: if the words `sh_N a b y w Psi` at the point `S x` are bounded by `B a b (prod |y_i|)(prod |w_j|)`,
then `|sh_N p q y w (Psi ∘ S) x| <= (sum_t C(q,t) |l|^t B (p+t) (q-t)) (prod |y_i|) (prod |w_j|)`.
-/

set_option autoImplicit false
noncomputable section

namespace HRS.MS.R26T8A

section Shear2

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Schwarz: `DW` and `DY` commute on `C^2` functions. -/
theorem r26t8a_sh_comm (e v : E) {f : E × E → ℝ} (hf : ContDiff ℝ 2 f) :
    r26t8a_sh_DW v (r26t8a_sh_DY e f) = r26t8a_sh_DY e (r26t8a_sh_DW v f) := by
  funext x
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by simp) x
  have hsym := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp) (v := (e, 0)) (w := (0, v))
  have key : ∀ u w : E × E, fderiv ℝ (fun y => fderiv ℝ f y u) x w = fderiv ℝ (fderiv ℝ f) x w u := by
    intro u w
    have := (ContinuousLinearMap.apply ℝ ℝ u).hasFDerivAt.comp x hd.hasFDerivAt
    rw [show (fun y => fderiv ℝ f y u) = (ContinuousLinearMap.apply ℝ ℝ u) ∘ (fderiv ℝ f) from rfl,
      this.fderiv]
    rfl
  unfold r26t8a_sh_DW r26t8a_sh_DY
  rw [key, key]
  exact hsym.symm

theorem r26t8a_sh_Ny_lin (c : ℝ) : ∀ (p : ℕ) (y : Fin p → E) (f g : E × E → ℝ),
    ContDiff ℝ (p : WithTop ℕ∞) f → ContDiff ℝ (p : WithTop ℕ∞) g →
    r26t8a_sh_Ny p y (fun x => f x + c * g x) = fun x => r26t8a_sh_Ny p y f x + c * r26t8a_sh_Ny p y g x := by
  intro p
  induction p with
  | zero => intro y f g _ _; rfl
  | succ p ih =>
    intro y f g hf hg
    have hf' : ContDiff ℝ (p : WithTop ℕ∞) f := hf.of_le (by exact_mod_cast Nat.le_succ p)
    have hg' : ContDiff ℝ (p : WithTop ℕ∞) g := hg.of_le (by exact_mod_cast Nat.le_succ p)
    show r26t8a_sh_DY (y 0) (r26t8a_sh_Ny p (Fin.tail y) (fun x => f x + c * g x)) = _
    rw [ih (Fin.tail y) f g hf' hg']
    exact r26t8a_sh_DY_lin (y 0) c
      ((r26t8a_sh_contDiff_Ny p 1 (Fin.tail y) f (by simpa using hf)).differentiable (by simp))
      ((r26t8a_sh_contDiff_Ny p 1 (Fin.tail y) g (by simpa using hg)).differentiable (by simp))

theorem r26t8a_sh_Nw_lin (c : ℝ) : ∀ (q : ℕ) (w : Fin q → E) (f g : E × E → ℝ),
    ContDiff ℝ (q : WithTop ℕ∞) f → ContDiff ℝ (q : WithTop ℕ∞) g →
    r26t8a_sh_Nw q w (fun x => f x + c * g x) = fun x => r26t8a_sh_Nw q w f x + c * r26t8a_sh_Nw q w g x := by
  intro q
  induction q with
  | zero => intro w f g _ _; rfl
  | succ q ih =>
    intro w f g hf hg
    show r26t8a_sh_Nw q (Fin.init w) (r26t8a_sh_DW (w (Fin.last q)) (fun x => f x + c * g x)) = _
    rw [r26t8a_sh_DW_lin (w (Fin.last q)) c (hf.differentiable (by simp)) (hg.differentiable (by simp))]
    exact ih (Fin.init w) _ _ (r26t8a_sh_contDiff_DW _ hf) (r26t8a_sh_contDiff_DW _ hg)

theorem r26t8a_sh_N_lin (c : ℝ) (p q : ℕ) (y : Fin p → E) (w : Fin q → E) {f g : E × E → ℝ}
    (hf : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) f) (hg : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) g) (x : E × E) :
    r26t8a_sh_N p q y w (fun z => f z + c * g z) x =
      r26t8a_sh_N p q y w f x + c * r26t8a_sh_N p q y w g x := by
  unfold r26t8a_sh_N
  have hqf : ContDiff ℝ (q : WithTop ℕ∞) f := hf.of_le (by exact_mod_cast Nat.le_add_left q p)
  have hqg : ContDiff ℝ (q : WithTop ℕ∞) g := hg.of_le (by exact_mod_cast Nat.le_add_left q p)
  rw [r26t8a_sh_Nw_lin c q w f g hqf hqg]
  have hpf : ContDiff ℝ (p : WithTop ℕ∞) (r26t8a_sh_Nw q w f) :=
    r26t8a_sh_contDiff_Nw q p w f (by rwa [add_comm])
  have hpg : ContDiff ℝ (p : WithTop ℕ∞) (r26t8a_sh_Nw q w g) :=
    r26t8a_sh_contDiff_Nw q p w g (by rwa [add_comm])
  rw [r26t8a_sh_Ny_lin c p y _ _ hpf hpg]

/-- `Ny` of a snoc'ed word. -/
theorem r26t8a_sh_Ny_snoc : ∀ (a : ℕ) (y : Fin a → E) (e : E) (G : E × E → ℝ),
    r26t8a_sh_Ny (a + 1) (Fin.snoc y e) G = r26t8a_sh_Ny a y (r26t8a_sh_DY e G) := by
  intro a
  induction a with
  | zero => intro y e G; simp [r26t8a_sh_Ny, Fin.snoc]
  | succ a ih =>
    intro y e G
    show r26t8a_sh_DY ((Fin.snoc y e : Fin (a + 2) → E) 0)
        (r26t8a_sh_Ny (a + 1) (Fin.tail (Fin.snoc y e : Fin (a + 2) → E)) G) =
      r26t8a_sh_DY (y 0) (r26t8a_sh_Ny a (Fin.tail y) (r26t8a_sh_DY e G))
    have h0 : (Fin.snoc y e : Fin (a + 2) → E) 0 = y 0 := by
      have : (0 : Fin (a + 2)) = Fin.castSucc (0 : Fin (a + 1)) := rfl
      rw [this, Fin.snoc_castSucc]
    have ht : Fin.tail (Fin.snoc y e : Fin (a + 2) → E) = Fin.snoc (Fin.tail y) e := by
      funext i
      induction i using Fin.lastCases with
      | last => simp only [Fin.tail, Fin.succ_last, Fin.snoc_last]
      | cast i => simp only [Fin.tail, Fin.succ_castSucc, Fin.snoc_castSucc]
    rw [h0, ht, ih (Fin.tail y) e G]

theorem r26t8a_sh_Nw_snoc : ∀ (b : ℕ) (w : Fin b → E) (e : E) (Ψ : E × E → ℝ),
    r26t8a_sh_Nw (b + 1) (Fin.snoc w e) Ψ = r26t8a_sh_Nw b w (r26t8a_sh_DW e Ψ) := by
  intro b w e Ψ
  show r26t8a_sh_Nw b (Fin.init (Fin.snoc w e : Fin (b + 1) → E))
      (r26t8a_sh_DW ((Fin.snoc w e : Fin (b + 1) → E) (Fin.last b)) Ψ) = _
  rw [Fin.init_snoc, Fin.snoc_last]

/-- `Nw` commutes with `DY` on sufficiently smooth functions. -/
theorem r26t8a_sh_Nw_DY : ∀ (q : ℕ) (w : Fin q → E) (e : E) (f : E × E → ℝ),
    ContDiff ℝ ((q + 1 : ℕ) : WithTop ℕ∞) f →
    r26t8a_sh_Nw q w (r26t8a_sh_DY e f) = r26t8a_sh_DY e (r26t8a_sh_Nw q w f) := by
  intro q
  induction q with
  | zero => intro w e f _; rfl
  | succ q ih =>
    intro w e f hf
    show r26t8a_sh_Nw q (Fin.init w) (r26t8a_sh_DW (w (Fin.last q)) (r26t8a_sh_DY e f)) =
      r26t8a_sh_DY e (r26t8a_sh_Nw q (Fin.init w) (r26t8a_sh_DW (w (Fin.last q)) f))
    rw [r26t8a_sh_comm e _ (hf.of_le (by exact_mod_cast (by omega : 2 ≤ q + 1 + 1)))]
    exact ih (Fin.init w) e _ (r26t8a_sh_contDiff_DW _ hf)

end Shear2

end HRS.MS.R26T8A
