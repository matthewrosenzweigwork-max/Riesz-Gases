import HRS.PDE.TorusFPExistAux2

/-!
# D1 existence, helper 3: algebra of classical backward solutions

Linear combinations, constants, time shift, the sup-norm contraction (from the maximum principle) and
uniqueness of `D1BackwardSolution`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS

variable {n : ℕ}

theorem d1_isCk2_lincomb {f g : Torus n → ℝ} (hf : Torus.IsCk 2 f) (hg : Torus.IsCk 2 g) (a c : ℝ) :
    Torus.IsCk 2 (fun x => a * f x + c * g x) := by
  have h1 : ContDiff ℝ 2 (Torus.lift f) := by
    have : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (Torus.lift f) := hf
    simpa using this
  have h2 : ContDiff ℝ 2 (Torus.lift g) := by
    have : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (Torus.lift g) := hg
    simpa using this
  have : ContDiff ℝ 2 (fun y => a * Torus.lift f y + c * Torus.lift g y) :=
    (contDiff_const.mul h1).add (contDiff_const.mul h2)
  exact this

theorem d1_laplacian_lincomb {f g : Torus n → ℝ} (hf : Torus.IsCk 2 f) (hg : Torus.IsCk 2 g)
    (a c : ℝ) (x : Torus n) :
    Torus.laplacian (fun x => a * f x + c * g x) x = a * Torus.laplacian f x + c * Torus.laplacian g x := by
  have h1 : ContDiff ℝ 2 (Torus.lift f) := by
    have : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (Torus.lift f) := hf
    simpa using this
  have h2 : ContDiff ℝ 2 (Torus.lift g) := by
    have : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (Torus.lift g) := hg
    simpa using this
  unfold Torus.laplacian
  have e : Torus.lift (fun x => a * f x + c * g x) = a • Torus.lift f + c • Torus.lift g := by
    funext y; simp [Torus.lift]
  rw [e]
  have hA : ContDiffAt ℝ 2 (a • Torus.lift f) (Torus.rep x) := (h1.const_smul a).contDiffAt
  have hB : ContDiffAt ℝ 2 (c • Torus.lift g) (Torus.rep x) := (h2.const_smul c).contDiffAt
  rw [hA.laplacian_add hB, InnerProductSpace.laplacian_smul a h1.contDiffAt,
    InnerProductSpace.laplacian_smul c h2.contDiffAt]
  simp

theorem d1_grad_lincomb {f g : Torus n → ℝ} (hf : Torus.IsCk 2 f) (hg : Torus.IsCk 2 g)
    (a c : ℝ) (x : Torus n) :
    Torus.grad (fun x => a * f x + c * g x) x = a • Torus.grad f x + c • Torus.grad g x := by
  have h1 : ContDiff ℝ 2 (Torus.lift f) := by
    have : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (Torus.lift f) := hf
    simpa using this
  have h2 : ContDiff ℝ 2 (Torus.lift g) := by
    have : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (Torus.lift g) := hg
    simpa using this
  unfold Torus.grad
  have e : Torus.lift (fun x => a * f x + c * g x) = a • Torus.lift f + c • Torus.lift g := by
    funext y; simp [Torus.lift]
  rw [e]
  have d1 : DifferentiableAt ℝ (Torus.lift f) (Torus.rep x) :=
    (h1.differentiable (by norm_num)) _
  have d2 : DifferentiableAt ℝ (Torus.lift g) (Torus.rep x) :=
    (h2.differentiable (by norm_num)) _
  unfold gradient
  rw [fderiv_add (d1.const_smul a) (d2.const_smul c), fderiv_const_smul d1, fderiv_const_smul d2]
  simp

theorem d1_gen_lincomb {κ : ℝ} {b : Torus n → Euc n} {f g : Torus n → ℝ} (hf : Torus.IsCk 2 f)
    (hg : Torus.IsCk 2 g) (a c : ℝ) (x : Torus n) :
    d1_gen κ b (fun x => a * f x + c * g x) x = a * d1_gen κ b f x + c * d1_gen κ b g x := by
  unfold d1_gen
  rw [d1_laplacian_lincomb hf hg, d1_grad_lincomb hf hg, inner_add_right, inner_smul_right,
    inner_smul_right]
  ring

theorem d1_gen_const (κ : ℝ) (b : Torus n → Euc n) (c : ℝ) (x : Torus n) :
    d1_gen κ b (fun _ => c) x = 0 := by
  unfold d1_gen Torus.laplacian Torus.grad
  have e : Torus.lift (fun _ : Torus n => c) = fun _ => c := by funext y; simp [Torus.lift]
  rw [e]
  simp


theorem d1_contDiff_of_isCk2 {f : Torus n → ℝ} (hf : Torus.IsCk 2 f) {j : ℕ} (hj : j ≤ 2) :
    ContDiff ℝ j (Torus.lift f) := by
  have : ContDiff ℝ ((2 : ℕ) : WithTop ℕ∞) (Torus.lift f) := hf
  exact this.of_le (by exact_mod_cast hj)

theorem D1BackwardSolution.lincomb {κ : ℝ} {b : Torus n → Euc n} {t : ℝ} {φ₁ φ₂ : Torus n → ℝ}
    {f₁ f₂ : ℝ → Torus n → ℝ} (h₁ : D1BackwardSolution κ b t φ₁ f₁)
    (h₂ : D1BackwardSolution κ b t φ₂ f₂) (a c : ℝ) :
    D1BackwardSolution κ b t (fun x => a * φ₁ x + c * φ₂ x) (fun r x => a * f₁ r x + c * f₂ r x) where
  c2 r hr := d1_isCk2_lincomb (h₁.c2 r hr) (h₂.c2 r hr) a c
  cont_c2 j hj := by
    have hcont : Continuous fun p : Set.Icc (0 : ℝ) t × Euc n =>
        a • iteratedFDeriv ℝ j (Torus.lift (f₁ p.1)) p.2 + c • iteratedFDeriv ℝ j (Torus.lift (f₂ p.1)) p.2 :=
      ((h₁.cont_c2 j hj).const_smul a).add ((h₂.cont_c2 j hj).const_smul c)
    refine hcont.congr fun p => ?_
    have e : Torus.lift (fun x => a * f₁ p.1 x + c * f₂ p.1 x) =
        a • Torus.lift (f₁ p.1) + c • Torus.lift (f₂ p.1) := by
      funext y; simp [Torus.lift]
    have hA : ContDiffAt ℝ j (a • Torus.lift (f₁ p.1)) p.2 :=
      ((d1_contDiff_of_isCk2 (h₁.c2 p.1 p.1.2) hj).const_smul a).contDiffAt
    have hB : ContDiffAt ℝ j (c • Torus.lift (f₂ p.1)) p.2 :=
      ((d1_contDiff_of_isCk2 (h₂.c2 p.1 p.1.2) hj).const_smul c).contDiffAt
    rw [e, iteratedFDeriv_add_apply (f := a • Torus.lift (f₁ p.1)) (g := c • Torus.lift (f₂ p.1))
      hA hB,
      iteratedFDeriv_const_smul_apply (f := Torus.lift (f₁ p.1))
        (d1_contDiff_of_isCk2 (h₁.c2 p.1 p.1.2) hj).contDiffAt,
      iteratedFDeriv_const_smul_apply (f := Torus.lift (f₂ p.1))
        (d1_contDiff_of_isCk2 (h₂.c2 p.1 p.1.2) hj).contDiffAt]
  terminal := by funext x; simp [h₁.terminal, h₂.terminal]
  time_deriv x r hr := by
    have hr' : r ∈ Set.Icc 0 t := Set.Ioo_subset_Icc_self hr
    have := ((h₁.time_deriv x r hr).const_mul a).add ((h₂.time_deriv x r hr).const_mul c)
    convert this using 1
    rw [d1_gen_lincomb (h₁.c2 r hr') (h₂.c2 r hr')]
    ring
  cont_time_deriv := by
    have hcont : Continuous fun p : Set.Icc (0 : ℝ) t × Torus n =>
        a * d1_gen κ b (f₁ p.1) p.2 + c * d1_gen κ b (f₂ p.1) p.2 :=
      (continuous_const.mul h₁.cont_time_deriv).add (continuous_const.mul h₂.cont_time_deriv)
    refine hcont.congr fun p => ?_
    rw [d1_gen_lincomb (h₁.c2 p.1 p.1.2) (h₂.c2 p.1 p.1.2)]

theorem D1BackwardSolution.const (κ : ℝ) (b : Torus n → Euc n) (t c : ℝ) :
    D1BackwardSolution κ b t (fun _ => c) (fun _ _ => c) where
  c2 r hr := by
    unfold Torus.IsCk Torus.lift
    exact contDiff_const
  cont_c2 j hj := by
    have e : ∀ (p : Set.Icc (0 : ℝ) t × Euc n),
        iteratedFDeriv ℝ j (Torus.lift (fun _ : Torus n => c)) p.2 =
          iteratedFDeriv ℝ j (fun _ : Euc n => c) p.2 := fun p => rfl
    simp only [e]
    by_cases hj0 : j = 0
    · subst hj0
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
      exact continuous_const
    · simp only [iteratedFDeriv_const_of_ne hj0 c]
      exact continuous_const
  terminal := rfl
  time_deriv x r hr := by
    simpa [d1_gen_const] using hasDerivAt_const r c
  cont_time_deriv := by
    simpa [d1_gen_const] using (continuous_const : Continuous fun _ : Set.Icc (0 : ℝ) t × Torus n => (0 : ℝ))


/-- Sup-norm contraction between classical solutions (from the maximum principle). -/
theorem d1_backward_abs_le {κ : ℝ} (hκ : 0 < κ) {b : Torus n → Euc n} {t : ℝ} (ht : 0 < t)
    {φ₁ φ₂ : Torus n → ℝ} {f₁ f₂ : ℝ → Torus n → ℝ} (h₁ : D1BackwardSolution κ b t φ₁ f₁)
    (h₂ : D1BackwardSolution κ b t φ₂ f₂) {c : ℝ} (hc : ∀ x, |φ₁ x - φ₂ x| ≤ c) :
    ∀ r ∈ Set.Icc 0 t, ∀ x, |f₁ r x - f₂ r x| ≤ c := by
  have hd := h₁.lincomb h₂ 1 (-1)
  have hp := (D1BackwardSolution.const κ b t c).lincomb hd 1 1
  have hm := (D1BackwardSolution.const κ b t c).lincomb hd 1 (-1)
  have np := d1_backward_nonneg hκ ht hp (fun x => by
    have := abs_le.1 (hc x)
    linarith [this.1])
  have nm := d1_backward_nonneg hκ ht hm (fun x => by
    have := abs_le.1 (hc x)
    linarith [this.2])
  intro r hr x
  have a1 := np r hr x
  have a2 := nm r hr x
  rw [abs_le]
  constructor <;> linarith

/-- Uniqueness of classical backward solutions. -/
theorem d1_backward_unique {κ : ℝ} (hκ : 0 < κ) {b : Torus n → Euc n} {t : ℝ} (ht : 0 < t)
    {φ : Torus n → ℝ} {f₁ f₂ : ℝ → Torus n → ℝ} (h₁ : D1BackwardSolution κ b t φ f₁)
    (h₂ : D1BackwardSolution κ b t φ f₂) : ∀ r ∈ Set.Icc 0 t, ∀ x, f₁ r x = f₂ r x := by
  intro r hr x
  have := d1_backward_abs_le hκ ht h₁ h₂ (c := 0) (fun x => by simp) r hr x
  have h0 : |f₁ r x - f₂ r x| = 0 := le_antisymm this (abs_nonneg _)
  linarith [abs_eq_zero.1 h0]

/-- The time shift `[0, s] → [0, T]`, `r ↦ r + (T - s)`. -/
def d1_shiftIcc {T s : ℝ} (hsT : s ≤ T) (u : Set.Icc (0 : ℝ) s) : Set.Icc (0 : ℝ) T :=
  ⟨u.1 + (T - s), by linarith [u.2.1], by linarith [u.2.2]⟩

theorem d1_continuous_shiftIcc {T s : ℝ} (hsT : s ≤ T) : Continuous (d1_shiftIcc hsT) :=
  Continuous.subtype_mk ((continuous_subtype_val).add continuous_const) _

/-- Time shift: the restriction of a solution on `[0, T]` to `[T - s, T]`, re-based at `0`. -/
theorem D1BackwardSolution.shift {κ : ℝ} {b : Torus n → Euc n} {T s : ℝ} (hs : 0 < s) (hsT : s ≤ T)
    {φ : Torus n → ℝ} {f : ℝ → Torus n → ℝ} (h : D1BackwardSolution κ b T φ f) :
    D1BackwardSolution κ b s φ (fun r => f (r + (T - s))) where
  c2 r hr := h.c2 (r + (T - s)) ⟨by linarith [hr.1], by linarith [hr.2]⟩
  cont_c2 j hj := by
    have h1 := (h.cont_c2 j hj).comp ((d1_continuous_shiftIcc hsT).prodMap continuous_id)
    refine h1.congr fun p => ?_
    rfl
  terminal := by
    show f (s + (T - s)) = φ
    rw [show s + (T - s) = T by ring]
    exact h.terminal
  time_deriv x r hr := by
    have h1 := h.time_deriv x (r + (T - s)) ⟨by linarith [hr.1], by linarith [hr.2]⟩
    show HasDerivAt (fun r' => f (r' + (T - s)) x) (-(d1_gen κ b (f (r + (T - s))) x)) r
    exact HasDerivAt.comp_add_const r (T - s) (f := fun r' => f r' x) h1
  cont_time_deriv := by
    have h1 := h.cont_time_deriv.comp ((d1_continuous_shiftIcc hsT).prodMap continuous_id)
    refine h1.congr fun p => ?_
    rfl

end HRS
