import Mathlib

/-!
# S8.2 P06a infrastructure: symmetry of the iterated Frechet derivative of a `C^n` map
(Mathlib has it only for analytic maps.)  `r26t8a_iter_symm`: `D^n f x (m ∘ σ) = D^n f x m` for every permutation `σ` of the slots.
Induction on `n` through the right recursion `D^(n+1) f = D^n (fderiv f)(init _)(last _)`; adjacent transpositions away from the last
slot use the induction hypothesis for `fderiv f`; the last transposition uses symmetry of the second derivative at nearby points.
-/

set_option autoImplicit false
noncomputable section
open Equiv Fin Filter

namespace HRS.MS.R26T8A

theorem r26t8a_iter_symm_K (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n' : ℕ) (f : E → F) (x : E) (hf : ContDiffAt ℝ ((n' + 2 : ℕ) : WithTop ℕ∞) f x) (M0 : Fin n' → E) (a b : E) :
    iteratedFDeriv ℝ n' (fun y => fderiv ℝ (fun y => fderiv ℝ f y) y) x M0 a b =
    iteratedFDeriv ℝ n' (fun y => fderiv ℝ (fun y => fderiv ℝ f y) y) x M0 b a := by
  have hn0 : ∀ n : ℕ, ((n : ℕ) : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun n => by
    exact_mod_cast ENat.natCast_ne_top n
  set K : E → (E →L[ℝ] E →L[ℝ] F) := fun y => fderiv ℝ (fun y => fderiv ℝ f y) y with hK
  let g : (E →L[ℝ] E →L[ℝ] F) ≃L[ℝ] (E →L[ℝ] E →L[ℝ] F) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E F).toContinuousLinearEquiv
  have hg : ∀ T v w, g T v w = T w v := fun T v w => rfl
  have hev : K =ᶠ[nhds x] g ∘ K := by
    filter_upwards [hf.eventually (hn0 (n' + 2))] with y hy
    have hs := hy.isSymmSndFDerivAt (by simp)
    ext v w
    simp only [hK, Function.comp, hg]
    exact hs v w
  have h3 := (hev.iteratedFDeriv ℝ n').self_of_nhds
  have h4 := ContinuousLinearEquiv.iteratedFDeriv_comp_left (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] F)
    (G := E →L[ℝ] E →L[ℝ] F) (f := K) (x := x) g (i := n')
  exact congrArg (fun T => T M0 a b) (h3.trans h4)

theorem r26t8a_iter_symm_last (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n' : ℕ) (f : E → F) (x : E) (hf : ContDiffAt ℝ ((n' + 2 : ℕ) : WithTop ℕ∞) f x) (m : Fin (n' + 2) → E) :
    iteratedFDeriv ℝ (n' + 2) f x (m ∘ swap (Fin.last n').castSucc (Fin.last n').succ) =
      iteratedFDeriv ℝ (n' + 2) f x m := by
  rw [iteratedFDeriv_succ_apply_right (m := m ∘ swap (Fin.last n').castSucc (Fin.last n').succ),
    iteratedFDeriv_succ_apply_right (m := m)]
  rw [iteratedFDeriv_succ_apply_right (f := fun y => fderiv ℝ f y)
      (m := Fin.init (m ∘ swap (Fin.last n').castSucc (Fin.last n').succ)),
    iteratedFDeriv_succ_apply_right (f := fun y => fderiv ℝ f y) (m := Fin.init m)]
  have e1 : (m ∘ swap (Fin.last n').castSucc (Fin.last n').succ) (Fin.last (n' + 1)) =
      m (Fin.last n').castSucc := by
    simp only [Function.comp, Fin.succ_last]
    rw [swap_apply_right]
  have e2 : Fin.init (m ∘ swap (Fin.last n').castSucc (Fin.last n').succ) (Fin.last n') =
      m (Fin.last (n' + 1)) := by
    simp only [Fin.init, Function.comp, Fin.succ_last]
    rw [swap_apply_left]
  have e3 : Fin.init (Fin.init (m ∘ swap (Fin.last n').castSucc (Fin.last n').succ)) =
      Fin.init (Fin.init m) := by
    funext j
    simp only [Fin.init, Function.comp]
    rw [swap_apply_of_ne_of_ne]
    · intro h; have := congrArg Fin.val h; have := j.isLt; simp at *
    · intro h; have := congrArg Fin.val h; have := j.isLt; simp [Fin.succ_last] at *
  rw [e1, e2, e3]
  exact r26t8a_iter_symm_K E n' f x hf (Fin.init (Fin.init m)) (m (Fin.last (n' + 1))) (m (Fin.last n').castSucc)

theorem r26t8a_iter_symm_mid (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n' : ℕ) (f : E → F) (x : E)
    (ih : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (f : E → F) (x : E), ContDiffAt ℝ ((n' + 1 : ℕ) : WithTop ℕ∞) f x → ∀ (σ : Perm (Fin (n' + 1)))
      (m : Fin (n' + 1) → E), iteratedFDeriv ℝ (n' + 1) f x (m ∘ σ) = iteratedFDeriv ℝ (n' + 1) f x m)
    (hg : ContDiffAt ℝ ((n' + 1 : ℕ) : WithTop ℕ∞) (fderiv ℝ f) x)
    (i : Fin (n' + 1)) (hi : i.val < n') (m : Fin (n' + 2) → E) :
    iteratedFDeriv ℝ (n' + 2) f x (m ∘ swap i.castSucc i.succ) = iteratedFDeriv ℝ (n' + 2) f x m := by
  rw [iteratedFDeriv_succ_apply_right (m := m ∘ swap i.castSucc i.succ),
    iteratedFDeriv_succ_apply_right (m := m)]
  have hl : (m ∘ swap i.castSucc i.succ) (Fin.last (n' + 1)) = m (Fin.last (n' + 1)) := by
    simp only [Function.comp]
    rw [swap_apply_of_ne_of_ne]
    · intro h; have := congrArg Fin.val h; simp at this; omega
    · intro h; have := congrArg Fin.val h; simp at this; omega
  rw [hl]
  have e1 : (⟨i.val + 1, by omega⟩ : Fin (n' + 1)).castSucc = i.succ := by ext; simp
  have hτ : Fin.init (m ∘ swap i.castSucc i.succ) =
      Fin.init m ∘ swap i (⟨i.val + 1, by omega⟩ : Fin (n' + 1)) := by
    funext j
    simp only [Fin.init, Function.comp]
    congr 1
    by_cases h1 : j = i
    · subst h1
      rw [swap_apply_left, swap_apply_left, e1]
    · by_cases h2 : j = (⟨i.val + 1, by omega⟩ : Fin (n' + 1))
      · subst h2
        rw [swap_apply_right, e1, swap_apply_right]
      · rw [swap_apply_of_ne_of_ne, swap_apply_of_ne_of_ne h1 h2]
        · intro h; apply h1; ext; have := congrArg Fin.val h; simpa using this
        · intro h; apply h2; ext; have := congrArg Fin.val h; simpa using this
  rw [hτ]
  have := ih (fderiv ℝ f) x hg (swap i (⟨i.val + 1, by omega⟩ : Fin (n' + 1))) (Fin.init m)
  rw [this]

theorem r26t8a_iter_symm (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] : ∀ (n : ℕ) {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (x : E), ContDiffAt ℝ (n : WithTop ℕ∞) f x →
    ∀ (σ : Perm (Fin n)) (m : Fin n → E), iteratedFDeriv ℝ n f x (m ∘ σ) = iteratedFDeriv ℝ n f x m := by
  intro n
  induction n with
  | zero =>
    intro F _ _ f x _ σ m
    have : m ∘ σ = m := funext fun i => i.elim0
    rw [this]
  | succ n ih =>
    intro F _ _ f x hf σ m
    have hg : ContDiffAt ℝ (n : WithTop ℕ∞) (fderiv ℝ f) x :=
      hf.fderiv_right (m := n) (by push_cast; exact le_rfl)
    have hsub := Equiv.Perm.mclosure_swap_castSucc_succ n
    have key : ∀ σ : Perm (Fin (n + 1)),
        σ ∈ Submonoid.closure (Set.range fun i : Fin n => swap i.castSucc i.succ) →
        ∀ m : Fin (n + 1) → E, iteratedFDeriv ℝ (n + 1) f x (m ∘ σ) = iteratedFDeriv ℝ (n + 1) f x m := by
      intro σ hσ
      induction hσ using Submonoid.closure_induction with
      | mem x' hx' =>
        obtain ⟨i, rfl⟩ := hx'
        intro m
        cases n with
        | zero => exact i.elim0
        | succ n' =>
          by_cases hi : i.val < n'
          · exact r26t8a_iter_symm_mid E n' f x ih hg i hi m
          · have hi' : i = Fin.last n' := Fin.ext (by have := i.isLt; simp; omega)
            subst hi'
            exact r26t8a_iter_symm_last E n' f x hf m
      | one => intro m; rfl
      | mul a b _ _ ha hb =>
        intro m
        rw [show m ∘ ⇑(a * b) = (m ∘ a) ∘ b from rfl, hb, ha]
    exact key σ (by rw [hsub]; trivial) m

end HRS.MS.R26T8A
