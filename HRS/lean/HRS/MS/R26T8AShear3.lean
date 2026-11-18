import HRS.MS.R26T8AShear2

/-!
# S8.2 shear calculus (3): the shear bound
-/

set_option autoImplicit false
noncomputable section

namespace HRS.MS.R26T8A

section Shear3

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem r26t8a_sh_pascal (q p : ℕ) (l : ℝ) (B : ℕ → ℕ → ℝ) :
    ∑ t ∈ Finset.range (q + 2), ((q + 1).choose t : ℝ) * |l| ^ t * B (p + t) (q + 1 - t) =
      ∑ t ∈ Finset.range (q + 1), (q.choose t : ℝ) * |l| ^ t * B (p + t) (q - t + 1) +
        |l| * ∑ t ∈ Finset.range (q + 1), (q.choose t : ℝ) * |l| ^ t * B (p + t + 1) (q - t) := by
  have h := Finset.sum_choose_succ_mul (fun i j => |l| ^ i * B (p + i) j) q
  have e1 : ∑ t ∈ Finset.range (q + 2), ((q + 1).choose t : ℝ) * |l| ^ t * B (p + t) (q + 1 - t) =
      ∑ i ∈ Finset.range (q + 2), ((q + 1).choose i : ℝ) * (|l| ^ i * B (p + i) (q + 1 - i)) :=
    Finset.sum_congr rfl fun t _ => by ring
  rw [e1, h]
  congr 1
  · refine Finset.sum_congr rfl fun t ht => ?_
    have : q - t + 1 = q + 1 - t := by have := Finset.mem_range.1 ht; omega
    rw [this]; ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [pow_succ]; ring

theorem r26t8a_sh_bound (l : ℝ) : ∀ (q p : ℕ) (Ψ : E × E → ℝ),
    ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) Ψ → ∀ (x : E × E) (B : ℕ → ℕ → ℝ),
    (∀ a b : ℕ, a + b ≤ p + q → ∀ (y : Fin a → E) (w : Fin b → E),
      |r26t8a_sh_N a b y w Ψ (r26t8a_sh_S l x)| ≤ B a b * (∏ i, ‖y i‖) * ∏ j, ‖w j‖) →
    ∀ (y : Fin p → E) (w : Fin q → E),
      |r26t8a_sh_N p q y w (fun z => Ψ (r26t8a_sh_S l z)) x| ≤
        (∑ t ∈ Finset.range (q + 1), (q.choose t : ℝ) * |l| ^ t * B (p + t) (q - t)) *
          (∏ i, ‖y i‖) * ∏ j, ‖w j‖ := by
  intro q
  induction q with
  | zero =>
    intro p Ψ hΨ x B hB y w
    have h1 := r26t8a_sh_Ny_S l p y Ψ (by simpa using hΨ)
    have := hB p 0 (by omega) y w
    show |r26t8a_sh_Ny p y (fun z => Ψ (r26t8a_sh_S l z)) x| ≤ _
    rw [h1]
    have h2 : r26t8a_sh_N p 0 y w Ψ (r26t8a_sh_S l x) = r26t8a_sh_Ny p y Ψ (r26t8a_sh_S l x) := rfl
    rw [h2] at this
    simpa using this
  | succ q ih =>
    intro p Ψ hΨ x B hB y w
    set wl : E := w (Fin.last q) with hwl
    set w' : Fin q → E := Fin.init w with hw'
    have hd : Differentiable ℝ Ψ := hΨ.differentiable (Nat.cast_ne_zero.2 (by omega))
    have h1 : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (r26t8a_sh_DW wl Ψ) :=
      r26t8a_sh_contDiff_DW wl (n := p + q) hΨ
    have h2 : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (r26t8a_sh_DY wl Ψ) :=
      r26t8a_sh_contDiff_DY wl (n := p + q) hΨ
    have hS : ContDiff ℝ ⊤ (r26t8a_sh_S (E := E) l) := ContinuousLinearMap.contDiff (𝕜 := ℝ) (r26t8a_sh_S (E := E) l)
    have hc1 : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun z => r26t8a_sh_DW wl Ψ (r26t8a_sh_S l z)) :=
      h1.comp (hS.of_le le_top)
    have hc2 : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun z => r26t8a_sh_DY wl Ψ (r26t8a_sh_S l z)) :=
      h2.comp (hS.of_le le_top)
    have hshear := r26t8a_sh_DW_S l wl hd
    have hN : r26t8a_sh_N p (q + 1) y w (fun z => Ψ (r26t8a_sh_S l z)) x =
        r26t8a_sh_N p q y w' (fun z => r26t8a_sh_DW wl Ψ (r26t8a_sh_S l z)) x +
          l * r26t8a_sh_N p q y w' (fun z => r26t8a_sh_DY wl Ψ (r26t8a_sh_S l z)) x := by
      show r26t8a_sh_N p q y w' (r26t8a_sh_DW wl (fun z => Ψ (r26t8a_sh_S l z))) x = _
      rw [hshear]
      exact r26t8a_sh_N_lin l p q y w' hc1 hc2 x
    -- products
    have hprod : ∀ (u : Fin (q + 1) → E), ∏ j, ‖u j‖ = (∏ j : Fin q, ‖Fin.init u j‖) * ‖u (Fin.last q)‖ := by
      intro u; rw [Fin.prod_univ_castSucc]; rfl
    have hprodsn : ∀ (m : ℕ) (u : Fin m → E) (e : E),
        ∏ j, ‖(Fin.snoc u e : Fin (m + 1) → E) j‖ = (∏ j, ‖u j‖) * ‖e‖ := by
      intro m u e
      rw [Fin.prod_univ_castSucc]
      simp [Fin.snoc_castSucc, Fin.snoc_last]
    -- hypotheses for the two derived functions
    have hyp1 : ∀ a b : ℕ, a + b ≤ p + q → ∀ (y' : Fin a → E) (w'' : Fin b → E),
        |r26t8a_sh_N a b y' w'' (r26t8a_sh_DW wl Ψ) (r26t8a_sh_S l x)| ≤
          (B a (b + 1) * ‖wl‖) * (∏ i, ‖y' i‖) * ∏ j, ‖w'' j‖ := by
      intro a b hab y' w''
      have e : r26t8a_sh_N a b y' w'' (r26t8a_sh_DW wl Ψ) =
          r26t8a_sh_N a (b + 1) y' (Fin.snoc w'' wl) Ψ := by
        unfold r26t8a_sh_N
        rw [r26t8a_sh_Nw_snoc]
      rw [e]
      have := hB a (b + 1) (by omega) y' (Fin.snoc w'' wl)
      rw [hprodsn] at this
      linarith
    have hyp2 : ∀ a b : ℕ, a + b ≤ p + q → ∀ (y' : Fin a → E) (w'' : Fin b → E),
        |r26t8a_sh_N a b y' w'' (r26t8a_sh_DY wl Ψ) (r26t8a_sh_S l x)| ≤
          (B (a + 1) b * ‖wl‖) * (∏ i, ‖y' i‖) * ∏ j, ‖w'' j‖ := by
      intro a b hab y' w''
      have hsm : ContDiff ℝ ((b + 1 : ℕ) : WithTop ℕ∞) Ψ :=
        hΨ.of_le (by exact_mod_cast (by omega : b + 1 ≤ p + (q + 1)))
      have e : r26t8a_sh_N a b y' w'' (r26t8a_sh_DY wl Ψ) =
          r26t8a_sh_N (a + 1) b (Fin.snoc y' wl) w'' Ψ := by
        unfold r26t8a_sh_N
        rw [r26t8a_sh_Nw_DY b w'' wl Ψ hsm, r26t8a_sh_Ny_snoc]
      rw [e]
      have := hB (a + 1) b (by omega) (Fin.snoc y' wl) w''
      rw [hprodsn] at this
      linarith
    have I1 := ih p (r26t8a_sh_DW wl Ψ) h1 x (fun a b => B a (b + 1) * ‖wl‖) hyp1 y w'
    have I2 := ih p (r26t8a_sh_DY wl Ψ) h2 x (fun a b => B (a + 1) b * ‖wl‖) hyp2 y w'
    rw [hN, hprod w]
    have hw'wl : ‖w (Fin.last q)‖ = ‖wl‖ := rfl
    -- combine
    have hP : 0 ≤ (∏ i, ‖y i‖) * ∏ j, ‖w' j‖ :=
      mul_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    have hpas := r26t8a_sh_pascal q p l B
    calc |r26t8a_sh_N p q y w' (fun z => r26t8a_sh_DW wl Ψ (r26t8a_sh_S l z)) x +
          l * r26t8a_sh_N p q y w' (fun z => r26t8a_sh_DY wl Ψ (r26t8a_sh_S l z)) x|
        ≤ |r26t8a_sh_N p q y w' (fun z => r26t8a_sh_DW wl Ψ (r26t8a_sh_S l z)) x| +
          |l| * |r26t8a_sh_N p q y w' (fun z => r26t8a_sh_DY wl Ψ (r26t8a_sh_S l z)) x| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ (∑ t ∈ Finset.range (q + 1), (q.choose t : ℝ) * |l| ^ t * (B (p + t) (q - t + 1) * ‖wl‖)) *
            (∏ i, ‖y i‖) * (∏ j, ‖w' j‖) +
          |l| * ((∑ t ∈ Finset.range (q + 1), (q.choose t : ℝ) * |l| ^ t * (B (p + t + 1) (q - t) * ‖wl‖)) *
            (∏ i, ‖y i‖) * (∏ j, ‖w' j‖)) :=
          add_le_add I1 (mul_le_mul_of_nonneg_left I2 (abs_nonneg l))
      _ = (∑ t ∈ Finset.range (q + 1 + 1), ((q + 1).choose t : ℝ) * |l| ^ t * B (p + t) (q + 1 - t)) *
            (∏ i, ‖y i‖) * ((∏ j, ‖w' j‖) * ‖wl‖) := by
          have e1 : ∑ t ∈ Finset.range (q + 1), (q.choose t : ℝ) * |l| ^ t * (B (p + t) (q - t + 1) * ‖wl‖) =
              (∑ t ∈ Finset.range (q + 1), (q.choose t : ℝ) * |l| ^ t * B (p + t) (q - t + 1)) * ‖wl‖ := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun t _ => by ring
          have e2 : ∑ t ∈ Finset.range (q + 1), (q.choose t : ℝ) * |l| ^ t * (B (p + t + 1) (q - t) * ‖wl‖) =
              (∑ t ∈ Finset.range (q + 1), (q.choose t : ℝ) * |l| ^ t * B (p + t + 1) (q - t)) * ‖wl‖ := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun t _ => by ring
          rw [e1, e2, show q + 1 + 1 = q + 2 from rfl, hpas]
          ring

end Shear3

end HRS.MS.R26T8A
