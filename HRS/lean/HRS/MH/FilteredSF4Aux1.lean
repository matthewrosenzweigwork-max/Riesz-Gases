import HRS.Main.GFB3Aux1
import HRS.MH.FilteredSF2
import HRS.MH.FilteredSF3

/-!
# Packet SF4, helper 1: basis vectors, dyadic shells, and the shell block bound

Exponent bookkeeping (`a = γ - 1 - n > d/2`, `t = d/2 + a > d`, `x = t - 2a = d/2 - a < 0`):
shell `s` holds the `k` with `2^s ≤ ⟨k⟩ < 2^{s+1}`, so `#S_s ≤ C 2^{(s+1) t}` (SF2).  For `i ≤ n` the scalar
derivative bound is `√2 ⟨k⟩^{-γ+i+1} ≤ √2 ⟨k⟩^{-a} ≤ √2 (2^s)^{-a}`.  Pythagoras (SF3) gives
`‖D^i G_s‖^2 ≤ #S_s · 2 · 2^{-2 a s} ≤ 2 C 2^t (2^{t-2a})^s`, and `2^{t-2a} = 2^x < 1`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators

namespace HRS.MH.FilteredP

open HRS HRS.Uniform HRS.Uniform.Q54c HRS.GF

variable {d : ℕ}

/-- The basis vector `e_k = lp.single k 1` of `NegSobolev d γ`. -/
def sf4_e (γ : ℝ) (k : NonzeroLattice d) : NegSobolev d γ :=
  ((lp.single 2 k (1 : ℝ) : lp (fun _ : NonzeroLattice d => ℝ) 2) : NegSobolev d γ)

lemma sf4_e_orthonormal (γ : ℝ) : Orthonormal ℝ (sf4_e (d := d) γ) := by
  classical
  rw [orthonormal_iff_ite]
  intro k l
  show inner ℝ (lp.single 2 k (1 : ℝ) : lp (fun _ : NonzeroLattice d => ℝ) 2)
    (lp.single 2 l (1 : ℝ)) = _
  rw [lp.inner_single_left]
  by_cases h : k = l
  · subst h; simp
  · simp [h, lp.single_apply]

/-- The scalar coefficient of the `k`-th term. -/
def sf4_g (γ : ℝ) (j : Fin d) (k : NonzeroLattice d) (y : Euc d) : ℝ :=
  Lattice.jp k.1 ^ (-γ) * Dmode k j y

lemma sf4_term_eq (γ : ℝ) (j : Fin d) (k : NonzeroLattice d) :
    gfb3_term γ j k = fun y => sf4_g γ j k y • sf4_e γ k := rfl

lemma sf4_g_eq (γ : ℝ) (j : Fin d) (k : NonzeroLattice d) :
    sf4_g γ j k = (innerSL ℝ (sf4_e γ k)) ∘ gfb3_term γ j k := by
  funext y
  have h1 : ‖sf4_e γ k‖ = 1 := by
    show ‖(lp.single 2 k (1 : ℝ) : lp (fun _ : NonzeroLattice d => ℝ) 2)‖ = 1
    rw [lp.norm_single (by norm_num)]; simp
  rw [sf4_term_eq]
  simp only [Function.comp, innerSL_apply_apply, inner_smul_right, real_inner_self_eq_norm_sq, h1]
  simp

lemma sf4_norm_iter_g (γ : ℝ) (j : Fin d) (k : NonzeroLattice d) (i : ℕ) (y : Euc d) :
    ‖iteratedFDeriv ℝ i (sf4_g γ j k) y‖ ≤
      Real.sqrt 2 * Lattice.jp k.1 ^ (-γ) * Lattice.jp k.1 ^ (i + 1) := by
  have h1 : ‖sf4_e γ k‖ = 1 := by
    show ‖(lp.single 2 k (1 : ℝ) : lp (fun _ : NonzeroLattice d => ℝ) 2)‖ = 1
    rw [lp.norm_single (by norm_num)]; simp
  rw [sf4_g_eq]
  have hL := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (innerSL ℝ (sf4_e γ k))
    ((gfb3_contDiff_term γ j k ⊤).contDiffAt (x := y)) (n := i) (by exact_mod_cast le_top)
  refine hL.trans ?_
  rw [innerSL_apply_norm, h1, one_mul]
  exact gfb3_norm_iter_term γ j k i y

/-- The dyadic shell index of `k`. -/
def sf4_shell (k : NonzeroLattice d) : ℕ := ⌊Real.logb 2 (Lattice.jp k.1)⌋₊

lemma sf4_shell_bounds (k : NonzeroLattice d) :
    (2 : ℝ) ^ (sf4_shell k) ≤ Lattice.jp k.1 ∧ Lattice.jp k.1 < (2 : ℝ) ^ (sf4_shell k + 1) := by
  have hj : 1 ≤ Lattice.jp k.1 := Torus.jp_ge_one k.1
  have hj0 : 0 < Lattice.jp k.1 := lt_of_lt_of_le one_pos hj
  have hL : 0 ≤ Real.logb 2 (Lattice.jp k.1) := Real.logb_nonneg (by norm_num) hj
  constructor
  · have h := Nat.floor_le hL
    have := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hj0).mp h
    rw [Real.rpow_natCast] at this
    exact this
  · have h := Nat.lt_floor_add_one (Real.logb 2 (Lattice.jp k.1))
    have := (Real.logb_lt_iff_lt_rpow (by norm_num : (1 : ℝ) < 2) hj0).mp h
    have e : ((2 : ℝ) ^ ((⌊Real.logb 2 (Lattice.jp k.1)⌋₊ : ℝ) + 1)) = (2 : ℝ) ^ (sf4_shell k + 1) := by
      rw [← Real.rpow_natCast]; push_cast; rfl
    rw [e] at this
    exact this

lemma sf4_shell_finite {t : ℝ} {C : ℝ}
    (hC : ∀ R : ℝ, 0 < R → {k : NonzeroLattice d | Lattice.jp k.1 ≤ R}.Finite ∧
        (({k : NonzeroLattice d | Lattice.jp k.1 ≤ R}).ncard : ℝ) ≤ C * R ^ t) (s : ℕ) :
    {k : NonzeroLattice d | sf4_shell k = s}.Finite ∧
      (({k : NonzeroLattice d | sf4_shell k = s}).ncard : ℝ) ≤ C * ((2 : ℝ) ^ (s + 1)) ^ t := by
  have hR : (0 : ℝ) < (2 : ℝ) ^ (s + 1) := by positivity
  obtain ⟨hf, hc⟩ := hC _ hR
  have hsub : {k : NonzeroLattice d | sf4_shell k = s} ⊆ {k : NonzeroLattice d | Lattice.jp k.1 ≤ (2 : ℝ) ^ (s + 1)} := by
    intro k hk
    have h := (sf4_shell_bounds k).2
    simp only [Set.mem_ofPred_eq] at hk ⊢
    rw [hk] at h
    exact h.le
  refine ⟨hf.subset hsub, ?_⟩
  have h1 : (({k : NonzeroLattice d | sf4_shell k = s}).ncard : ℝ) ≤
      (({k : NonzeroLattice d | Lattice.jp k.1 ≤ (2 : ℝ) ^ (s + 1)}).ncard : ℝ) := by
    exact_mod_cast Set.ncard_le_ncard hsub hf
  exact h1.trans hc

end HRS.MH.FilteredP
