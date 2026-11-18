import HRS.MS.UniqFAux2

/-!
# UNIQ-F, part 3: uniqueness of classical adjoint solutions of `fixedEqCoeff`, viscosity `ν > 0`

`uniqf_unique_pos`: `ν > 0`, ANY matrices `M, Q`, time-dependent bounded `c_r` and good slices `ρ_r`
(uniform constants), `0 ≤ s < d`: two `IsClassicalAdjointW` solutions of `fixedEqCoeff s M Q ν c ρ` with the same terminal datum agree on `[0,t]`.
The difference `u = f₁ - f₂` is a `UqSol` with source `S = ⟨c_r,∇u⟩ - ulNL s M ρ_r (∇u)` (the generator of `fixedEqCoeff` at time `r`
is that of `fixedViscosityCoeff s M Q ν (c r) (ρ r)`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff RealInnerProductSpace Matrix MatrixOrder

namespace HRS.MS.UniqF

open HRS HRS.Whole HRS.MS.Ul HRS.MS.Lc HRS.MS.UniqQ HRS.MS.S52B

variable {d : ℕ}

theorem uniqf_gen_eq (s : ℝ) (M Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (c : ℝ → Euc d → Euc d) (ρ : ℝ → Euc d → ℝ)
    (r : ℝ) (φ : Euc d → ℝ) (x : Euc d) :
    generatorW (fixedEqCoeff s M Q ν c ρ) r φ x = ul5A Q ν φ x + ulPert s M (ρ r) (c r) φ x :=
  ul5_gen_fixed s M Q ν (c r) (ρ r) r φ x

theorem uniqf_grad_bound {f : Euc d → ℝ} {B : ℝ} (hB : ∀ y, ‖iteratedFDeriv ℝ 1 f y‖ ≤ B) (y : Euc d) :
    ‖gradient f y‖ ≤ B := by
  rw [uniqq_grad_norm, ← norm_iteratedFDeriv_one]; exact hB y

/-- **uniqueness of classical adjoint solutions for `fixedEqCoeff`, `ν > 0`** -/
theorem uniqf_unique_pos {s ν : ℝ} (hν : 0 < ν) (hs0 : 0 ≤ s) (hsd : s < d)
    (M Q : Matrix (Fin d) (Fin d) ℝ) {ρ : ℝ → Euc d → ℝ} {B L I : ℝ} {c : ℝ → Euc d → Euc d} {Λ : ℝ} {t : ℝ}
    (ht : 0 ≤ t) (hρ : ∀ r ∈ Icc (0 : ℝ) t, UqfGood (ρ r) B L I)
    (hΛ : ∀ r ∈ Icc (0 : ℝ) t, ∀ x, ‖c r x‖ ≤ Λ) {φ : Euc d → ℝ} {f1 f2 : ℝ → Euc d → ℝ}
    (h1 : IsClassicalAdjointW (fixedEqCoeff s M Q ν c ρ) t φ f1)
    (h2 : IsClassicalAdjointW (fixedEqCoeff s M Q ν c ρ) t φ f2) :
    ∀ r ∈ Icc (0 : ℝ) t, f1 r = f2 r := by
  set u : ℝ → Euc d → ℝ := fun r x => f1 r x - f2 r x with hu
  set S : ℝ → Euc d → ℝ := fun r x =>
    inner ℝ (c r x) (gradient (u r) x) - ulNL s M (ρ r) (u r) x with hS
  have hsol : UqSol Q ν t u S := by
    refine ⟨fun r hr => (h1.c2 r hr).sub (h2.c2 r hr), ?_, ?_, ?_⟩
    · have key : ∀ j, j ≤ 2 → ∃ B : ℝ, ∀ r ∈ Icc (0 : ℝ) t, ∀ x, ‖iteratedFDeriv ℝ j (u r) x‖ ≤ B := by
        intro j hj
        obtain ⟨B1, hB1⟩ := h1.bdd j hj
        obtain ⟨B2, hB2⟩ := h2.bdd j hj
        refine ⟨B1 + B2, fun r hr x => ?_⟩
        have e : iteratedFDeriv ℝ j (fun y => f1 r y - f2 r y) x =
            iteratedFDeriv ℝ j (f1 r) x - iteratedFDeriv ℝ j (f2 r) x :=
          iteratedFDeriv_sub_apply ((h1.c2 r hr).of_le (by exact_mod_cast hj)).contDiffAt
            ((h2.c2 r hr).of_le (by exact_mod_cast hj)).contDiffAt
        simp only [hu]
        rw [e]
        exact (norm_sub_le _ _).trans (add_le_add (hB1 r hr x) (hB2 r hr x))
      obtain ⟨B0, hB0⟩ := key 0 (by norm_num)
      obtain ⟨B1, hB1⟩ := key 1 (by norm_num)
      obtain ⟨B2, hB2⟩ := key 2 (by norm_num)
      refine ⟨max (max B0 B1) B2, fun j hj r hr x => ?_⟩
      interval_cases j
      · exact (hB0 r hr x).trans ((le_max_left _ _).trans (le_max_left _ _))
      · exact (hB1 r hr x).trans ((le_max_right _ _).trans (le_max_left _ _))
      · exact (hB2 r hr x).trans (le_max_right _ _)
    · exact (uniqq_cont_val h1).sub (uniqq_cont_val h2)
    · intro x r hr
      have hrI : r ∈ Icc (0 : ℝ) t := ⟨hr.1.le, hr.2.le⟩
      have hd := (h1.time_deriv x r hr).sub (h2.time_deriv x r hr)
      refine hd.congr_deriv ?_
      have g1 := uniqf_gen_eq s M Q ν c ρ r (f1 r) x
      have g2 := uniqf_gen_eq s M Q ν c ρ r (f2 r) x
      have hl := uqL0_sub Q ν (h1.c2 r hrI) (h2.c2 r hrI) x
      have hg := lu_grad_sub ((h1.c2 r hrI).differentiable (by norm_num))
        ((h2.c2 r hrI).differentiable (by norm_num)) x
      obtain ⟨G1, hG1⟩ := h1.bdd 1 (by norm_num)
      obtain ⟨G2, hG2⟩ := h2.bdd 1 (by norm_num)
      have hn := uniqf_nl_sub hs0 hsd M (hρ r hrI) (h1.c2 r hrI) (h2.c2 r hrI)
        (G := max G1 G2) (fun y => (uniqf_grad_bound (fun z => hG1 r hrI z) y).trans (le_max_left _ _))
        (fun y => (uniqf_grad_bound (fun z => hG2 r hrI z) y).trans (le_max_right _ _)) x
      have hS' : S r x = inner ℝ (c r x) (gradient (f1 r) x) - inner ℝ (c r x) (gradient (f2 r) x) -
          (ulNL s M (ρ r) (f1 r) x - ulNL s M (ρ r) (f2 r) x) := by
        simp only [hS, hu]
        rw [hg, inner_sub_right, hn]
      have e2 : uqL0 Q ν (u r) x = uqL0 Q ν (f1 r) x - uqL0 Q ν (f2 r) x := hl
      unfold ulPert ul5A at g1 g2
      show -generatorW (fixedEqCoeff s M Q ν c ρ) r (f1 r) x -
        -generatorW (fixedEqCoeff s M Q ν c ρ) r (f2 r) x = -(uqL0 Q ν (u r) x + S r x)
      rw [e2, hS', g1, g2]
      simp only [uqL0]
      ring
  have hz : ∀ y, u t y = 0 := fun y => by
    simp only [hu, h1.terminal, h2.terminal, sub_self]
  have := uniqf_zero hν hs0 hsd M hρ hΛ ht hsol (fun r hr x => rfl) hz
  intro r hr
  funext y
  have := this r hr y
  simp only [hu] at this
  linarith

end HRS.MS.UniqF
