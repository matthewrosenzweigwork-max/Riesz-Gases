import HRS.MS.S104eFinal
import HRS.MS.S21F_D00
import HRS.MS.R2WinOrbTRD7
import HRS.MS.WadAux62

/-!
# S2.1(iii): classical adjoints on finite Hermite combinations

`S104eHex` supplies every Hermite basis datum along a resulting trajectory.  The
Volterra input in `S104eC5C` is still only constructed for those basis data.
This file extends existence and the chosen propagator's linearity to finite
Hermite combinations, using the existing S10.3 superposition and S10.4
uniqueness results.  No density/limit passage to all of `IsOscTest` is asserted.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R2WinOrbNL

private theorem fp81s21_density_u2dec
    (p : HRS.MS.R26T3.Parameters) {δ : ℝ}
    (R : HRS.MS.R26T3.Trajectory p δ) {t : ℝ} (_ht : 0 ≤ t) :
    ∃ A : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) t,
      U2Dec 1 ((p.d + 1 : ℕ) : ℝ) A (R.ρ τ) := by
  have hsd : p.s < (p.d : ℝ) := by
    have hdreal : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    nlinarith [p.hs]
  obtain ⟨c, K, hc, hK0, hρ⟩ := HRS.MS.S104e.s104e_gauss_rho
    p.hd p.hs0 hsd p.ha p.hβ δ p.c₁ p.C₁ 1 (by omega)
    R.thermal R.resulting
  obtain ⟨P, hP0, hU⟩ := HRS.MS.S104e.s104e_u2dec_of_gauss
    (d := p.d) hc 1 (p.d + 1)
  refine ⟨P * K, fun τ hτ => ?_⟩
  have hτ' : 0 ≤ τ := hτ.1
  obtain ⟨hreg, hbnd⟩ := hρ τ hτ'
  exact hU (R.ρ τ) K hK0 hreg (fun k hk x => hbnd k hk x)

/-- The exact S104e interface along an actual common-radius trajectory,
specialized to one Hermite basis datum. -/
theorem fp81s21_hermite_adjoint
    (p : HRS.MS.R26T3.Parameters) {δ : ℝ}
    (R : HRS.MS.R26T3.Trajectory p δ)
    (α : MultiIndex p.d) {t : ℝ} (ht : 0 ≤ t) :
    ∃ f : ℝ → Euc p.d → ℝ,
      IsClassicalAdjointW (HRS.MS.R26T3.r26t3_coeff R) t
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α) f := by
  have hsd : p.s < (p.d : ℝ) := by
    have hdreal : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    nlinarith [p.hs]
  have hhex := HRS.MS.S104e.s104e_hex p.hd p.hs0 hsd p.ha p.hβ
    δ p.c₁ p.C₁ R.thermal
  have h := hhex R.ε R.ψ R.ρ R.admissible R.resulting α t ht
  simpa [HRS.MS.R26T3.r26t3_coeff] using h

/-- Every finite Hermite combination has a classical adjoint along the same
trajectory and at every terminal time. -/
theorem fp81s21_adjoint_of_hermite_combo
    (p : HRS.MS.R26T3.Parameters) {δ : ℝ}
    (R : HRS.MS.R26T3.Trajectory p δ)
    {φ : Euc p.d → ℝ}
    (hφ : IsR2DualCombo (wholeSpaceIndex p.d : ℝ) φ)
    {t : ℝ} (ht : 0 ≤ t) :
    ∃ f : ℝ → Euc p.d → ℝ,
      IsClassicalAdjointW (HRS.MS.R26T3.r26t3_coeff R) t φ f := by
  obtain ⟨A, hA⟩ := fp81s21_density_u2dec p R ht
  have hsd : p.s < (p.d : ℝ) := by
    have hdreal : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    nlinarith [p.hs]
  have hhex := HRS.MS.S104e.s104e_hex p.hd p.hs0 hsd p.ha p.hβ
    δ p.c₁ p.C₁ R.thermal
  have hbasis : ∀ α : MultiIndex p.d, ∃ f : ℝ → Euc p.d → ℝ,
      IsClassicalAdjointW ((quadraticGradientDyn p.d p.s p.a p.β).coeff R.ρ)
        t (oscTestFun (wholeSpaceIndex p.d : ℝ) α) f := by
    intro α
    exact hhex R.ε R.ψ R.ρ R.admissible R.resulting α t ht
  rcases hφ with ⟨S, coeff, rfl⟩
  induction S using Finset.induction_on with
  | empty =>
      obtain ⟨f, hf⟩ := hbasis (0 : MultiIndex p.d)
      have hz := HRS.MS.R2WinOrbNL.s103c_lincomb p.hd p.hs0 hsd
        (show (p.d : ℝ) < ((p.d + 1 : ℕ) : ℝ) by exact_mod_cast Nat.lt_succ_self p.d)
        R.ρ hA 0 0 hf hf
      refine ⟨fun _ _ => 0, ?_⟩
      simpa [HRS.MS.R26T3.r26t3_coeff] using hz
  | @insert α S hα ih =>
      obtain ⟨g, hg⟩ := hbasis α
      obtain ⟨f, hf⟩ := ih
      have hsum := HRS.MS.R2WinOrbNL.s103c_lincomb p.hd p.hs0 hsd
        (show (p.d : ℝ) < ((p.d + 1 : ℕ) : ℝ) by exact_mod_cast Nat.lt_succ_self p.d)
        R.ρ hA (coeff α) 1 hg hf
      have heq :
          (fun x => coeff α * oscTestFun (wholeSpaceIndex p.d : ℝ) α x +
            1 * (∑ β ∈ S, coeff β * oscTestFun (wholeSpaceIndex p.d : ℝ) β x)) =
          (fun x => ∑ β ∈ insert α S,
            coeff β * oscTestFun (wholeSpaceIndex p.d : ℝ) β x) := by
        funext x
        simp [Finset.sum_insert, hα]
      refine ⟨fun r x => coeff α * g r x + f r x, ?_⟩
      rw [← heq]
      simpa [HRS.MS.R26T3.r26t3_coeff] using hsum

/-- Finite Hermite combinations are closed under the test-class linear
combination used by the adjoint propagator. -/
theorem fp81s21_hermite_combo_linear
    {d : ℕ} {m : ℝ} {φ ψ : Euc d → ℝ} (hφ : IsR2DualCombo m φ)
    (hψ : IsR2DualCombo m ψ) (c : ℝ) :
    IsR2DualCombo m (fun x => φ x + c * ψ x) := by
  rcases hφ with ⟨S, a, rfl⟩
  rcases hψ with ⟨T, b, rfl⟩
  let U := S ∪ T
  let q : MultiIndex d → ℝ := fun α =>
    (if α ∈ S then a α else 0) + c * (if α ∈ T then b α else 0)
  refine ⟨U, q, ?_⟩
  funext x
  simp only [q]
  have hS : ∑ α ∈ U, (if α ∈ S then a α else 0) * oscTestFun m α x =
      ∑ α ∈ S, a α * oscTestFun m α x := by
    have hfilter : U.filter (fun α => α ∈ S) = S := by
      ext α
      simp [U]
    simp only [ite_mul, zero_mul]
    rw [← Finset.sum_filter, hfilter]
  have hT : ∑ α ∈ U, (if α ∈ T then b α else 0) * oscTestFun m α x =
      ∑ α ∈ T, b α * oscTestFun m α x := by
    have hfilter : U.filter (fun α => α ∈ T) = T := by
      ext α
      simp [U]
    simp only [ite_mul, zero_mul]
    rw [← Finset.sum_filter, hfilter]
  have hU :
      ∑ α ∈ U,
          ((if α ∈ S then a α else 0) + c * (if α ∈ T then b α else 0)) *
            oscTestFun m α x =
        (∑ α ∈ U, (if α ∈ S then a α else 0) * oscTestFun m α x) +
          c * (∑ α ∈ U, (if α ∈ T then b α else 0) * oscTestFun m α x) := by
    calc
      _ = ∑ α ∈ U,
          ((if α ∈ S then a α else 0) * oscTestFun m α x +
            c * ((if α ∈ T then b α else 0) * oscTestFun m α x)) := by
              apply Finset.sum_congr rfl
              intro α hα
              ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  calc
    (∑ α ∈ S, a α * oscTestFun m α x) +
        c * (∑ α ∈ T, b α * oscTestFun m α x) =
      (∑ α ∈ U, (if α ∈ S then a α else 0) * oscTestFun m α x) +
        c * (∑ α ∈ U, (if α ∈ T then b α else 0) * oscTestFun m α x) := by rw [hS, hT]
    _ = ∑ α ∈ U,
        ((if α ∈ S then a α else 0) + c * (if α ∈ T then b α else 0)) *
          oscTestFun m α x := hU.symm

/-- On finite Hermite combinations, `r26t3_U` is the chosen classical
propagator and is linear in the terminal datum. -/
theorem fp81s21_U_linear_of_hermite_combo
    (p : HRS.MS.R26T3.Parameters) {δ : ℝ}
    (R : HRS.MS.R26T3.Trajectory p δ)
    {φ ψ : Euc p.d → ℝ}
    (hφ : IsR2DualCombo (wholeSpaceIndex p.d : ℝ) φ)
    (hψ : IsR2DualCombo (wholeSpaceIndex p.d : ℝ) ψ)
    (c : ℝ) {t r : ℝ} (ht : 0 ≤ t) (hr : r ∈ Set.Icc (0 : ℝ) t) :
    HRS.MS.R26T3.r26t3_U R r t (fun x => φ x + c * ψ x) =
      fun x => HRS.MS.R26T3.r26t3_U R r t φ x +
        c * HRS.MS.R26T3.r26t3_U R r t ψ x := by
  obtain ⟨f, hf⟩ := fp81s21_adjoint_of_hermite_combo p R hφ ht
  obtain ⟨g, hg⟩ := fp81s21_adjoint_of_hermite_combo p R hψ ht
  have hsd : p.s < (p.d : ℝ) := by
    have hdreal : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    nlinarith [p.hs]
  obtain ⟨A, hA⟩ := fp81s21_density_u2dec p R ht
  have hlin0 := HRS.MS.R2WinOrbNL.s103c_lincomb p.hd p.hs0 hsd
    (show (p.d : ℝ) < ((p.d + 1 : ℕ) : ℝ) by exact_mod_cast Nat.lt_succ_self p.d)
    R.ρ hA 1 c hf hg
  have hlin : IsClassicalAdjointW ((quadraticGradientDyn p.d p.s p.a p.β).coeff R.ρ)
      t (fun x => φ x + c * ψ x) (fun q x => f q x + c * g q x) := by
    simpa using hlin0
  have huF := HRS.MS.S104e.s104e_unique p.hd p.hs0 hsd p.ha p.hβ
    δ p.c₁ p.C₁ R.thermal R.admissible R.resulting t ht ⟨ht, le_rfl⟩ hf
  have huG := HRS.MS.S104e.s104e_unique p.hd p.hs0 hsd p.ha p.hβ
    δ p.c₁ p.C₁ R.thermal R.admissible R.resulting t ht ⟨ht, le_rfl⟩ hg
  have huSum := HRS.MS.S104e.s104e_unique p.hd p.hs0 hsd p.ha p.hβ
    δ p.c₁ p.C₁ R.thermal R.admissible R.resulting t ht ⟨ht, le_rfl⟩ hlin
  have ef : HRS.MS.R26T3.r26t3_U R r t φ = f r := by
    simpa [HRS.MS.R26T3.r26t3_U, HRS.MS.R26T3.r26t3_coeff] using huF r hr
  have eg : HRS.MS.R26T3.r26t3_U R r t ψ = g r := by
    simpa [HRS.MS.R26T3.r26t3_U, HRS.MS.R26T3.r26t3_coeff] using huG r hr
  have esum : HRS.MS.R26T3.r26t3_U R r t (fun x => φ x + c * ψ x) =
      (fun x => f r x + c * g r x) := by
    simpa [HRS.MS.R26T3.r26t3_U, HRS.MS.R26T3.r26t3_coeff] using huSum r hr
  rw [esum, ef, eg]

/-- The chosen propagator preserves constants along a resulting trajectory. -/
theorem fp81s21_U_constant
    (p : HRS.MS.R26T3.Parameters) {δ : ℝ}
    (R : HRS.MS.R26T3.Trajectory p δ)
    (c : ℝ) {t r : ℝ} (ht : 0 ≤ t) (hr : r ∈ Set.Icc (0 : ℝ) t) :
    HRS.MS.R26T3.r26t3_U R r t (fun _ => c) = fun _ => c := by
  have hsd : p.s < (p.d : ℝ) := by
    have hdreal : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    nlinarith [p.hs]
  have hconst : IsClassicalAdjointW
      ((quadraticGradientDyn p.d p.s p.a p.β).coeff R.ρ) t
      (fun _ => c) (fun _ _ => c) :=
    HRS.MS.Wad.s8d_const_classical _ t c
  have hu := HRS.MS.S104e.s104e_unique p.hd p.hs0 hsd p.ha p.hβ
    δ p.c₁ p.C₁ R.thermal R.admissible R.resulting t ht ⟨ht, le_rfl⟩ hconst
  simpa [HRS.MS.R26T3.r26t3_U, HRS.MS.R26T3.r26t3_coeff] using hu r hr

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_hermite_adjoint
#print axioms HRS.Fp81.S21.fp81s21_adjoint_of_hermite_combo
#print axioms HRS.Fp81.S21.fp81s21_hermite_combo_linear
#print axioms HRS.Fp81.S21.fp81s21_U_linear_of_hermite_combo
#print axioms HRS.Fp81.S21.fp81s21_U_constant

end
