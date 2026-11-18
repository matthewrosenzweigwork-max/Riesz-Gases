import HRS.MS.SA16Y4Mb2
import HRS.MS.SA16Y3Cu1
import HRS.MS.SA16Y3Dc1
import HRS.MS.SA16StrongApprox

/-!
# S.A.16 (SA16Y4) Fam1: the truncated mollified coefficients `χ_{n+1} (ρ_n ⋆ b_i)`

`sa16y4_tm d n f x = χ_{n+1}(x) ∫ f(y) ρ_n(x-y) dy`.
`sa16y4_trunc_mol_coef`: for coefficients `b_i ∈ C^{m+1}` with `|b_i| ≤ A + L‖·‖` and `‖D^j b_i‖ ≤ L` (`1 ≤ j ≤ m+1`) there are `B` and `B' : ℕ → ℝ`,
depending only on `d, m, A, L`, such that for EVERY `n` the family `(sa16y4_tm d n b_i)_i` is `SA16DerCoef (m+1) B` and
`SA16BddCoef (m+1) (B' n)` (the zeroth-order size grows like `n`; only needed qualitatively).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Fam1
variable {d : ℕ}

/-- `χ_{n+1} · (ρ_n ⋆ f)` -/
def sa16y4_tm (d n : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x => sa16j_chi d ((n : ℝ) + 1) x * ∫ y, f y * sa16y_rho d n (x - y)

lemma sa16y4_rho_cc (n : ℕ) : IsCcInfty (sa16y_rho d n) := ⟨sa16y_rho_smooth n, sa16y_rho_compact n⟩

lemma sa16y4_mol_smooth (n : ℕ) {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Continuous f) :
    ContDiff ℝ ∞ (fun x => ∫ y, f y * sa16y_rho d n (x - y)) :=
  sa16y3_conv_contDiff hf.locallyIntegrable (sa16y4_rho_cc n)

lemma sa16y4_tm_smooth (n : ℕ) {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Continuous f) :
    ContDiff ℝ ∞ (sa16y4_tm d n f) :=
  (sa16j_chi_contDiff d _).mul (sa16y4_mol_smooth n hf)

theorem sa16y4_trunc_mol_coef (d m : ℕ) {A L : ℝ} (hA0 : 0 ≤ A) (hL0 : 0 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ B' : ℕ → ℝ, ∀ (n : ℕ) (bi : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      (∀ i, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (bi i)) → (∀ i y, |bi i y| ≤ A + L * ‖y‖) →
      (∀ i j, 1 ≤ j → j ≤ m + 1 → ∀ x, ‖iteratedFDeriv ℝ j (bi i) x‖ ≤ L) →
      SA16DerCoef (m + 1) B (fun i => sa16y4_tm d n (bi i)) ∧
        SA16BddCoef (m + 1) (B' n) (fun i => sa16y4_tm d n (bi i)) := by
  set L' : ℝ := ((d : ℝ) + 1) ^ (m + 1) * L with hL'
  have hL'0 : 0 ≤ L' := by positivity
  have hLL' : L ≤ L' := by
    rw [hL']
    have : (1 : ℝ) ≤ ((d : ℝ) + 1) ^ (m + 1) := one_le_pow₀ (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)
    nlinarith
  obtain ⟨C, hC⟩ := sa16y3_cut_mul_der_bound (d := d) (k := m + 1) (A := A + L) (L := L') (by linarith) hL'0
  refine ⟨max C 0, le_max_right _ _, fun n => max (max C 0) (A + L + L' * (2 * ((n : ℝ) + 1))), fun n bi hbs hbg hbL => ?_⟩
  have hρ0 : ∀ z, 0 ≤ sa16y_rho d n z := sa16y_rho_nonneg n
  have hρ1 := sa16y_rho_int (d := d) n
  have hρs : ∀ z : EuclideanSpace ℝ (Fin d), 1 < ‖z‖ → sa16y_rho d n z = 0 := by
    intro z hz
    refine sa16y_rho_supp n z (lt_of_le_of_lt ?_ hz)
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hRn : (1 : ℝ) ≤ (n : ℝ) + 1 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hg : ∀ i, ContDiff ℝ ∞ (fun x => ∫ y, bi i y * sa16y_rho d n (x - y)) := fun i =>
    sa16y4_mol_smooth n (hbs i).continuous
  have hggrow : ∀ i x, |∫ y, bi i y * sa16y_rho d n (x - y)| ≤ (A + L) + L' * ‖x‖ := by
    intro i x
    refine (sa16y4_mol_growth (sa16y4_rho_cc n) hρ0 hρ1 hρs (hbg i) hL0 x).trans ?_
    nlinarith [norm_nonneg x]
  have hgder : ∀ i j, 1 ≤ j → j ≤ m + 1 → ∀ x,
      ‖iteratedFDeriv ℝ j (fun x => ∫ y, bi i y * sa16y_rho d n (x - y)) x‖ ≤ L' := by
    intro i j hj1 hj2 x
    refine (sa16y4_mol_iter_bound (sa16y4_rho_cc n) hρ0 hρ1 (hbs i) (hbL i) hj1 hj2 x).trans ?_
    rw [hL']
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]) hj2 |>.trans' (pow_le_pow_left₀ (Nat.cast_nonneg d) (by linarith) j)) hL0
  have hder : ∀ i j, 1 ≤ j → j ≤ m + 1 → ∀ x, ‖iteratedFDeriv ℝ j (sa16y4_tm d n (bi i)) x‖ ≤ C :=
    fun i j hj1 hj2 x => hC _ (hg i) (hggrow i) (hgder i) _ hRn j hj1 hj2 x
  refine ⟨⟨le_max_right _ _, fun i => sa16y4_tm_smooth n (hbs i).continuous, fun i j hj1 hj2 x =>
    (hder i j hj1 hj2 x).trans (le_max_left _ _)⟩, ?_⟩
  refine ⟨le_max_of_le_left (le_max_right _ _),
    fun i => sa16y4_tm_smooth n (hbs i).continuous, fun i j hj x => ?_⟩
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    rw [norm_iteratedFDeriv_zero]
    refine le_trans ?_ (le_max_right _ _)
    unfold sa16y4_tm
    by_cases hfar : 2 * ((n : ℝ) + 1) < ‖x‖
    · have := sa16y3_chi_zero_far (d := d) 0 (by linarith : (0 : ℝ) < (n : ℝ) + 1) hfar
      have h2 : sa16j_chi d ((n : ℝ) + 1) x = 0 := by
        have h3 := congrArg (fun F : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => EuclideanSpace ℝ (Fin d)) ℝ =>
          F (fun _ => 0)) this
        simpa [iteratedFDeriv_zero_apply] using h3
      rw [h2, zero_mul, norm_zero]
      have : (0 : ℝ) ≤ A + L + L' * (2 * ((n : ℝ) + 1)) := by positivity
      exact this
    · have hx : ‖x‖ ≤ 2 * ((n : ℝ) + 1) := not_lt.1 hfar
      have hχ1 : |sa16j_chi d ((n : ℝ) + 1) x| ≤ 1 := by
        unfold sa16j_chi
        rw [abs_of_nonneg ((sa16j_bump d).nonneg), ]
        exact (sa16j_bump d).le_one
      rw [Real.norm_eq_abs, abs_mul]
      calc |sa16j_chi d ((n : ℝ) + 1) x| * |∫ y, bi i y * sa16y_rho d n (x - y)|
          ≤ 1 * ((A + L) + L' * ‖x‖) := mul_le_mul hχ1 (hggrow i x) (abs_nonneg _) zero_le_one
        _ ≤ A + L + L' * (2 * ((n : ℝ) + 1)) := by nlinarith
  · exact (hder i j hpos (hj) x).trans ((le_max_left _ _).trans (le_max_left _ _))

end Fam1

end HRS.Whole.AppendixA.Phase2SA16R
