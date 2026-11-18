import HRS.MS.SA16Y4Fam1
import HRS.MS.SA16Y3Cu1
import HRS.MS.SA16Y4Mb2
import HRS.MS.SA16SOp2

/-!
# S.A.16 (SA16Y11) Dr2: truncated mollification of a BOUNDED `C^{m+1}` coefficient has a bound linear in the sup bound, uniformly in `n`

`sa16y11_tm_bdd`: if `‖D^j b_i‖ ≤ δ` for all `j ≤ m+1` then `SA16BddCoef (m+1) (C δ) (tm_n b)` with `C = C(d,m)` independent of `n`
and `δ` (scaling of `sa16y3_cut_mul_der_bound` by `δ⁻¹`; the existing `sa16y4_trunc_mol_coef` has an `n`-dependent value bound because it allows
linear growth).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Dr2
variable {d : ℕ}

theorem sa16y11_tm_bdd (d m : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (δ : ℝ), 0 ≤ δ → ∀ (n : ℕ) (bi : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      (∀ i, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (bi i)) →
      (∀ i, ∀ j ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ j (bi i) x‖ ≤ δ) →
      SA16BddCoef (m + 1) (C * δ) (fun i => sa16y4_tm d n (bi i)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C1, hC1⟩ := sa16y3_cut_mul_der_bound (d := d) (k := m + 1) (A := 1) (L := (d : ℝ) ^ (m + 1))
    zero_le_one (by positivity)
  refine ⟨max C1 1, le_max_right _ _, fun δ hδ n bi hbs hbd => ?_⟩
  have hρ0 : ∀ z, 0 ≤ sa16y_rho d n z := sa16y_rho_nonneg n
  have hρ1 := sa16y_rho_int (d := d) n
  have hρs : ∀ z : EuclideanSpace ℝ (Fin d), 1 < ‖z‖ → sa16y_rho d n z = 0 := by
    intro z hz
    refine sa16y_rho_supp n z (lt_of_le_of_lt ?_ hz)
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hRn : (1 : ℝ) ≤ (n : ℝ) + 1 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hCmax : 0 ≤ max C1 1 * δ := mul_nonneg (le_trans zero_le_one (le_max_right _ _)) hδ
  refine ⟨hCmax, fun i => sa16y4_tm_smooth n (hbs i).continuous, fun i j hj x => ?_⟩
  have hgabs : ∀ x, |∫ y, bi i y * sa16y_rho d n (x - y)| ≤ δ := by
    intro x
    have h := sa16y4_mol_growth (sa16y4_rho_cc n) hρ0 hρ1 hρs (b := bi i) (A := δ) (L := 0)
      (fun y => by
        have := hbd i 0 (Nat.zero_le _) y
        rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
        simpa using this) le_rfl x
    simpa using h
  rcases hδ.eq_or_lt with h0 | hpos
  · -- δ = 0
    have hb0 : ∀ y, bi i y = 0 := fun y => by
      have := hbd i 0 (Nat.zero_le _) y
      rw [← h0, norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
      exact abs_nonpos_iff.1 this
    have : sa16y4_tm d n (bi i) = fun _ => 0 := by
      funext x
      unfold sa16y4_tm
      simp [hb0]
    rw [this, ← h0, mul_zero]
    rcases Nat.eq_zero_or_pos j with hj0 | hj1
    · subst hj0; simp
    · rw [iteratedFDeriv_const_of_ne (by omega)]; simp
  · -- δ > 0: scale to `A = 1`
    set g : EuclideanSpace ℝ (Fin d) → ℝ := fun x => ∫ y, bi i y * sa16y_rho d n (x - y) with hg
    set g' : EuclideanSpace ℝ (Fin d) → ℝ := fun x => δ⁻¹ * g x with hg'
    have hgs : ContDiff ℝ ∞ g := sa16y4_mol_smooth n (hbs i).continuous
    have hg's : ContDiff ℝ ∞ g' := contDiff_const.mul hgs
    have hg'abs : ∀ x, |g' x| ≤ 1 + (d : ℝ) ^ (m + 1) * ‖x‖ := by
      intro x
      have : |g' x| ≤ 1 := by
        simp only [hg', abs_mul, abs_inv, abs_of_pos hpos]
        calc δ⁻¹ * |g x| ≤ δ⁻¹ * δ := mul_le_mul_of_nonneg_left (hgabs x) (inv_nonneg.2 hδ)
          _ = 1 := inv_mul_cancel₀ hpos.ne'
      nlinarith [norm_nonneg x, pow_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) (m + 1)]
    have hg'der : ∀ j, 1 ≤ j → j ≤ m + 1 → ∀ x, ‖iteratedFDeriv ℝ j g' x‖ ≤ (d : ℝ) ^ (m + 1) := by
      intro j hj1 hj2 x
      have h1 := sa16y4_mol_iter_bound (sa16y4_rho_cc n) hρ0 hρ1 (hbs i) (L := δ)
        (fun j _ hjk x => hbd i j hjk x) hj1 hj2 x
      have h2 := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (a := δ⁻¹) (f := g) (i := j) (x := x)
        ((hgs.of_le (by exact_mod_cast le_top)).contDiffAt)
      have e : g' = δ⁻¹ • g := rfl
      rw [e, h2, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos)]
      calc δ⁻¹ * ‖iteratedFDeriv ℝ j g x‖ ≤ δ⁻¹ * ((d : ℝ) ^ j * δ) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hδ)
        _ = (d : ℝ) ^ j := by field_simp
        _ ≤ (d : ℝ) ^ (m + 1) := pow_le_pow_right₀ hd1 hj2
    have hmain := hC1 g' hg's hg'abs hg'der ((n : ℝ) + 1) hRn
    rcases Nat.eq_zero_or_pos j with hj0 | hj1
    · subst hj0
      rw [norm_iteratedFDeriv_zero]
      unfold sa16y4_tm
      rw [Real.norm_eq_abs, abs_mul]
      have hχ1 : |sa16j_chi d ((n : ℝ) + 1) x| ≤ 1 := by
        unfold sa16j_chi
        rw [abs_of_nonneg ((sa16j_bump d).nonneg)]
        exact (sa16j_bump d).le_one
      calc |sa16j_chi d ((n : ℝ) + 1) x| * |∫ y, bi i y * sa16y_rho d n (x - y)| ≤ 1 * δ :=
            mul_le_mul hχ1 (hgabs x) (abs_nonneg _) zero_le_one
        _ ≤ max C1 1 * δ := mul_le_mul_of_nonneg_right (le_max_right _ _) hδ
    · have hfun : sa16y4_tm d n (bi i) = fun y => δ • (sa16j_chi d ((n : ℝ) + 1) y * g' y) := by
        funext y
        simp only [sa16y4_tm, hg', hg, smul_eq_mul]
        field_simp
      have hχg : ContDiff ℝ ∞ (fun y => sa16j_chi d ((n : ℝ) + 1) y * g' y) :=
        (sa16j_chi_contDiff d _).mul hg's
      have h3 := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (a := δ)
        (f := fun y => sa16j_chi d ((n : ℝ) + 1) y * g' y) (i := j) (x := x)
        ((hχg.of_le (by exact_mod_cast le_top)).contDiffAt)
      rw [hfun]
      show ‖iteratedFDeriv ℝ j (δ • fun y => sa16j_chi d ((n : ℝ) + 1) y * g' y) x‖ ≤ _
      rw [h3, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
      calc δ * ‖iteratedFDeriv ℝ j (fun y => sa16j_chi d ((n : ℝ) + 1) y * g' y) x‖ ≤ δ * C1 :=
            mul_le_mul_of_nonneg_left (hmain j hj1 hj x) hδ
        _ ≤ max C1 1 * δ := by nlinarith [le_max_left C1 1]

end Dr2

end HRS.Whole.AppendixA.Phase2SA16R

end
