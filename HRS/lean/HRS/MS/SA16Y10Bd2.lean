import HRS.MS.SA16Y10Bd1

/-!
# S.A.16 (SA16Y10) Bd2: the truncated mollification of a small bounded coefficient is small, uniformly in `n`

`sa16y10_tm_bdd`: if `‖D^j h_i‖ ≤ δ` for `0 ≤ j ≤ m+1` (`h_i ∈ C^{m+1}`), then `(tm n h_i)_i` is `SA16BddCoef (m+1) (Cb δ)`,
`Cb` independent of `n, δ, h`.
-/

set_option autoImplicit false

noncomputable section
open scoped ContDiff
open Filter MeasureTheory

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem sa16y10_tm_bdd (d m : ℕ) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (n : ℕ) (h : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) (δ : ℝ), 0 ≤ δ →
      (∀ i, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (h i)) → (∀ i y, |h i y| ≤ δ) →
      (∀ i j, 1 ≤ j → j ≤ m + 1 → ∀ x, ‖iteratedFDeriv ℝ j (h i) x‖ ≤ δ) →
      SA16BddCoef (m + 1) (Cb * δ) (fun i => sa16y4_tm d n (h i)) := by
  obtain ⟨B, hB0, B', hFam⟩ := sa16y4_trunc_mol_coef d m (A := 1) (L := 1) zero_le_one zero_le_one
  refine ⟨max B 1, le_trans zero_le_one (le_max_right _ _), fun n h δ hδ hhs hhb hhj => ?_⟩
  rcases hδ.eq_or_lt with h0 | hpos
  · subst h0
    have hz : ∀ i, h i = fun _ => (0 : ℝ) := fun i => funext fun y => abs_nonpos_iff.1 (by simpa using hhb i y)
    have htm : ∀ i, sa16y4_tm d n (h i) = fun _ => (0 : ℝ) := fun i => by
      have := sa16y10_tm_smul n 0 (h i)
      have e : (fun y => (0 : ℝ) * h i y) = h i := by rw [hz i]; funext y; simp
      rw [e] at this
      rw [this]; funext x; simp
    refine ⟨by simp, fun i => ?_, fun i j hj x => ?_⟩
    · rw [htm i]; exact contDiff_const
    · rw [htm i]
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp
      · rw [iteratedFDeriv_const_of_ne (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin d)) (Nat.pos_iff_ne_zero.1 hj0)]
        simp
  · set h' : Fin d → EuclideanSpace ℝ (Fin d) → ℝ := fun i y => δ⁻¹ * h i y with hh'
    have hh's : ∀ i, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (h' i) := fun i => contDiff_const.mul (hhs i)
    have hh'1 : ∀ i y, |h' i y| ≤ 1 := fun i y => by
      rw [hh', abs_mul, abs_of_pos (inv_pos.2 hpos)]
      calc δ⁻¹ * |h i y| ≤ δ⁻¹ * δ := mul_le_mul_of_nonneg_left (hhb i y) (inv_nonneg.2 hpos.le)
        _ = 1 := by field_simp
    have hh'b : ∀ i y, |h' i y| ≤ 1 + 1 * ‖y‖ := fun i y => by
      nlinarith [norm_nonneg y, hh'1 i y]
    have hh'j : ∀ i j, 1 ≤ j → j ≤ m + 1 → ∀ x, ‖iteratedFDeriv ℝ j (h' i) x‖ ≤ 1 := by
      intro i j hj1 hj2 x
      have hc : ContDiffAt ℝ j (fun y => h i y) x := ((hhs i).of_le (by exact_mod_cast hj2)).contDiffAt
      have e : iteratedFDeriv ℝ j (fun y => δ⁻¹ * h i y) x = δ⁻¹ • iteratedFDeriv ℝ j (h i) x :=
        iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := δ⁻¹) (f := h i) (x := x) (i := j) hc
      show ‖iteratedFDeriv ℝ j (fun y => δ⁻¹ * h i y) x‖ ≤ 1
      rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hpos.le)]
      calc δ⁻¹ * ‖iteratedFDeriv ℝ j (h i) x‖ ≤ δ⁻¹ * δ := mul_le_mul_of_nonneg_left (hhj i j hj1 hj2 x) (inv_nonneg.2 hpos.le)
        _ = 1 := by field_simp
    obtain ⟨hDer, -⟩ := hFam n h' hh's hh'b hh'j
    have hbase : SA16BddCoef (m + 1) (max B 1) (fun i => sa16y4_tm d n (h' i)) := by
      refine ⟨le_trans zero_le_one (le_max_right _ _), fun i => sa16y4_tm_smooth n (hh's i).continuous, fun i j hj x => ?_⟩
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
        refine le_trans ?_ (le_max_right _ _)
        unfold sa16y4_tm
        have hρ0 := sa16y_rho_nonneg (d := d) n
        have hmol := sa16y4_mol_growth (sa16y4_rho_cc n) hρ0 (sa16y_rho_int n)
          (fun z hz => sa16y_rho_supp n z (lt_of_le_of_lt (by
            rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) hz))
          (b := h' i) (A := 1) (L := 0) (fun y => by simpa using hh'1 i y) le_rfl x
        have hχ1 : |sa16j_chi d ((n : ℝ) + 1) x| ≤ 1 := by
          unfold sa16j_chi
          rw [abs_of_nonneg ((sa16j_bump d).nonneg)]
          exact (sa16j_bump d).le_one
        have hm1 : |∫ y, h' i y * sa16y_rho d n (x - y)| ≤ 1 := by simpa using hmol
        rw [abs_mul]
        calc |sa16j_chi d ((n : ℝ) + 1) x| * |∫ y, h' i y * sa16y_rho d n (x - y)| ≤ 1 * 1 :=
              mul_le_mul hχ1 hm1 (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      · exact (hDer.bound i j hj0 hj x).trans (le_max_left _ _)
    have hsc := sa16y10_BddCoef_smul hbase δ
    have e : (fun i x => δ * sa16y4_tm d n (h' i) x) = fun i => sa16y4_tm d n (h i) := by
      funext i
      have := sa16y10_tm_smul n δ (h' i)
      have eh : (fun y => δ * h' i y) = h i := by
        funext y; rw [hh']; field_simp
      rw [eh] at this
      exact this.symm
    rw [e, abs_of_pos hpos, mul_comm] at hsc
    exact hsc

end HRS.Whole.AppendixA.Phase2SA16R

end
