import HRS.MS.R2InterpAux15

/-!
# S10.2 (worker S102), part 16: quantitative bounds of `V^{t,u}z`

For `|z f| ≤ M ‖f‖_E` on the tests: `‖V^{t,u}z‖ ≤ |M| K_c S^{1/2}` and `‖V^{t,u}z - V^{t',u}z‖ ≤ |M| K_c S^{1/2} (t - t')`, `S = ∑ c_α²`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MS.FixEq

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ} {z : (Euc d → ℝ) → ℝ}

/-- The constant `K_V = K_c S^{1/2}`. -/
def s102_KV (d r : ℕ) (Pw : ℝ) (c : MultiIndex d → ℝ) : ℝ := s57pC d r Pw * Real.sqrt (∑' α, c α ^ 2)

theorem s102_KV_nonneg (d r : ℕ) (Pw : ℝ) (c : MultiIndex d → ℝ) : 0 ≤ s102_KV d r Pw c :=
  mul_nonneg (s57pC_nonneg d r Pw) (Real.sqrt_nonneg _)

theorem s102_Vprop_norm_M (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) (hz : S102Z r Pw z)
    (hlin : S102Lin C m T) {M : ℝ}
    (hM : ∀ f, IsR2WeightedTest r Pw f → |z f| ≤ M * (weightedSobolevE r Pw f).toReal)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T) {t : ℝ} (ht : t ∈ Icc u T) :
    ‖r2Vprop C m t u z‖ ≤ |M| * s102_KV d r Pw c := by
  set S : ℝ := ∑' α, c α ^ 2 with hS
  set A : ℝ := |M| * s57pC d r Pw with hA
  have hA0 : 0 ≤ A := mul_nonneg (abs_nonneg M) (s57pC_nonneg d r Pw)
  have hS0 : 0 ≤ S := tsum_nonneg fun α => sq_nonneg _
  have hcoord : ∀ α, |OscDual.coord (r2Vprop C m t u z) α| ≤ A * c α := by
    intro α
    rw [s102_Vprop_coord hP hD hz hlin hu ht]
    refine (s102_z_orbit_bound hP hD hz hM hu ht α).trans (le_of_eq ?_)
    rw [hA]; ring
  have hsq : Summable fun α => (A * c α) ^ 2 :=
    (hD.summable.mul_left (A ^ 2)).congr (fun α => by ring)
  rw [OscDual.norm_eq_coord]
  have h1 : ∑' α, OscDual.coord (r2Vprop C m t u z) α ^ 2 ≤ A ^ 2 * S := by
    calc _ ≤ ∑' α, (A * c α) ^ 2 :=
          Summable.tsum_le_tsum (fun α => by
            have := hcoord α
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) this 2)
            (OscDual.coord_sq_summable' _) hsq
      _ = A ^ 2 * S := by
          simp_rw [mul_pow]
          rw [tsum_mul_left]
  calc Real.sqrt _ ≤ Real.sqrt (A ^ 2 * S) := Real.sqrt_le_sqrt h1
    _ = A * Real.sqrt S := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hA0]
    _ = |M| * s102_KV d r Pw c := by rw [hA, s102_KV]; ring

theorem s102_Vprop_lip_M (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) (hz : S102Z r Pw z)
    (hlin : S102Lin C m T) {M : ℝ}
    (hM : ∀ f, IsR2WeightedTest r Pw f → |z f| ≤ M * (weightedSobolevE r Pw f).toReal)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T) {t' t : ℝ} (ht' : t' ∈ Icc u T) (ht : t ∈ Icc u T) (htt : t' ≤ t) :
    ‖r2Vprop C m t u z - r2Vprop C m t' u z‖ ≤ |M| * s102_KV d r Pw c * (t - t') := by
  set S : ℝ := ∑' α, c α ^ 2 with hS
  set A : ℝ := |M| * s57pC d r Pw with hA
  have hA0 : 0 ≤ A := mul_nonneg (abs_nonneg M) (s57pC_nonneg d r Pw)
  have hS0 : 0 ≤ S := tsum_nonneg fun α => sq_nonneg _
  have hcoord : ∀ α, |OscDual.coord (r2Vprop C m t u z - r2Vprop C m t' u z) α| ≤ A * (t - t') * c α := by
    intro α
    rw [s102_coord_sub, s102_Vprop_coord hP hD hz hlin hu ht, s102_Vprop_coord hP hD hz hlin hu ht']
    refine (s102_z_orbit_diff hP hD hz hM hu ht' ht htt α).trans (le_of_eq ?_)
    rw [hA]; ring
  have hsq : Summable fun α => (A * (t - t') * c α) ^ 2 :=
    (hD.summable.mul_left ((A * (t - t')) ^ 2)).congr (fun α => by ring)
  rw [OscDual.norm_eq_coord]
  have h1 : ∑' α, OscDual.coord (r2Vprop C m t u z - r2Vprop C m t' u z) α ^ 2 ≤
      (A * (t - t')) ^ 2 * S := by
    calc _ ≤ ∑' α, (A * (t - t') * c α) ^ 2 :=
          Summable.tsum_le_tsum (fun α => by
            have := hcoord α
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) this 2)
            (OscDual.coord_sq_summable' _) hsq
      _ = (A * (t - t')) ^ 2 * S := by
          simp_rw [mul_pow]
          rw [tsum_mul_left]
  calc Real.sqrt _ ≤ Real.sqrt ((A * (t - t')) ^ 2 * S) := Real.sqrt_le_sqrt h1
    _ = A * (t - t') * Real.sqrt S := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hA0 (sub_nonneg.2 htt))]
    _ = |M| * s102_KV d r Pw c * (t - t') := by rw [hA, s102_KV]; ring

end HRS.MS.R2Interp

end
