import HRS.MS.Fp81S21RecentRS4

/-!
# S2.1(iii), packet 34a: signed scalar correction profile

Drift and covariance expectations enter with the physical signs
`- E dval + (1/2) E jval`.  Separate mixed-coupling bounds for the two
functionals give the scalar recent profile with no particle-scale factor.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Filter Topology

namespace HRS.Fp81.S21

/-- The signed drift/covariance correction, with the physical coefficients. -/
def fp81s21_recentRSCorrection (dval jval : ℝ) : ℝ := -dval + (1 / 2 : ℝ) * jval

/-- Scalar profile obtained from the drift and covariance mixed-coupling
profiles, using the same joint distance, moment bound, and positive slack. -/
def fp81s21_recentRSScalarProfile (C_D C_J M : ℝ)
    (e η : ℕ → ℝ) : ℕ → ℝ := fun N =>
  C_D * (1 + Real.sqrt M) * (e N + η N) +
    (C_J / 2) * (1 + Real.sqrt M) * (e N + η N)

/-- Pointwise scalar correction comparison with the drift minus sign and
covariance half factor. -/
theorem fp81s21_recentRS_correction_difference
    (dN dG jN jG : ℝ) :
    |fp81s21_recentRSCorrection dN jN - fp81s21_recentRSCorrection dG jG| ≤
      |dN - dG| + (1 / 2 : ℝ) * |jN - jG| := by
  have hidentity : fp81s21_recentRSCorrection dN jN -
      fp81s21_recentRSCorrection dG jG = -(dN - dG) + (1 / 2 : ℝ) * (jN - jG) := by
    simp [fp81s21_recentRSCorrection]
    ring
  rw [hidentity]
  calc
    |-(dN - dG) + (1 / 2 : ℝ) * (jN - jG)| ≤
        |-(dN - dG)| + |(1 / 2 : ℝ) * (jN - jG)| := abs_add_le _ _
    _ = |dN - dG| + (1 / 2 : ℝ) * |jN - jG| := by
      rw [abs_neg, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]

/-- The two RS expectation comparisons imply a nonnegative scalar recent
profile tending to zero.  The hypotheses `hD` and `hJ` are the outputs of the
W2 comparison theorem for the drift and covariance functionals, respectively. -/
theorem fp81s21_recentRS_scalar_profile
    (dN dG jN jG e η : ℕ → ℝ) (C_D C_J M : ℝ)
    (hCD : 0 ≤ C_D) (hCJ : 0 ≤ C_J) (hM : 0 ≤ M)
    (he : ∀ N, 0 ≤ e N) (hη : ∀ N, 0 < η N)
    (heT : Tendsto e atTop (𝓝 0)) (hηT : Tendsto η atTop (𝓝 0))
    (hD : ∀ N, |dN N - dG N| ≤ C_D * (1 + Real.sqrt M) * (e N + η N))
    (hJ : ∀ N, |jN N - jG N| ≤ C_J * (1 + Real.sqrt M) * (e N + η N)) :
    (∀ N, 0 ≤ fp81s21_recentRSScalarProfile C_D C_J M e η N) ∧
    Tendsto (fp81s21_recentRSScalarProfile C_D C_J M e η) atTop (𝓝 0) ∧
    (∀ N, |fp81s21_recentRSCorrection (dN N) (jN N) -
      fp81s21_recentRSCorrection (dG N) (jG N)| ≤
        fp81s21_recentRSScalarProfile C_D C_J M e η N) := by
  have hMroot : 0 ≤ 1 + Real.sqrt M := by positivity
  have heη : Tendsto (fun N => e N + η N) atTop (𝓝 0) := by
    simpa using heT.add hηT
  have hDlim : Tendsto
      (fun N => C_D * (1 + Real.sqrt M) * (e N + η N)) atTop (𝓝 0) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      heη.const_mul (C_D * (1 + Real.sqrt M))
  have hJlim : Tendsto
      (fun N => (C_J / 2) * (1 + Real.sqrt M) * (e N + η N)) atTop (𝓝 0) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      heη.const_mul ((C_J / 2) * (1 + Real.sqrt M))
  refine ⟨?_, ?_, ?_⟩
  · intro N
    have hsum : 0 ≤ e N + η N := add_nonneg (he N) (hη N).le
    simp [fp81s21_recentRSScalarProfile]
    exact add_nonneg
      (mul_nonneg (mul_nonneg hCD hMroot) hsum)
      (mul_nonneg (mul_nonneg (div_nonneg hCJ (by norm_num)) hMroot) hsum)
  · change Tendsto
      (fun N => C_D * (1 + Real.sqrt M) * (e N + η N) +
        (C_J / 2) * (1 + Real.sqrt M) * (e N + η N)) atTop (𝓝 0)
    simpa using hDlim.add hJlim
  · intro N
    have hcorr := fp81s21_recentRS_correction_difference
      (dN N) (dG N) (jN N) (jG N)
    calc
      |fp81s21_recentRSCorrection (dN N) (jN N) -
          fp81s21_recentRSCorrection (dG N) (jG N)| ≤
          |dN N - dG N| + (1 / 2 : ℝ) * |jN N - jG N| := hcorr
      _ ≤ C_D * (1 + Real.sqrt M) * (e N + η N) +
            (1 / 2 : ℝ) * (C_J * (1 + Real.sqrt M) * (e N + η N)) := by
          exact add_le_add (hD N)
            (mul_le_mul_of_nonneg_left (hJ N) (by norm_num : 0 ≤ (1 / 2 : ℝ)))
      _ = fp81s21_recentRSScalarProfile C_D C_J M e η N := by
          simp [fp81s21_recentRSScalarProfile]
          ring

/- Explicit positive-slack specialization with `η_N = 1 / (N + 1)`, as
provided by the approximate W2 coupling theorem. -/
theorem fp81s21_recentRS_scalar_profile_inv
    (dN dG jN jG e : ℕ → ℝ) (C_D C_J M : ℝ)
    (hCD : 0 ≤ C_D) (hCJ : 0 ≤ C_J) (hM : 0 ≤ M)
    (he : ∀ N, 0 ≤ e N) (heT : Tendsto e atTop (𝓝 0))
    (hD : ∀ N, |dN N - dG N| ≤
      C_D * (1 + Real.sqrt M) * (e N + 1 / ((N : ℝ) + 1)))
    (hJ : ∀ N, |jN N - jG N| ≤
      C_J * (1 + Real.sqrt M) * (e N + 1 / ((N : ℝ) + 1))) :
    (∀ N, 0 ≤ fp81s21_recentRSScalarProfile C_D C_J M e
      (fun N => 1 / ((N : ℝ) + 1)) N) ∧
    Tendsto (fp81s21_recentRSScalarProfile C_D C_J M e
      (fun N => 1 / ((N : ℝ) + 1))) atTop (𝓝 0) ∧
    (∀ N, |fp81s21_recentRSCorrection (dN N) (jN N) -
      fp81s21_recentRSCorrection (dG N) (jG N)| ≤
        fp81s21_recentRSScalarProfile C_D C_J M e
          (fun N => 1 / ((N : ℝ) + 1)) N) := by
  let η : ℕ → ℝ := fun N => 1 / ((N : ℝ) + 1)
  have hη : ∀ N, 0 < η N := by
    intro N
    dsimp [η]
    positivity
  have hηT : Tendsto η atTop (𝓝 0) := by
    simpa [η] using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0))
  have hD' : ∀ N, |dN N - dG N| ≤ C_D * (1 + Real.sqrt M) * (e N + η N) := by
    simpa [η] using hD
  have hJ' : ∀ N, |jN N - jG N| ≤ C_J * (1 + Real.sqrt M) * (e N + η N) := by
    simpa [η] using hJ
  simpa [η] using fp81s21_recentRS_scalar_profile dN dG jN jG e η C_D C_J M
    hCD hCJ hM he hη heT hηT hD' hJ'

#print axioms fp81s21_recentRS_correction_difference
#print axioms fp81s21_recentRS_scalar_profile
#print axioms fp81s21_recentRS_scalar_profile_inv

end HRS.Fp81.S21

end
