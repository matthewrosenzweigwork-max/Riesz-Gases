import HRS.MS.R26T8AG00d

/-!
# S8.2 observed-time layer, packet T8A.G00 (helper e): pointwise envelope bound for the Gibbs density

Off the collision set, `exp(-β H_N) · env_M² ≤ K0 · ∏_i (1+‖X_i‖)^k exp(-(βa/2)‖X_i‖²)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_g00e_sum_le_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) : 1 + ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 + x i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hS : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg fun i _ => hx i
    have h1 : (1 + x a) * (1 + ∑ i ∈ s, x i) ≤ (1 + x a) * ∏ i ∈ s, (1 + x i) :=
      mul_le_mul_of_nonneg_left ih (by linarith [hx a])
    nlinarith [hx a, mul_nonneg (hx a) hS]

theorem r26t8a_g00e_pt {d N : ℕ} (hN : 2 ≤ N) {s a beta M : ℝ} (hs : 0 < s) (ha : 0 < a)
    (hbeta : 0 < beta) (hM : 0 ≤ M) (k : ℕ) (hk : 2 * M ≤ k) (K : ℝ) (hK0 : 0 ≤ K)
    (hKb : ∀ t : ℝ, 0 < t → (1 + t ^ (-M)) ^ 2 * Real.exp (-(beta / (2 * N)) * t ^ (-s)) ≤ K)
    (X : EucConfig d N) (hX : X ∉ eucCollisionSet d N) :
    Real.exp (-beta * HRS.Whole.canonicalHamiltonian (rieszKernel d s) (HRS.Whole.confinement a) X) *
        (configPoleEnvelope M X) ^ 2 ≤
      (∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, K) *
        ∏ i : Fin N, ((1 + ‖X i‖) ^ k * Real.exp (-(beta * a / 2) * ‖X i‖ ^ 2)) := by
  -- the envelope squared
  have henv : (configPoleEnvelope M X) ^ 2 = (1 + ‖X‖) ^ (2 * M) *
      ∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-M)) ^ 2 := by
    unfold configPoleEnvelope
    have hA : ((1 + ‖X‖) ^ M) ^ 2 = (1 + ‖X‖) ^ (2 * M) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1
      push_cast
      ring
    have hB : (∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-M))) ^ 2 =
        ∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-M)) ^ 2 := by
      rw [← Finset.prod_pow]
      exact Finset.prod_congr rfl fun i _ => (Finset.prod_pow _ _ _).symm
    rw [mul_pow, hA, hB]
  rw [HRS.MS.R26T8A.r26t8a_g00d_exp_split hN hs X, henv]
  -- the pair factors: each ordered pair contributes at most `K`
  have hpair0 : ∀ i j : Fin N, 0 ≤ (1 + ‖X i - X j‖ ^ (-M)) ^ 2 *
      Real.exp (-(beta / (2 * N)) * ‖X i - X j‖ ^ (-s)) := fun i j =>
    mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hpair : ∀ i j : Fin N, i ≠ j →
      (1 + ‖X i - X j‖ ^ (-M)) ^ 2 * Real.exp (-(beta / (2 * N)) * ‖X i - X j‖ ^ (-s)) ≤ K := by
    intro i j hij
    have ht : 0 < ‖X i - X j‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h => hX ⟨i, j, hij, h⟩)
    exact hKb _ ht
  have hPE : (∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-M)) ^ 2) *
      (∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, Real.exp (-(beta / (2 * N)) * ‖X i - X j‖ ^ (-s))) =
      ∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, ((1 + ‖X i - X j‖ ^ (-M)) ^ 2 *
        Real.exp (-(beta / (2 * N)) * ‖X i - X j‖ ^ (-s))) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [← Finset.prod_mul_distrib]
  have hQ : (∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-M)) ^ 2) *
      (∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, Real.exp (-(beta / (2 * N)) * ‖X i - X j‖ ^ (-s))) ≤
      ∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, K := by
    rw [hPE]
    exact Finset.prod_le_prod₀ (fun i _ => Finset.prod_nonneg fun j _ => hpair0 i j)
      (fun i _ => Finset.prod_le_prod₀ (fun j _ => hpair0 i j)
        (fun j hj => hpair i j (Finset.ne_of_mem_erase hj).symm))
  -- the Gaussian part and the envelope growth
  have hE1 : (∏ i : Fin N, Real.exp (-beta * (a * ‖X i‖ ^ 2 / 2))) =
      ∏ i : Fin N, Real.exp (-(beta * a / 2) * ‖X i‖ ^ 2) :=
    Finset.prod_congr rfl fun i _ => by congr 1; ring
  have hE1nn : 0 ≤ ∏ i : Fin N, Real.exp (-(beta * a / 2) * ‖X i‖ ^ 2) :=
    Finset.prod_nonneg fun i _ => (Real.exp_pos _).le
  have hpow1 : (1 + ‖X‖) ^ (2 * M) ≤ (1 + ‖X‖) ^ k := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg X]) hk
  have hnorm : 1 + ‖X‖ ≤ ∏ i : Fin N, (1 + ‖X i‖) := by
    have hX1 : ‖X‖ ≤ ∑ i, ‖X i‖ :=
      (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)).2 fun i =>
        Finset.single_le_sum (f := fun i => ‖X i‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)
    exact le_trans (by linarith) (r26t8a_g00e_sum_le_prod Finset.univ (fun i => ‖X i‖)
      fun i => norm_nonneg _)
  have hpowk : (1 + ‖X‖) ^ k ≤ ∏ i : Fin N, (1 + ‖X i‖) ^ k := by
    rw [Finset.prod_pow]
    exact pow_le_pow_left₀ (by linarith [norm_nonneg X]) hnorm k
  have hkey : (1 + ‖X‖) ^ (2 * M) * ∏ i : Fin N, Real.exp (-(beta * a / 2) * ‖X i‖ ^ 2) ≤
      ∏ i : Fin N, ((1 + ‖X i‖) ^ k * Real.exp (-(beta * a / 2) * ‖X i‖ ^ 2)) := by
    rw [Finset.prod_mul_distrib]
    exact mul_le_mul_of_nonneg_right (hpow1.trans hpowk) hE1nn
  -- assemble
  have hE1' : 0 ≤ (1 + ‖X‖) ^ (2 * M) := by positivity
  set P := ∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, (1 + ‖X i - X j‖ ^ (-M)) ^ 2 with hP
  set E2 := ∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, Real.exp (-(beta / (2 * N)) * ‖X i - X j‖ ^ (-s)) with hE2
  set E1' := ∏ i : Fin N, Real.exp (-(beta * a / 2) * ‖X i‖ ^ 2) with hE1d
  set K0 := ∏ i : Fin N, ∏ j ∈ Finset.univ.erase i, K with hK0d
  set Pi := ∏ i : Fin N, ((1 + ‖X i‖) ^ k * Real.exp (-(beta * a / 2) * ‖X i‖ ^ 2)) with hPi
  have hK0nn : 0 ≤ K0 := Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => hK0
  rw [hE1]
  calc (E1' * E2 * ((1 + ‖X‖) ^ (2 * M) * P)) = ((1 + ‖X‖) ^ (2 * M) * E1') * (P * E2) := by ring
    _ ≤ ((1 + ‖X‖) ^ (2 * M) * E1') * K0 := mul_le_mul_of_nonneg_left hQ (by positivity)
    _ = K0 * ((1 + ‖X‖) ^ (2 * M) * E1') := by ring
    _ ≤ K0 * Pi := mul_le_mul_of_nonneg_left hkey hK0nn

end HRS.MS.R26T8A

end
