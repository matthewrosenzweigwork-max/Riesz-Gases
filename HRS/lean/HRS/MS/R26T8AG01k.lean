import HRS.MS.R26T8AG01j

/-!
# S8.2 observed-time layer, packet T8A.G01 (helper k): spatial product and envelope comparison

The spatial product `S_n X = ∏_i (1 - ψ(m⁻² ‖X i‖²))` has derivatives bounded uniformly in `n`, and the inverse
distances `1/‖X i - X j‖` are dominated by the pole envelope `configPoleEnvelope 2` (with squares by the envelope).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_g01k_S {d N : ℕ} {K1 K2 Λ0 : ℝ}
    (hK1 : ∀ t : ℝ, |deriv r26t8a_g01a_psi t| ≤ K1) (hK2 : ∀ t : ℝ, |deriv (deriv r26t8a_g01a_psi) t| ≤ K2)
    (hK1n : 0 ≤ K1) (hK2n : 0 ≤ K2) (hΛ0 : 0 ≤ Λ0)
    (hp : ∀ i : Fin N, ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i‖ ≤ Λ0)
    (n : ℕ) (X : EucConfig d N) :
    ‖iteratedFDeriv ℝ 1 (fun y : EucConfig d N => ∏ i : Fin N,
        (1 - r26t8a_g01a_psi (((n : ℝ) + 1)⁻¹ ^ 2 * ‖y i‖ ^ 2))) X‖ ≤ (N : ℝ) * (8 * K1 * Λ0) ∧
    ‖iteratedFDeriv ℝ 2 (fun y : EucConfig d N => ∏ i : Fin N,
        (1 - r26t8a_g01a_psi (((n : ℝ) + 1)⁻¹ ^ 2 * ‖y i‖ ^ 2))) X‖ ≤
      (N : ℝ) * ((8 * K1 + 64 * K2) * Λ0 ^ 2) + ((N : ℝ) * (8 * K1 * Λ0)) ^ 2 := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := by positivity
    linarith
  have hfac := fun i : Fin N => r26t8a_g01i_spatial hK1 hK2 hK1n hK2n n i X
  have hval : ∀ i : Fin N, |1 - r26t8a_g01a_psi (((n : ℝ) + 1)⁻¹ ^ 2 * ‖X i‖ ^ 2)| ≤ 1 := by
    intro i
    have h0 := r26t8a_g01a_nonneg (((n : ℝ) + 1)⁻¹ ^ 2 * ‖X i‖ ^ 2)
    have h1 := r26t8a_g01a_le_one (((n : ℝ) + 1)⁻¹ ^ 2 * ‖X i‖ ^ 2)
    rw [abs_le]
    constructor <;> linarith
  have hd := r26t8a_g01d_prod (ι := Fin N) Finset.univ
    (fun i (y : EucConfig d N) => 1 - r26t8a_g01a_psi (((n : ℝ) + 1)⁻¹ ^ 2 * ‖y i‖ ^ 2))
    (fun i => by
      have hL : ContDiff ℝ ∞ (fun y : EucConfig d N => ‖y i‖ ^ 2) :=
        (contDiff_norm_sq ℝ).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i).contDiff
      exact contDiff_const.sub (r26t8a_g01a_contDiff.comp (contDiff_const.mul hL))) X hval
  obtain ⟨d1, d2⟩ := hd
  have hb1 : ∀ i : Fin N, ‖iteratedFDeriv ℝ 1 (fun y : EucConfig d N =>
      1 - r26t8a_g01a_psi (((n : ℝ) + 1)⁻¹ ^ 2 * ‖y i‖ ^ 2)) X‖ ≤ 8 * K1 * Λ0 := fun i =>
    (hfac i).1.trans (mul_le_mul_of_nonneg_left (hp i) (by positivity))
  have hb2 : ∀ i : Fin N, ‖iteratedFDeriv ℝ 2 (fun y : EucConfig d N =>
      1 - r26t8a_g01a_psi (((n : ℝ) + 1)⁻¹ ^ 2 * ‖y i‖ ^ 2)) X‖ ≤ (8 * K1 + 64 * K2) * Λ0 ^ 2 := fun i =>
    (hfac i).2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (hp i) 2) (by positivity))
  constructor
  · refine d1.trans ?_
    calc ∑ i : Fin N, ‖iteratedFDeriv ℝ 1 (fun y : EucConfig d N =>
          1 - r26t8a_g01a_psi (((n : ℝ) + 1)⁻¹ ^ 2 * ‖y i‖ ^ 2)) X‖
        ≤ ∑ _i : Fin N, 8 * K1 * Λ0 := Finset.sum_le_sum fun i _ => hb1 i
      _ = (N : ℝ) * (8 * K1 * Λ0) := by simp
  · refine d2.trans ?_
    have hs1 : ∑ i : Fin N, ‖iteratedFDeriv ℝ 1 (fun y : EucConfig d N =>
          1 - r26t8a_g01a_psi (((n : ℝ) + 1)⁻¹ ^ 2 * ‖y i‖ ^ 2)) X‖ ≤ (N : ℝ) * (8 * K1 * Λ0) := by
      calc _ ≤ ∑ _i : Fin N, 8 * K1 * Λ0 := Finset.sum_le_sum fun i _ => hb1 i
        _ = (N : ℝ) * (8 * K1 * Λ0) := by simp
    have hs0 : 0 ≤ ∑ i : Fin N, ‖iteratedFDeriv ℝ 1 (fun y : EucConfig d N =>
          1 - r26t8a_g01a_psi (((n : ℝ) + 1)⁻¹ ^ 2 * ‖y i‖ ^ 2)) X‖ :=
      Finset.sum_nonneg fun i _ => norm_nonneg _
    have hs2 : ∑ i : Fin N, ‖iteratedFDeriv ℝ 2 (fun y : EucConfig d N =>
          1 - r26t8a_g01a_psi (((n : ℝ) + 1)⁻¹ ^ 2 * ‖y i‖ ^ 2)) X‖ ≤ (N : ℝ) * ((8 * K1 + 64 * K2) * Λ0 ^ 2) := by
      calc _ ≤ ∑ _i : Fin N, (8 * K1 + 64 * K2) * Λ0 ^ 2 := Finset.sum_le_sum fun i _ => hb2 i
        _ = (N : ℝ) * ((8 * K1 + 64 * K2) * Λ0 ^ 2) := by simp
    have := pow_le_pow_left₀ hs0 hs1 2
    linarith

/-- the inverse distances are dominated by the pole envelope (and their squares) -/
theorem r26t8a_g01k_env {d N : ℕ} (X : EucConfig d N) (i j : Fin N) (hij : i ≠ j) :
    1 / ‖X i - X j‖ ≤ 2 * configPoleEnvelope 2 X ∧ (1 / ‖X i - X j‖) ^ 2 ≤ configPoleEnvelope 2 X := by
  have hpair := r26t8a_g01h_env_pair d N X i j hij
  have h1 := r26t8a_g01h_env_one_le d N X
  have hsq : (1 / ‖X i - X j‖) ^ 2 = ‖X i - X j‖ ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg (norm_nonneg _), Real.rpow_two, one_div_pow, one_div]
  have hpos : 0 ≤ (1 / ‖X i - X j‖) ^ 2 := sq_nonneg _
  have hsq' : (1 / ‖X i - X j‖) ^ 2 ≤ configPoleEnvelope 2 X := by
    rw [hsq]
    linarith [Real.rpow_nonneg (norm_nonneg (X i - X j)) (-(2 : ℝ))]
  refine ⟨?_, hsq'⟩
  have hA0 : 0 ≤ 1 / ‖X i - X j‖ := by positivity
  nlinarith [sq_nonneg (1 / ‖X i - X j‖ - 1)]

end HRS.MS.R26T8A

end
