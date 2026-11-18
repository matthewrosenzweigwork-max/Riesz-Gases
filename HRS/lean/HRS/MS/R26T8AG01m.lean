import HRS.MS.R26T8AG01l
import HRS.MS.R26T8AG01g

/-!
# S8.2 observed-time layer, packet T8A.G01 (helper m): the graph cutoff is bounded by the pole envelope

For all `n`, `‖∂θ_n X‖ + ‖∂²θ_n X‖ ≤ C · configPoleEnvelope 2 X` with `C` independent of `n` and `X`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_g01m_theta_bd (d N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (X : EucConfig d N), X ∉ eucCollisionSet d N →
      ‖iteratedFDeriv ℝ 1 (r26t8a_g01_theta d N n) X‖ + ‖iteratedFDeriv ℝ 2 (r26t8a_g01_theta d N n) X‖ ≤
        C * configPoleEnvelope 2 X := by
  obtain ⟨K1, K2, hK1n, hK2n, hK⟩ := r26t8a_g01a_deriv_bdd
  have hK1 : ∀ t : ℝ, |deriv r26t8a_g01a_psi t| ≤ K1 := fun t => (hK t).1
  have hK2 : ∀ t : ℝ, |deriv (deriv r26t8a_g01a_psi) t| ≤ K2 := fun t => (hK t).2
  set Λ : ℝ := ∑ i : Fin N, ∑ j : Fin N, ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i -
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) j‖ with hΛdef
  have hΛ : ∀ i j : Fin N, ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i -
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) j‖ ≤ Λ := by
    intro i j
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j : Fin N, ‖ContinuousLinearMap.proj
      (R := ℝ) (φ := fun _ : Fin N => Euc d) i - ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) j‖)
      (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i -
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) j‖) (fun j _ => norm_nonneg _)
      (Finset.mem_univ j)
  have hΛ0 : 0 ≤ Λ := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  set Λ0 : ℝ := ∑ i : Fin N, ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i‖ with hΛ0def
  have hp : ∀ i : Fin N, ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i‖ ≤ Λ0 :=
    fun i => Finset.single_le_sum (f := fun i => ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i‖)
      (fun i _ => norm_nonneg _) (Finset.mem_univ i)
  have hΛ0' : 0 ≤ Λ0 := Finset.sum_nonneg fun i _ => norm_nonneg _
  obtain ⟨Cc, hCc⟩ : ∃ Cc : ℝ, Cc =
      ((N : ℝ) * (8 * K1 * Λ0) + ((N : ℝ) * ((8 * K1 + 64 * K2) * Λ0 ^ 2) + ((N : ℝ) * (8 * K1 * Λ0)) ^ 2)) +
      ((8 * K1 * Λ) + 2 * ((N : ℝ) * (8 * K1 * Λ0)) * (8 * K1 * Λ)) * (2 * (N : ℝ) * (N : ℝ)) +
      ((8 * K1 + 64 * K2) * Λ ^ 2) * ((N : ℝ) * (N : ℝ)) + ((N : ℝ) + 1) * (8 * K1 * Λ) ^ 2 * ((N : ℝ) ^ 4) :=
    ⟨_, rfl⟩
  refine ⟨|Cc|, abs_nonneg _, fun n X _ => ?_⟩
  -- the two factors
  set S : EucConfig d N → ℝ := fun y => ∏ i : Fin N, (1 - r26t8a_g01a_psi (((n : ℝ) + 1)⁻¹ ^ 2 * ‖y i‖ ^ 2))
    with hSdef
  set P : EucConfig d N → ℝ := fun y => ∏ i : Fin N, ∏ j ∈ Finset.univ.filter (fun j => i < j),
    r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖y i - y j‖ ^ 2) with hPdef
  have hθ : r26t8a_g01_theta d N n = fun y => S y * P y := rfl
  have hSc : ContDiff ℝ ∞ S := by
    refine contDiff_prod fun i _ => ?_
    have hL : ContDiff ℝ ∞ (fun y : EucConfig d N => ‖y i‖ ^ 2) :=
      (contDiff_norm_sq ℝ).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i).contDiff
    exact contDiff_const.sub (r26t8a_g01a_contDiff.comp (contDiff_const.mul hL))
  have hPc : ContDiff ℝ ∞ P := by
    refine contDiff_prod fun i _ => contDiff_prod fun j _ => ?_
    have hL : ContDiff ℝ ∞ (fun y : EucConfig d N => ‖y i - y j‖ ^ 2) :=
      (contDiff_norm_sq ℝ).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i -
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) j).contDiff)
    exact r26t8a_g01a_contDiff.comp (contDiff_const.mul hL)
  have hS01 : 0 ≤ S X ∧ S X ≤ 1 := by
    have hS : ∀ i : Fin N, 0 ≤ 1 - r26t8a_g01a_psi (((n : ℝ) + 1)⁻¹ ^ 2 * ‖X i‖ ^ 2) ∧
        1 - r26t8a_g01a_psi (((n : ℝ) + 1)⁻¹ ^ 2 * ‖X i‖ ^ 2) ≤ 1 := fun i =>
      ⟨by linarith [r26t8a_g01a_le_one (((n : ℝ) + 1)⁻¹ ^ 2 * ‖X i‖ ^ 2)],
        by linarith [r26t8a_g01a_nonneg (((n : ℝ) + 1)⁻¹ ^ 2 * ‖X i‖ ^ 2)]⟩
    exact ⟨Finset.prod_nonneg fun i _ => (hS i).1, Finset.prod_le_one₀ (fun i _ => (hS i).1) fun i _ => (hS i).2⟩
  have hP01 : 0 ≤ P X ∧ P X ≤ 1 := by
    have hP : ∀ i j : Fin N, 0 ≤ r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖X i - X j‖ ^ 2) ∧
        r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖X i - X j‖ ^ 2) ≤ 1 := fun i j =>
      ⟨r26t8a_g01a_nonneg _, r26t8a_g01a_le_one _⟩
    exact ⟨Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => (hP i j).1,
      Finset.prod_le_one₀ (fun i _ => Finset.prod_nonneg fun j _ => (hP i j).1)
        fun i _ => Finset.prod_le_one₀ (fun j _ => (hP i j).1) fun j _ => (hP i j).2⟩
  -- derivative bounds of the factors
  obtain ⟨hPd1, hPd2⟩ := r26t8a_g01j_P hK1 hK2 hK1n hK2n hΛ0 hΛ n X
  obtain ⟨hSd1, hSd2⟩ := r26t8a_g01k_S hK1 hK2 hK1n hK2n hΛ0' hp n X
  rw [← hPdef] at hPd1 hPd2
  rw [← hSdef] at hSd1 hSd2
  -- Leibniz for θ = S · P
  obtain ⟨hL1, hL2⟩ := r26t8a_g01c_mul hSc hPc X
  rw [← hθ] at hL1 hL2
  have hsa : ‖S X‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hS01.1]; exact hS01.2
  have hpa : ‖P X‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hP01.1]; exact hP01.2
  have hnS : 0 ≤ ‖S X‖ := norm_nonneg _
  have hnP : 0 ≤ ‖P X‖ := norm_nonneg _
  -- envelope sums
  have hc1 : 0 ≤ 8 * K1 * Λ := by have := mul_nonneg hK1n hΛ0; linarith
  have hA := (r26t8a_g01l_sums X).1
  have hQ := (r26t8a_g01l_sums X).2.1
  have hA2 := (r26t8a_g01l_sums X).2.2
  have henv1 := r26t8a_g01h_env_one_le d N X
  have hc2 : 0 ≤ (8 * K1 + 64 * K2) * Λ ^ 2 := by
    have := mul_nonneg (by linarith : (0:ℝ) ≤ 8 * K1 + 64 * K2) (sq_nonneg Λ); linarith
  have hCS0 : 0 ≤ (N : ℝ) * (8 * K1 * Λ0) := mul_nonneg (Nat.cast_nonneg _) (by
    have := mul_nonneg hK1n hΛ0'; linarith)
  have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  -- the first and second derivatives of θ
  have T1 : ‖iteratedFDeriv ℝ 1 (r26t8a_g01_theta d N n) X‖ ≤ 8 * K1 * Λ *
      (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖X i - X j‖) +
        (N : ℝ) * (8 * K1 * Λ0) := by
    have e1 : ‖S X‖ * ‖iteratedFDeriv ℝ 1 P X‖ ≤ ‖iteratedFDeriv ℝ 1 P X‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hsa
    have e2 : ‖iteratedFDeriv ℝ 1 S X‖ * ‖P X‖ ≤ ‖iteratedFDeriv ℝ 1 S X‖ :=
      mul_le_of_le_one_right (norm_nonneg _) hpa
    linarith [hL1, hPd1, hSd1, e1, e2]
  have T2 : ‖iteratedFDeriv ℝ 2 (r26t8a_g01_theta d N n) X‖ ≤
      (8 * K1 + 64 * K2) * Λ ^ 2 * (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), (1 / ‖X i - X j‖) ^ 2) +
        ((N : ℝ) + 1) * (8 * K1 * Λ * (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖X i - X j‖)) ^ 2 +
        2 * ((N : ℝ) * (8 * K1 * Λ0)) * (8 * K1 * Λ * (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖X i - X j‖)) +
        ((N : ℝ) * ((8 * K1 + 64 * K2) * Λ0 ^ 2) + ((N : ℝ) * (8 * K1 * Λ0)) ^ 2) := by
    have e1 : ‖S X‖ * ‖iteratedFDeriv ℝ 2 P X‖ ≤ ‖iteratedFDeriv ℝ 2 P X‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hsa
    have e2 : ‖iteratedFDeriv ℝ 2 S X‖ * ‖P X‖ ≤ ‖iteratedFDeriv ℝ 2 S X‖ :=
      mul_le_of_le_one_right (norm_nonneg _) hpa
    have e3 : 2 * ‖iteratedFDeriv ℝ 1 S X‖ * ‖iteratedFDeriv ℝ 1 P X‖ ≤
        2 * ((N : ℝ) * (8 * K1 * Λ0)) * (8 * K1 * Λ * (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖X i - X j‖)) := by
      have hx : ‖iteratedFDeriv ℝ 1 S X‖ * ‖iteratedFDeriv ℝ 1 P X‖ ≤
          ((N : ℝ) * (8 * K1 * Λ0)) * (8 * K1 * Λ * (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖X i - X j‖)) :=
        mul_le_mul hSd1 hPd1 (norm_nonneg _) hCS0
      nlinarith
    linarith [hL2, hPd2, hSd2, e1, e2, e3]
  -- the final estimate
  have hE1 := henv1
  generalize hAg : (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖X i - X j‖) = A at T1 T2 hA hA2
  generalize hQg : (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), (1 / ‖X i - X j‖) ^ 2) = Q at T2 hQ hA2
  generalize hEg : configPoleEnvelope 2 X = E at hA hQ hA2 hE1 ⊢
  have hA0 : 0 ≤ A := by
    have : 0 ≤ ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖X i - X j‖ :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
    rw [hAg] at this
    exact this
  have hQ0 : 0 ≤ Q := by
    have : 0 ≤ ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), (1 / ‖X i - X j‖) ^ 2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
    rw [hQg] at this
    exact this
  have hAsq : A ^ 2 ≤ (N : ℝ) ^ 4 * E := by
    have h1 : (N : ℝ) ^ 2 * Q ≤ (N : ℝ) ^ 2 * ((N : ℝ) * (N : ℝ) * E) :=
      mul_le_mul_of_nonneg_left hQ (sq_nonneg _)
    exact hA2.trans (h1.trans_eq (by ring))
  have hCS0' : 0 ≤ (N : ℝ) * (8 * K1 * Λ0) := hCS0
  have hCS2nn : 0 ≤ (N : ℝ) * ((8 * K1 + 64 * K2) * Λ0 ^ 2) + ((N : ℝ) * (8 * K1 * Λ0)) ^ 2 := by
    have : 0 ≤ (N : ℝ) * ((8 * K1 + 64 * K2) * Λ0 ^ 2) := mul_nonneg hNn (mul_nonneg
      (by linarith : (0 : ℝ) ≤ 8 * K1 + 64 * K2) (sq_nonneg _))
    exact add_nonneg this (sq_nonneg _)
  have hEge : 1 ≤ E := hE1
  have hEnn : 0 ≤ E := zero_le_one.trans hEge
  have hsum : ‖iteratedFDeriv ℝ 1 (r26t8a_g01_theta d N n) X‖ + ‖iteratedFDeriv ℝ 2 (r26t8a_g01_theta d N n) X‖ ≤
      Cc * E := by
    rw [hCc]
    have b1 : 8 * K1 * Λ * A ≤ 8 * K1 * Λ * ((N : ℝ) * (N : ℝ) * (2 * E)) :=
      mul_le_mul_of_nonneg_left hA hc1
    have b2 : (8 * K1 + 64 * K2) * Λ ^ 2 * Q ≤ (8 * K1 + 64 * K2) * Λ ^ 2 * ((N : ℝ) * (N : ℝ) * E) :=
      mul_le_mul_of_nonneg_left hQ hc2
    have b3 : ((N : ℝ) + 1) * (8 * K1 * Λ * A) ^ 2 ≤
        ((N : ℝ) + 1) * (8 * K1 * Λ) ^ 2 * ((N : ℝ) ^ 4 * E) := by
      have e : (8 * K1 * Λ * A) ^ 2 = (8 * K1 * Λ) ^ 2 * A ^ 2 := by ring
      rw [e]
      have hsq : (8 * K1 * Λ) ^ 2 * A ^ 2 ≤ (8 * K1 * Λ) ^ 2 * ((N : ℝ) ^ 4 * E) :=
        mul_le_mul_of_nonneg_left hAsq (sq_nonneg _)
      calc ((N : ℝ) + 1) * ((8 * K1 * Λ) ^ 2 * A ^ 2)
          ≤ ((N : ℝ) + 1) * ((8 * K1 * Λ) ^ 2 * ((N : ℝ) ^ 4 * E)) :=
            mul_le_mul_of_nonneg_left hsq (by linarith)
        _ = ((N : ℝ) + 1) * (8 * K1 * Λ) ^ 2 * ((N : ℝ) ^ 4 * E) := by ring
    have hx0 : 0 ≤ 2 * ((N : ℝ) * (8 * K1 * Λ0)) := by linarith
    have b4 : 2 * ((N : ℝ) * (8 * K1 * Λ0)) * (8 * K1 * Λ * A) ≤
        2 * ((N : ℝ) * (8 * K1 * Λ0)) * (8 * K1 * Λ) * ((N : ℝ) * (N : ℝ) * (2 * E)) := by
      calc 2 * ((N : ℝ) * (8 * K1 * Λ0)) * (8 * K1 * Λ * A)
          = (2 * ((N : ℝ) * (8 * K1 * Λ0))) * (8 * K1 * Λ * A) := rfl
        _ ≤ (2 * ((N : ℝ) * (8 * K1 * Λ0))) * (8 * K1 * Λ * ((N : ℝ) * (N : ℝ) * (2 * E))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA hc1) hx0
        _ = 2 * ((N : ℝ) * (8 * K1 * Λ0)) * (8 * K1 * Λ) * ((N : ℝ) * (N : ℝ) * (2 * E)) := by ring
    have b5 : (N : ℝ) * (8 * K1 * Λ0) ≤ (N : ℝ) * (8 * K1 * Λ0) * E :=
      le_mul_of_one_le_right hCS0' hEge
    have b6 : (N : ℝ) * ((8 * K1 + 64 * K2) * Λ0 ^ 2) + ((N : ℝ) * (8 * K1 * Λ0)) ^ 2 ≤
        ((N : ℝ) * ((8 * K1 + 64 * K2) * Λ0 ^ 2) + ((N : ℝ) * (8 * K1 * Λ0)) ^ 2) * E :=
      le_mul_of_one_le_right hCS2nn hEge
    linarith [T1, T2, b1, b2, b3, b4, b5, b6]
  calc ‖iteratedFDeriv ℝ 1 (r26t8a_g01_theta d N n) X‖ + ‖iteratedFDeriv ℝ 2 (r26t8a_g01_theta d N n) X‖
      ≤ Cc * E := hsum
    _ ≤ |Cc| * E := mul_le_mul_of_nonneg_right (le_abs_self _) hEnn

end HRS.MS.R26T8A

end
