import HRS.MS.SuppU2Aux8

/-!
# U2 auxiliary 9: the core decay theorem and the kernel instance
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.Whole

variable {d : ℕ}

lemma u2_cmp {u v p : ℝ} (hu : 0 < u) (hv : 0 < v) (h : v ≤ 2 * u) (hp : 0 ≤ p) :
    u ^ (-p) ≤ 2 ^ p * v ^ (-p) := by
  have h1 : v / 2 ≤ u := by linarith
  have h2 := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < v / 2) h1 (by linarith : -p ≤ 0)
  refine h2.trans (le_of_eq ?_)
  rw [Real.div_rpow hv.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
    Real.rpow_neg hv.le]
  field_simp

theorem u2_core {κ : Euc d → ℝ} {a : ℝ} (hK : U2KerFull κ a) (k : ℕ) {L : ℝ}
    (hL : (d : ℝ) + k + a + 2 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ) (h : Euc d → ℝ), 0 ≤ A → U2Dec k L A h →
      ContDiff ℝ k (u2Conv κ h) ∧ ∀ j ≤ k, ∀ x : Euc d,
        ‖iteratedFDeriv ℝ j (u2Conv κ h) x‖ ≤ C * A * (1 + ‖x‖) ^ (-(a + j)) := by
  have hker := hK.ker
  have ha := hker.a_nonneg
  have hdL : (d : ℝ) < L := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  obtain ⟨Cf, hCf0, hCf⟩ := u2_far hK k hL
  obtain ⟨Cu, hCu0, hCu⟩ := u2_conv_norm_le hker hdL
  refine ⟨(Cf + Cu) * 2 ^ (a + (k : ℝ)), by positivity, ?_⟩
  intro A h hA hdec
  obtain ⟨hF_iter, hF_cd⟩ := u2_conv_iter hker hdL hA hdec
  refine ⟨hF_cd, fun j hj x => ?_⟩
  have hp : 0 ≤ a + (j : ℝ) := by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
  have h2p : (2 : ℝ) ^ (a + (j : ℝ)) ≤ 2 ^ (a + (k : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have : (j : ℝ) ≤ k := by exact_mod_cast hj
    linarith
  have hv : 0 < 1 + ‖x‖ := by positivity
  have hvp : 0 ≤ (1 + ‖x‖) ^ (-(a + (j : ℝ))) := Real.rpow_nonneg hv.le _
  have hCC : (0 : ℝ) ≤ 2 ^ (a + (k : ℝ)) := by positivity
  by_cases hx : 1 ≤ ‖x‖
  · have h1 := hCf A h hA hdec x hx j hj
    have h3 := u2_cmp (by linarith : 0 < ‖x‖) hv (by linarith) hp
    calc ‖iteratedFDeriv ℝ j (u2Conv κ h) x‖ ≤ Cf * A * ‖x‖ ^ (-(a + (j : ℝ))) := h1
      _ ≤ Cf * A * (2 ^ (a + (j : ℝ)) * (1 + ‖x‖) ^ (-(a + (j : ℝ)))) :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg hCf0 hA)
      _ ≤ Cf * A * (2 ^ (a + (k : ℝ)) * (1 + ‖x‖) ^ (-(a + (j : ℝ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2p hvp) (mul_nonneg hCf0 hA)
      _ ≤ (Cf + Cu) * 2 ^ (a + (k : ℝ)) * A * (1 + ‖x‖) ^ (-(a + (j : ℝ))) := by
          have : Cf * A * (2 ^ (a + (k : ℝ)) * (1 + ‖x‖) ^ (-(a + (j : ℝ)))) =
              Cf * 2 ^ (a + (k : ℝ)) * A * (1 + ‖x‖) ^ (-(a + (j : ℝ))) := by ring
          rw [this]
          have h4 : Cf * 2 ^ (a + (k : ℝ)) ≤ (Cf + Cu) * 2 ^ (a + (k : ℝ)) :=
            mul_le_mul_of_nonneg_right (by linarith) hCC
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4 hA) hvp
  · push Not at hx
    rw [hF_iter j hj x]
    have hcm : Continuous (iteratedFDeriv ℝ j h) :=
      hdec.1.continuous_iteratedFDeriv (by exact_mod_cast hj)
    have h1 : ‖u2Conv κ (iteratedFDeriv ℝ j h) x‖ ≤ Cu * A :=
      hCu _ (iteratedFDeriv ℝ j h) A hA (hdec.2 j hj) x
    have h3 := u2_cmp (by norm_num : (0:ℝ) < 1) hv (by linarith) hp
    rw [Real.one_rpow] at h3
    calc ‖u2Conv κ (iteratedFDeriv ℝ j h) x‖ ≤ Cu * A := h1
      _ ≤ Cu * A * (2 ^ (a + (j : ℝ)) * (1 + ‖x‖) ^ (-(a + (j : ℝ)))) := by
          have : 0 ≤ Cu * A := mul_nonneg hCu0 hA
          nlinarith
      _ ≤ Cu * A * (2 ^ (a + (k : ℝ)) * (1 + ‖x‖) ^ (-(a + (j : ℝ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2p hvp) (mul_nonneg hCu0 hA)
      _ ≤ (Cf + Cu) * 2 ^ (a + (k : ℝ)) * A * (1 + ‖x‖) ^ (-(a + (j : ℝ))) := by
          have : Cu * A * (2 ^ (a + (k : ℝ)) * (1 + ‖x‖) ^ (-(a + (j : ℝ)))) =
              Cu * 2 ^ (a + (k : ℝ)) * A * (1 + ‖x‖) ^ (-(a + (j : ℝ))) := by ring
          rw [this]
          have h4 : Cu * 2 ^ (a + (k : ℝ)) ≤ (Cf + Cu) * 2 ^ (a + (k : ℝ)) :=
            mul_le_mul_of_nonneg_right (by linarith) hCC
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4 hA) hvp

end HRS.Whole
