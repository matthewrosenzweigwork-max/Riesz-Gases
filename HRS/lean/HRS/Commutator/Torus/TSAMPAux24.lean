import HRS.Commutator.Torus.TSAMPAux23

/-!
# T-SAMP helpers, part 24: sampling for kernels with a power profile
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma tsamp_Zq_pow {p q : ℝ} (hpq : p.HolderConjugate q) {η C Ia a γ : ℝ} (hη : 0 < η) (hC : 0 ≤ C)
    (hIa : 0 ≤ Ia) :
    ((C * η ^ (γ - d - a)) ^ q * η ^ (a * q) * η ^ d * Ia) ^ (p - 1) =
      C ^ p * Ia ^ (p - 1) * η ^ (p * (γ - d) + d * (p - 1)) := by
  have hp1 : 1 < p := hpq.lt
  have hqp : q * (p - 1) = p := by
    have h := hpq.inv_add_inv_eq_one
    have hp0 : p ≠ 0 := by linarith
    have hq0 : q ≠ 0 := hpq.symm.pos.ne'
    field_simp at h
    nlinarith [h]
  have e1 : ((C * η ^ (γ - d - a)) ^ q * η ^ (a * q) * η ^ d * Ia) =
      C ^ q * Ia * η ^ ((γ - d) * q + d) := by
    rw [Real.mul_rpow hC (Real.rpow_nonneg hη.le _), ← Real.rpow_mul hη.le,
      ← Real.rpow_natCast η d]
    have : η ^ ((γ - d - a) * q) * η ^ (a * q) * η ^ (d : ℝ) = η ^ ((γ - d) * q + d) := by
      rw [← Real.rpow_add hη, ← Real.rpow_add hη]; congr 1; ring
    calc C ^ q * η ^ ((γ - d - a) * q) * η ^ (a * q) * η ^ (d : ℝ) * Ia
        = C ^ q * Ia * (η ^ ((γ - d - a) * q) * η ^ (a * q) * η ^ (d : ℝ)) := by ring
      _ = C ^ q * Ia * η ^ ((γ - d) * q + d) := by rw [this]
  rw [e1, Real.mul_rpow (mul_nonneg (Real.rpow_nonneg hC _) hIa) (Real.rpow_nonneg hη.le _),
    Real.mul_rpow (Real.rpow_nonneg hC _) hIa, ← Real.rpow_mul hC, ← Real.rpow_mul hη.le, hqp]
  congr 2
  have : (γ - d) * q * (p - 1) = (γ - d) * p := by rw [mul_assoc, hqp]
  nlinarith [this]

end HRS.Commutator.TorusNote
