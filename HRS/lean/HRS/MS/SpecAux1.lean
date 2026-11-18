import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# S8P: quasi-compact perturbations (generic operator theory for S8.3)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  Over `ℂ`:

* `s8p_quasi_compact_resolvent`: if `S = K + R` with `K` compact and `‖R‖ < ‖λ‖`, then `λ` is an eigenvalue of `S`
  or lies in the resolvent set (Fredholm alternative for `(λ - R)⁻¹ K`);
* `s8p_geometric_decay`: if moreover every eigenvalue of `S` has modulus `≤ θ` with `‖R‖ ≤ θ < θ' < 1`,
  then `‖S^n‖ ≤ C θ'^n` (Gelfand's formula).
-/

noncomputable section

open Filter Topology Module
open scoped ENNReal NNReal

namespace HRS.MS.Spec

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Fredholm alternative for `K + R`, `K` compact, `‖R‖ < ‖λ‖`. -/
theorem s8p_quasi_compact_resolvent (K R : X →L[ℂ] X) (hK : IsCompactOperator K) {lam : ℂ}
    (hlam : ‖R‖ < ‖lam‖) :
    Module.End.HasEigenvalue ((K + R : X →L[ℂ] X) : Module.End ℂ X) lam ∨
      lam ∈ resolventSet ℂ (K + R) := by
  have hlam0 : lam ≠ 0 := by
    intro h; rw [h, norm_zero] at hlam; exact absurd hlam (not_lt.2 (norm_nonneg _))
  have hR : lam ∈ resolventSet ℂ R := by
    refine spectrum.mem_resolventSet_of_norm_lt_mul ?_
    calc ‖R‖ * ‖(1 : X →L[ℂ] X)‖ ≤ ‖R‖ * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
      _ < ‖lam‖ := by rwa [mul_one]
  rw [spectrum.mem_resolventSet_iff] at hR
  obtain ⟨u, hu⟩ := hR
  set G : X →L[ℂ] X := ↑u⁻¹ with hG
  have hGu : (u : X →L[ℂ] X) * G = 1 := by rw [hG]; exact u.mul_inv
  have hGu' : G * (u : X →L[ℂ] X) = 1 := by rw [hG]; exact u.inv_mul
  have hT : IsCompactOperator (G * K) := hK.clm_comp G
  have hlu : ((u : X →L[ℂ] X) : X →L[ℂ] X) = algebraMap ℂ (X →L[ℂ] X) lam - R := hu
  rcases hT.hasEigenvalue_or_mem_resolventSet (μ := (1 : ℂ)) one_ne_zero with h | h
  · left
    obtain ⟨x, hx⟩ := h.exists_hasEigenvector
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hx
    obtain ⟨hx1, hx0⟩ := hx
    have h1 : G (K x) = x := by simpa using hx1
    have h2 : K x = lam • x - R x := by
      have h3 : K x = (u : X →L[ℂ] X) x := by
        calc K x = ((u : X →L[ℂ] X) * G) (K x) := by rw [hGu]; rfl
          _ = (u : X →L[ℂ] X) (G (K x)) := rfl
          _ = (u : X →L[ℂ] X) x := by rw [h1]
      rw [h3, hlu]
      simp [Algebra.algebraMap_eq_smul_one]
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := x) ?_
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    refine ⟨?_, hx0⟩
    show (K + R) x = lam • x
    rw [add_apply, h2]; abel
  · right
    rw [spectrum.mem_resolventSet_iff] at h ⊢
    have e : algebraMap ℂ (X →L[ℂ] X) lam - (K + R) = (u : X →L[ℂ] X) * (algebraMap ℂ (X →L[ℂ] X) 1 - G * K) := by
      rw [mul_sub, ← mul_assoc, hGu]
      rw [hlu]; simp; abel
    rw [e]
    exact (Units.isUnit u).mul h

end HRS.MS.Spec
