import HRS.MS.SA16TAp2
import HRS.MS.SA16TGc5
import HRS.MS.SA16TEn2

/-!
# S.A.16 (SA16T) Ap3: helper lemmas for the approximating problems

`sa16t_nu`: the viscosity `ν_n = ν + 1/(n+1)`.  `sa16t_mu_cont`, `sa16t_mu_bdd`: joint continuity and sup bound of `μ` under
`CoeffHypRd`.  `sa16t_bound_from_energy`: norm bound from the `p`-th power energy bound.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16P Phase2SA16Evolution Phase2SA16Transfer

section Ap3
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- the viscosity of the `n`-th approximating problem -/
def sa16t_nu (D : WholeDyn d) (n : ℕ) : ℝ := D.invβ + 1 / ((n : ℝ) + 1)

lemma sa16t_nu_pos {D : WholeDyn d} (h : 0 ≤ D.invβ) (n : ℕ) : 0 < sa16t_nu D n := by
  unfold sa16t_nu; positivity

lemma sa16t_mu_cont (hd : 1 ≤ d) {s Λ T : ℝ} {m : ℕ} {μ : ℝ → Euc d → ℝ} (hT : 0 ≤ T) (hμ : CoeffHypRd s m Λ T μ) :
    ContinuousOn (fun q : ℝ × Euc d => μ q.1 q.2) (Icc (0 : ℝ) T ×ˢ univ) := by
  have h0 := (coefficient_time_regular d m hd s Λ T hT μ hμ).1 0 (by omega)
  have : (fun q : ℝ × Euc d => μ q.1 q.2) =
      fun q => (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ) (iteratedFDeriv ℝ 0 (μ q.1) q.2) := by
    funext q; rw [iteratedFDeriv_zero_eq_comp]; simp
  rw [this]
  exact (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).continuous.comp_continuousOn h0

lemma sa16t_mu_bdd {s Λ T : ℝ} {m : ℕ} {μ : ℝ → Euc d → ℝ} (hμ : CoeffHypRd s m Λ T μ) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) T) (y : Euc d) : |μ r y| ≤ Λ := by
  have := e14_bnd hμ hr (j := 0) (Nat.zero_le _) y
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this

lemma sa16t_bound_from_energy {E0 E : ℝ} {c a b Cj τ : ℝ} (hp : 0 < p) (hE0 : 0 ≤ E0) (hE : 0 ≤ E)
    (hle : E ≤ E0 * Real.exp (c * τ)) (ha : a ≤ E ^ (1 / p)) (hb : E0 ^ (1 / p) ≤ Cj * b) (hCj : 0 ≤ Cj) :
    a ≤ Cj * Real.exp (c / p * τ) * b := by
  have h1 : E ^ (1 / p) ≤ (E0 * Real.exp (c * τ)) ^ (1 / p) :=
    Real.rpow_le_rpow hE hle (by positivity)
  rw [Real.mul_rpow hE0 (Real.exp_pos _).le, ← Real.exp_mul] at h1
  have h2 : c * τ * (1 / p) = c / p * τ := by field_simp
  rw [h2] at h1
  calc a ≤ E0 ^ (1 / p) * Real.exp (c / p * τ) := ha.trans h1
    _ ≤ Cj * b * Real.exp (c / p * τ) := mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
    _ = _ := by ring

end Ap3

end HRS.Whole.AppendixA.Phase2SA16R
