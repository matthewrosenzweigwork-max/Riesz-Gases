import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.Whole.MovtrAux1

/-!
# S6.7 nonlinear, packet S6.7nl.04: polynomial Gaussian L2 membership and norm

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4180-4182, row
`S:W:lem:r2mov-global-adjoint` (nonlinear part). Owned definitions: none.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

/-- Polynomial times Gaussian is integrable on `Euc d`, in every dimension `d`
(for `d = 0` the space is a point and the integrand is the constant `1`). -/
theorem s67bd_poly_gauss_integrable (d k : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Euc d => (1 + ‖x‖) ^ k * Real.exp (-c * ‖x‖ ^ 2)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h : ∀ x : Euc 0, (1 + ‖x‖) ^ k * Real.exp (-c * ‖x‖ ^ 2) = 1 := by
      intro x
      have hx : x = 0 := by
        ext i
        exact i.elim0
      simp [hx]
    exact (integrable_const (1 : ℝ)).congr (ae_of_all _ fun x => (h x).symm)
  · have hd1 : 1 ≤ d := by omega
    have hexp : ∀ x : Euc d, (1 + ‖x‖) ^ k * Real.exp (-c * ‖x‖ ^ 2) =
        ∑ m ∈ Finset.range (k + 1),
          (k.choose m : ℝ) * (‖x‖ ^ (m : ℝ) * Real.exp (-c * ‖x‖ ^ 2)) := by
      intro x
      rw [add_comm (1 : ℝ) ‖x‖, add_pow, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [one_pow, mul_one, Real.rpow_natCast]
      ring
    have hint : ∀ m ∈ Finset.range (k + 1),
        Integrable (fun x : Euc d => (k.choose m : ℝ) * (‖x‖ ^ (m : ℝ) * Real.exp (-c * ‖x‖ ^ 2))) := by
      intro m _
      have hα : -(d : ℝ) < (m : ℝ) := by
        have h1 : (1 : ℝ) ≤ d := by exact_mod_cast hd1
        have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith
      exact (movtr_integrable_rpow_gauss hd1 hα hc).const_mul _
    have hfun : (fun x : Euc d => (1 + ‖x‖) ^ k * Real.exp (-c * ‖x‖ ^ 2)) =
        fun x : Euc d => ∑ m ∈ Finset.range (k + 1),
          (k.choose m : ℝ) * (‖x‖ ^ (m : ℝ) * Real.exp (-c * ‖x‖ ^ 2)) :=
      funext hexp
    rw [hfun]
    exact integrable_finsetSum _ hint

/-- **`s67bd_gaussian_L2`.** A measurable amplitude dominated by `A (1+‖x‖)^n e^{-b‖x‖²}` is in
`L²`, with norm at most `C A`, where `C` (the `L²` norm of the envelope) is fixed before `A` and `u`. -/
theorem s67bd_gaussian_L2 (d n : ℕ) (b : ℝ) (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ), 0 ≤ A → ∀ u : Euc d → ℝ,
      AEStronglyMeasurable u volume →
      (∀ x, |u x| ≤ A * (1 + ‖x‖) ^ n * Real.exp (-b * ‖x‖ ^ 2)) →
      MemLp u 2 volume ∧ (eLpNorm u 2 volume).toReal ≤ C * A := by
  obtain ⟨G, hGx⟩ : ∃ G : Euc d → ℝ, ∀ x, G x = (1 + ‖x‖) ^ n * Real.exp (-b * ‖x‖ ^ 2) :=
    ⟨fun x => (1 + ‖x‖) ^ n * Real.exp (-b * ‖x‖ ^ 2), fun x => rfl⟩
  have hGnn : ∀ x, 0 ≤ G x := fun x => by
    rw [hGx x]
    exact mul_nonneg (pow_nonneg (by positivity) _) (Real.exp_pos _).le
  have hGc : Continuous G := by
    have : G = fun x => (1 + ‖x‖) ^ n * Real.exp (-b * ‖x‖ ^ 2) := funext hGx
    rw [this]
    fun_prop
  have hsq : ∀ x, G x ^ 2 = (1 + ‖x‖) ^ (n * 2) * Real.exp (-(2 * b) * ‖x‖ ^ 2) := by
    intro x
    rw [hGx x, mul_pow, ← pow_mul, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hGL : MemLp G 2 volume := by
    rw [memLp_two_iff_integrable_sq hGc.aestronglyMeasurable]
    exact (s67bd_poly_gauss_integrable d (n * 2) (c := 2 * b) (by linarith)).congr
      (ae_of_all _ fun x => (hsq x).symm)
  refine ⟨(eLpNorm G 2 volume).toReal, ENNReal.toReal_nonneg, fun A hA u hu hdom => ?_⟩
  have hdomG : ∀ x, ‖u x‖ ≤ ‖A * G x‖ := by
    intro x
    rw [Real.norm_of_nonneg (mul_nonneg hA (hGnn x)), Real.norm_eq_abs, hGx x]
    exact (hdom x).trans_eq (by ring)
  have hAG : MemLp (fun x => A * G x) 2 volume := hGL.const_mul A
  have hu_mem : MemLp u 2 volume := hAG.of_le hu (ae_of_all _ hdomG)
  refine ⟨hu_mem, ?_⟩
  have h1 : eLpNorm u 2 volume ≤ eLpNorm (fun x => A * G x) 2 volume :=
    eLpNorm_mono hu hdomG
  have h2 : eLpNorm (fun x => A * G x) 2 volume = ENNReal.ofReal A * eLpNorm G 2 volume := by
    rw [show (fun x => A * G x) = A • G from rfl, eLpNorm_const_smul,
      Real.enorm_eq_ofReal hA]
  rw [h2] at h1
  have hfin : ENNReal.ofReal A * eLpNorm G 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGL.eLpNorm_lt_top.ne
  calc (eLpNorm u 2 volume).toReal ≤ (ENNReal.ofReal A * eLpNorm G 2 volume).toReal :=
        ENNReal.toReal_mono hfin h1
    _ = A * (eLpNorm G 2 volume).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA]
    _ = (eLpNorm G 2 volume).toReal * A := mul_comm _ _

end HRS.MS.BreakdownS67

end
