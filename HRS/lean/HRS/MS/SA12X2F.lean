import HRS.MS.SA12X2E
import HRS.MS.SA12Z3NearN5

/-!
# S.A.12 N9 (SA12X2), part F: the symmetric top term

`-∑_{ij} M_{ji} ∫ ω² u H_{ij}(a u) ≤ A₃ e` for `M` with `Sym M ≤ 0`, `a ≥ 0`, `d - 2 < s ≤ d - 1`:
`ω² u H(a u) = U H(a U) + U [ω, H](a u)`, `U = ω u`; N5 for the first, N2 for the second.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

theorem sa12x2_top (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs2 : (d : ℝ) - 2 < s)
    (hs1 : s ≤ (d : ℝ) - 1) (MB R Ka Kw : ℝ) (hR : 1 ≤ R) (hKa0 : 0 ≤ Ka) (hKw0 : 0 ≤ Kw) :
    ∃ A3 : ℝ, 0 ≤ A3 ∧ ∀ (c : Euc d) (om a u : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (e : ℝ),
      PDE.MatBound MB M → Torus.SymNonpos M →
      MemCb 2 om → cbNorm 2 om ≤ Kw → HasCompactSupport om → Function.support om ⊆ closedBall c R →
      MemCb 2 a → cbNorm 2 a ≤ Ka → (∀ x, 0 ≤ a x) → HasCompactSupport a →
      Function.support a ⊆ closedBall c R → ContDiff ℝ 2 u → 0 ≤ e →
      ∫ x, (om x * u x) ^ 2 ≤ e → ∫ x, (a x * u x) ^ 2 ≤ Ka ^ 2 * e →
      -(∑ i, ∑ j, M j i * ∫ x, om x ^ 2 * (u x * hessRiesz d s i j (fun y => a y * u y) x)) ≤
        A3 * e := by
  have hsd : s < d := by linarith
  obtain ⟨C5, hC5, h5⟩ := weighted_matrix_hess d hd s MB hs0 hs2 hsd
  obtain ⟨C2, C20, hC2, hC20, h2⟩ := sa12x2_comm_real hd hs0 hs1
  have hR0 : 0 < R := by linarith
  have hRp : 0 ≤ R ^ C20 := Real.rpow_nonneg hR0.le _
  refine ⟨C5 * Ka + (d : ℝ) ^ 2 * |MB| * (C2 * Kw * R ^ C20 * Ka), ?_, ?_⟩
  · positivity
  intro c om a u M e hM hSN hom hKw homc homs ha hKa h0 hac has hu he hUe hae
  have hom2 : ContDiff ℝ 2 om := by simpa using hom.1
  have ha2 : ContDiff ℝ 2 a := by simpa using ha.1
  set U : Euc d → ℝ := fun x => om x * u x with hUdef
  have hU2 : ContDiff ℝ 2 U := hom2.mul hu
  have hUc : HasCompactSupport U := homc.mul_right
  have hUs : Function.support U ⊆ closedBall c R := fun y hy =>
    homs (Function.mem_support.2 (left_ne_zero_of_mul (Function.mem_support.1 hy)))
  have hUm : MemCb 2 U := sa12z3_memCb_of_cc hU2 hUc
  set v : Euc d → ℝ := fun y => a y * u y with hvdef
  have hv2 : ContDiff ℝ 2 v := ha2.mul hu
  have hvc : HasCompactSupport v := hac.mul_right
  have hvs : Function.support v ⊆ closedBall c R := fun y hy =>
    has (Function.mem_support.2 (left_ne_zero_of_mul (Function.mem_support.1 hy)))
  have hvm : MemCb 2 v := sa12z3_memCb_of_cc hv2 hvc
  have hU2i : 0 ≤ ∫ x, U x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hv2i : 0 ≤ ∫ x, v x ^ 2 := integral_nonneg fun x => sq_nonneg _
  -- N5 for `U`
  obtain ⟨-, hN5⟩ := h5 M hM hSN a ha h0 U hUm hUc
  have hAU : ContDiff ℝ 2 (fun y => a y * U y) := ha2.mul hU2
  have hAUc : HasCompactSupport (fun y => a y * U y) := hUc.mul_left
  -- the commutators
  set Cc : Fin d → Fin d → Euc d → ℝ := fun i j x => om x * hessRiesz d s i j v x -
    hessRiesz d s i j (fun y => om y * v y) x with hCc
  have hCcc : ∀ i j, Continuous (Cc i j) := fun i j =>
    (hom2.continuous.mul (sa12n_hess_continuous hs0 hsd i j hv2 hvc)).sub
      (sa12n_hess_continuous hs0 hsd i j (hom2.mul hv2) hvc.mul_left)
  have hHc : ∀ i j, Continuous (hessRiesz d s i j (fun y => a y * U y)) := fun i j =>
    sa12n_hess_continuous hs0 hsd i j hAU hAUc
  have hI1 : ∀ i j, Integrable (fun x => U x * hessRiesz d s i j (fun y => a y * U y) x) volume :=
    fun i j => (hU2.continuous.mul (hHc i j)).integrable_of_hasCompactSupport hUc.mul_right
  have hI2 : ∀ i j, Integrable (fun x => U x * Cc i j x) volume := fun i j =>
    (hU2.continuous.mul (hCcc i j)).integrable_of_hasCompactSupport hUc.mul_right
  have hpt : ∀ i j x, om x ^ 2 * (u x * hessRiesz d s i j v x) =
      U x * hessRiesz d s i j (fun y => a y * U y) x + U x * Cc i j x := by
    intro i j x
    have e1 : (fun y => om y * v y) = fun y => a y * U y := by
      funext y; simp only [hvdef, hUdef]; ring
    simp only [hCc, e1, hUdef]; ring
  have hsum1 : ∀ i j, ∫ x, om x ^ 2 * (u x * hessRiesz d s i j v x) =
      (∫ x, U x * hessRiesz d s i j (fun y => a y * U y) x) + ∫ x, U x * Cc i j x := by
    intro i j
    simp_rw [hpt i j]
    exact integral_add (hI1 i j) (hI2 i j)
  -- the commutator pairing
  have hcomm : ∀ i j, |∫ x, U x * Cc i j x| ≤ C2 * Kw * R ^ C20 * Ka * e := by
    intro i j
    refine (sa12x2_pairU hU2.continuous hUc hUs (hCcc i j)).trans ?_
    have hb := h2 i j R hR om hom c v hvm hvs
    have h1 : Real.sqrt (∫ x, U x ^ 2) ≤ Real.sqrt e := Real.sqrt_le_sqrt hUe
    have h3 : Real.sqrt (∫ x, v x ^ 2) ≤ Ka * Real.sqrt e := by
      calc Real.sqrt (∫ x, v x ^ 2) ≤ Real.sqrt (Ka ^ 2 * e) := Real.sqrt_le_sqrt hae
        _ = Ka * Real.sqrt e := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hKa0]
    have h4 : C2 * cbNorm 2 om * R ^ C20 ≤ C2 * Kw * R ^ C20 := by gcongr
    have h5' : Real.sqrt (∫ x, ((closedBall c R).indicator (Cc i j) x) ^ 2) ≤
        C2 * Kw * R ^ C20 * (Ka * Real.sqrt e) :=
      hb.trans (mul_le_mul h4 h3 (Real.sqrt_nonneg _) (by positivity))
    calc Real.sqrt (∫ x, U x ^ 2) * Real.sqrt (∫ x, ((closedBall c R).indicator (Cc i j) x) ^ 2)
        ≤ Real.sqrt e * (C2 * Kw * R ^ C20 * (Ka * Real.sqrt e)) :=
          mul_le_mul h1 h5' (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = C2 * Kw * R ^ C20 * Ka * (Real.sqrt e * Real.sqrt e) := by ring
      _ = C2 * Kw * R ^ C20 * Ka * e := by rw [Real.mul_self_sqrt he]
  -- assemble
  have hS : ∑ i, ∑ j, M j i * ∫ x, om x ^ 2 * (u x * hessRiesz d s i j v x) =
      (∫ x, U x * matrixHess d s M (fun y => a y * U y) x) +
        ∑ i, ∑ j, M j i * ∫ x, U x * Cc i j x := by
    rw [sa12x2_int_mH s M U _ hI1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsum1 i j]; ring
  have hS2 : |∑ i, ∑ j, M j i * ∫ x, U x * Cc i j x| ≤
      (d : ℝ) ^ 2 * |MB| * (C2 * Kw * R ^ C20 * Ka * e) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hrow : ∀ i : Fin d, |∑ j, M j i * ∫ x, U x * Cc i j x| ≤
        (d : ℝ) * (|MB| * (C2 * Kw * R ^ C20 * Ka * e)) := by
      intro i
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have : ∀ j ∈ (Finset.univ : Finset (Fin d)), |M j i * ∫ x, U x * Cc i j x| ≤
          |MB| * (C2 * Kw * R ^ C20 * Ka * e) := fun j _ => by
        rw [abs_mul]
        exact mul_le_mul ((hM j i).trans (le_abs_self _)) (hcomm i j) (abs_nonneg _) (abs_nonneg _)
      refine (Finset.sum_le_sum this).trans ?_
      simp
    refine (Finset.sum_le_sum fun i _ => hrow i).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    refine le_of_eq ?_; ring
  rw [hS]
  have hcb : cbNorm 2 a * ∫ x, U x ^ 2 ≤ Ka * e := by
    exact mul_le_mul hKa hUe hU2i hKa0
  have := neg_abs_le (∑ i, ∑ j, M j i * ∫ x, U x * Cc i j x)
  nlinarith [hN5, hC5, mul_le_mul_of_nonneg_left hcb hC5.le]

end HRS.MH.AdjointRd.Phase2SA12Near
