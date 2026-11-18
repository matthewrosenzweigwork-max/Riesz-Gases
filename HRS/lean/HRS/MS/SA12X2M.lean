import HRS.MS.SA12X2L
import HRS.MS.SA12Z2NearN3

/-!
# S.A.12 N8 (SA12X2), part M: the odd same-function term with the cutoff `ω²`

For `0 ≤ s < d`: `|∫ ω² u T_i(b u)| ≤ K e` whenever `∫ (ω u)² ≤ e`, `∫ (b u)² ≤ K_b² e`.
`ω² u T_i(b u) = U ω T_i(b u) = U T_i(b U) + U [ω, T_i](b u)`, `U = ω u`: N3 (`odd_same_finite`) for the first,
the commutator bound `sa12x2_commT_real` for the second.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

theorem sa12x2_T2 (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (R Kb Kb' Kw : ℝ) (hR : 1 ≤ R)
    (hKb : 0 ≤ Kb) (hKb' : 0 ≤ Kb') (hKw : 0 ≤ Kw) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (c : Euc d) (om b u : Euc d → ℝ) (i : Fin d) (e : ℝ),
      MemCb 2 om → cbNorm 2 om ≤ Kw → HasCompactSupport om → Function.support om ⊆ closedBall c R →
      MemCb 1 b → cbNorm 1 b ≤ Kb → Function.support b ⊆ closedBall c R → ContDiff ℝ 2 u → 0 ≤ e →
      ∫ x, (om x * u x) ^ 2 ≤ e → ∫ x, (b x * u x) ^ 2 ≤ Kb' ^ 2 * e →
      |∫ x, om x ^ 2 * (u x * firstRiesz d s i (fun y => b y * u y) x)| ≤ K * e := by
  obtain ⟨C3, C30, hC3, hC30, h3⟩ := odd_same_finite d hd s hs0 hsd
  obtain ⟨Cc, hCc0, hCc⟩ := sa12x2_commT_real hd hs0 hsd
  have hR0 : 0 < R := by linarith
  have hRp : 0 ≤ R ^ C30 := Real.rpow_nonneg hR0.le _
  have hRd : 0 ≤ R ^ (d : ℝ) := Real.rpow_nonneg hR0.le _
  refine ⟨C3 * Kb * R ^ C30 + Cc * Kw * R ^ (d : ℝ) * Kb', by positivity, ?_⟩
  intro c om b u i e hom hKw' homc homs hb hKb'' hbs hu he hUe hbe
  have hom2 : ContDiff ℝ 2 om := by simpa using hom.1
  have hb1 : ContDiff ℝ 1 b := by simpa using hb.1
  set U : Euc d → ℝ := fun x => om x * u x with hUdef
  have hU2 : ContDiff ℝ 2 U := hom2.mul hu
  have hUc : HasCompactSupport U := homc.mul_right
  have hUs : Function.support U ⊆ closedBall c R := fun y hy =>
    homs (Function.mem_support.2 (left_ne_zero_of_mul (Function.mem_support.1 hy)))
  have hUm : MemCb 2 U := sa12z3_memCb_of_cc hU2 hUc
  set v : Euc d → ℝ := fun y => b y * u y with hvdef
  have hv1 : ContDiff ℝ 1 v := hb1.mul (hu.of_le (by norm_num))
  have hvc : HasCompactSupport v := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c R) fun y hy => ?_
    exact hbs (Function.mem_support.2 (left_ne_zero_of_mul (Function.mem_support.1 hy)))
  have hvs : Function.support v ⊆ closedBall c R := fun y hy =>
    hbs (Function.mem_support.2 (left_ne_zero_of_mul (Function.mem_support.1 hy)))
  have hKw0 : 0 ≤ Kw := hKw
  have hU2i : 0 ≤ ∫ x, U x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hv2i : 0 ≤ ∫ x, v x ^ 2 := integral_nonneg fun x => sq_nonneg _
  -- N3 for `U`
  obtain ⟨hI3, hN3⟩ := h3 i R hR b hb c U hUm hUs
  -- the commutator
  set Cm : Euc d → ℝ := fun x => om x * firstRiesz d s i v x -
    firstRiesz d s i (fun y => om y * v y) x with hCm
  have hCmc : Continuous Cm :=
    (hom2.continuous.mul (sa12z3_firstRiesz_cont hs0 hsd i hv1 hvc)).sub
      (sa12z3_firstRiesz_cont hs0 hsd i ((hom2.of_le (by norm_num)).mul hv1) hvc.mul_left)
  have hI2 : Integrable (fun x => U x * Cm x) volume :=
    (hU2.continuous.mul hCmc).integrable_of_hasCompactSupport hUc.mul_right
  have hlip : ∀ x y, |om x - om y| ≤ Kw * ‖x - y‖ := fun x y =>
    (sa12z3_a_lip hom x y).trans (mul_le_mul_of_nonneg_right hKw' (norm_nonneg _))
  have hpt : ∀ x, om x ^ 2 * (u x * firstRiesz d s i v x) =
      U x * firstRiesz d s i (fun y => b y * U y) x + U x * Cm x := by
    intro x
    have e1 : (fun y => om y * v y) = fun y => b y * U y := by
      funext y; simp only [hvdef, hUdef]; ring
    simp only [hCm, e1, hUdef]; ring
  have hsum : ∫ x, om x ^ 2 * (u x * firstRiesz d s i v x) =
      (∫ x, U x * firstRiesz d s i (fun y => b y * U y) x) + ∫ x, U x * Cm x := by
    simp_rw [hpt]
    exact integral_add hI3 hI2
  have hcomm : |∫ x, U x * Cm x| ≤ Cc * Kw * R ^ (d : ℝ) * Kb' * e := by
    refine (sa12x2_pairU hU2.continuous hUc hUs hCmc).trans ?_
    have hb2 := hCc i R hR c om v Kw hKw (hom2.of_le (by norm_num)) hlip hv1 hvc hvs
    have h1 : Real.sqrt (∫ x, U x ^ 2) ≤ Real.sqrt e := Real.sqrt_le_sqrt hUe
    have h3' : Real.sqrt (∫ x, v x ^ 2) ≤ Kb' * Real.sqrt e := by
      calc Real.sqrt (∫ x, v x ^ 2) ≤ Real.sqrt (Kb' ^ 2 * e) := Real.sqrt_le_sqrt hbe
        _ = Kb' * Real.sqrt e := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hKb']
    have h5 : Real.sqrt (∫ x, ((closedBall c R).indicator Cm x) ^ 2) ≤
        Cc * Kw * R ^ (d : ℝ) * (Kb' * Real.sqrt e) :=
      hb2.trans (mul_le_mul_of_nonneg_left h3' (by positivity))
    calc Real.sqrt (∫ x, U x ^ 2) * Real.sqrt (∫ x, ((closedBall c R).indicator Cm x) ^ 2)
        ≤ Real.sqrt e * (Cc * Kw * R ^ (d : ℝ) * (Kb' * Real.sqrt e)) :=
          mul_le_mul h1 h5 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Cc * Kw * R ^ (d : ℝ) * Kb' * (Real.sqrt e * Real.sqrt e) := by ring
      _ = Cc * Kw * R ^ (d : ℝ) * Kb' * e := by rw [Real.mul_self_sqrt he]
  rw [hsum]
  have hN3' : |∫ x, U x * firstRiesz d s i (fun y => b y * U y) x| ≤ C3 * Kb * R ^ C30 * e := by
    refine hN3.trans ?_
    have hcb := sa12z3_cb_nonneg hb
    calc C3 * cbNorm 1 b * R ^ C30 * ∫ x, U x ^ 2 ≤ C3 * Kb * R ^ C30 * e := by
          have : cbNorm 1 b * R ^ C30 ≤ Kb * R ^ C30 := mul_le_mul_of_nonneg_right hKb'' hRp
          have h0 : 0 ≤ C3 := hC3.le
          calc C3 * cbNorm 1 b * R ^ C30 * ∫ x, U x ^ 2
              = C3 * (cbNorm 1 b * R ^ C30) * ∫ x, U x ^ 2 := by ring
            _ ≤ C3 * (Kb * R ^ C30) * e := by
                gcongr
            _ = C3 * Kb * R ^ C30 * e := by ring
      _ = _ := rfl
  calc |(∫ x, U x * firstRiesz d s i (fun y => b y * U y) x) + ∫ x, U x * Cm x|
      ≤ |∫ x, U x * firstRiesz d s i (fun y => b y * U y) x| + |∫ x, U x * Cm x| := abs_add_le _ _
    _ ≤ C3 * Kb * R ^ C30 * e + Cc * Kw * R ^ (d : ℝ) * Kb' * e := add_le_add hN3' hcomm
    _ = (C3 * Kb * R ^ C30 + Cc * Kw * R ^ (d : ℝ) * Kb') * e := by ring

end HRS.MH.AdjointRd.Phase2SA12Near
