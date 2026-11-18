import HRS.MS.SA16Y6Tc4

/-!
# S.A.16 (SA16Y6) Tc5: the heat-gain `L^p` bound for `Tc` (boundary `s = d-1`)

`sa16y6_Tc_bound` (`p ≥ 2`): `‖Tc_a(P,Q)‖_p ≤ C a^{-1/2} (‖P‖_p + ‖Q‖_p)` for `0 < a ≤ 1`, `P, Q ∈ C_c^∞`.
Route: `g_a ⋆ R_i(∂_jP) = g_a ⋆ ∂_j(R_iP) = (∂_jg_a) ⋆ R_iP` (IBP, `sa16y6_cv_ibp`), Young and the Calderón-Zygmund bound for `R_i`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q HRS.MS.ToriCoefA

section Tc5
variable {d : ℕ}

lemma sa16y6_cv_RD (hd : 1 ≤ d) {a : ℝ} (ha : 0 < a) (i j : Fin d) {P : Euc d → ℝ} (hP : IsCcInfty P) :
    sa16r_cv (sa16r_g d a) (sa16y6_R d i (fun z => fderiv ℝ P z (sa16z_e j))) =
      sa16r_cv (sa16r_dg d a j) (sa16y6_R d i P) := by
  have e : sa16y6_R d i (fun z => fderiv ℝ P z (sa16z_e j)) =
      fun y => fderiv ℝ (sa16y6_R d i P) y (sa16z_e j) :=
    funext fun y => (sa16y6_R_fderiv hd rfl hP i j y).symm
  rw [e]
  funext x
  exact sa16y6_cv_ibp ha (sa16y6_R_BS hd rfl hP i) j x

theorem sa16y6_Tc_bound (hd : 1 ≤ d) {p : ℝ} (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ (i j : Fin d) (P Q : Euc d → ℝ), IsCcInfty P → IsCcInfty Q →
      eLpNorm (sa16y6_Tc d a i j P Q) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * a ^ (-(1 / 2 : ℝ))) *
          (eLpNorm P (ENNReal.ofReal p) volume + eLpNorm Q (ENNReal.ofReal p) volume) := by
  have hp1 : 1 ≤ p := by linarith
  choose CR hCR0 hCR using fun i : Fin d => sa16y6_R_Lp hd hp i
  set CRm : ℝ := ∑ i, CR i with hCRm
  have hCRm0 : 0 ≤ CRm := Finset.sum_nonneg fun i _ => hCR0 i
  have hCRle : ∀ i, CR i ≤ CRm := fun i =>
    Finset.single_le_sum (f := CR) (fun i _ => hCR0 i) (Finset.mem_univ i)
  set A : ℝ := (4 / 3 : ℝ) ^ ((d : ℝ) / 2) with hA
  have hA0 : 0 ≤ A := by positivity
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) ≤ (d : ℝ) - 1 := by linarith
  have hcs : 0 ≤ sa16y6_cs d := by
    unfold sa16y6_cs
    exact HRS.CZ.Hls.hlsg_c_nonneg hs0
  refine ⟨sa16y6_cs d * (CRm * (A + 1)), by positivity, ?_⟩
  intro a ha ha1 i j P Q hP hQ
  have hRPc : Continuous (sa16y6_R d i P) := (sa16y6_R_contDiff hd rfl hP i).continuous
  have hRQc : Continuous (sa16y6_R d i Q) := (sa16y6_R_contDiff hd rfl hQ i).continuous
  have hX : ∀ x, sa16y6_Tc d a i j P Q x = -(sa16y6_cs d) *
      (sa16r_cv (sa16r_dg d a j) (sa16y6_R d i P) x - sa16r_cv (sa16r_g d a) (sa16y6_R d i Q) x) := by
    intro x
    unfold sa16y6_Tc sa16y6_Wf
    obtain ⟨B1, hB1⟩ := sa16y6_R_bdd hd (sa16s_cc_fderiv hP (sa16z_e j)) i
    obtain ⟨B2, hB2⟩ := sa16y6_R_bdd hd hQ i
    rw [sa16y5_cv_sub_bdd (sa16r_g_int ha) (sa16y6_R_contDiff hd rfl (sa16s_cc_fderiv hP (sa16z_e j)) i).continuous
      hRQc hB1 hB2 x, sa16y6_cv_RD hd ha i j hP]
  have hA1 : Continuous (sa16r_cv (sa16r_dg d a j) (sa16y6_R d i P)) :=
    (sa16y6_cv_contDiff (sa16r_dg_cont a j).measurable (sa16r_dg_int ha j) (sa16y6_R_BS hd rfl hP i)).continuous
  have hB1 : Continuous (sa16r_cv (sa16r_g d a) (sa16y6_R d i Q)) :=
    (sa16y6_cv_contDiff sa16r_g_meas (sa16r_g_int ha) (sa16y6_R_BS hd rfl hQ i)).continuous
  have e : sa16y6_Tc d a i j P Q = (-(sa16y6_cs d)) • (fun x => sa16r_cv (sa16r_dg d a j) (sa16y6_R d i P) x -
      sa16r_cv (sa16r_g d a) (sa16y6_R d i Q) x) := by
    funext x; rw [hX x]; simp
  rw [e, eLpNorm_const_smul]
  have hn : ‖(-(sa16y6_cs d))‖ₑ = ENNReal.ofReal (sa16y6_cs d) := by
    rw [Real.enorm_eq_ofReal_abs, abs_neg, abs_of_nonneg hcs]
  rw [hn]
  have h1 := sa16y5_young (sa16r_dg_cont a j).measurable (sa16r_dg_int ha j) hRPc hp1
  have h2 := sa16y5_young sa16r_g_meas (sa16r_g_int ha) hRQc hp1
  rw [sa16y5_g_abs_L1 ha] at h2
  have hdg := sa16r_dg_L1 (d := d) ha j
  have hRP := hCR i P hP
  have hRQ := hCR i Q hQ
  have hsub := eLpNorm_sub_le (μ := (volume : Measure (Euc d))) (p := ENNReal.ofReal p)
    (f := sa16r_cv (sa16r_dg d a j) (sa16y6_R d i P)) (g := sa16r_cv (sa16r_g d a) (sa16y6_R d i Q))
    (ENNReal.one_le_ofReal.2 hp1)
  have hXa : a ^ (-(1 / 2 : ℝ)) ≥ 1 := by
    have : (1 : ℝ) ≤ a ^ (-(1 / 2 : ℝ)) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ha ha1 (by norm_num)
    exact this
  have hXa0 : 0 ≤ a ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg ha.le _
  have eP : ENNReal.ofReal (∫ z, |sa16r_dg d a j z|) ≤ ENNReal.ofReal (a ^ (-(1 / 2 : ℝ)) * A) :=
    ENNReal.ofReal_le_ofReal hdg
  calc ENNReal.ofReal (sa16y6_cs d) * eLpNorm (fun x => sa16r_cv (sa16r_dg d a j) (sa16y6_R d i P) x -
        sa16r_cv (sa16r_g d a) (sa16y6_R d i Q) x) (ENNReal.ofReal p) volume
      ≤ ENNReal.ofReal (sa16y6_cs d) * (eLpNorm (sa16r_cv (sa16r_dg d a j) (sa16y6_R d i P)) (ENNReal.ofReal p) volume +
          eLpNorm (sa16r_cv (sa16r_g d a) (sa16y6_R d i Q)) (ENNReal.ofReal p) volume) := by
        exact mul_le_mul' le_rfl hsub
    _ ≤ ENNReal.ofReal (sa16y6_cs d) * (ENNReal.ofReal (a ^ (-(1 / 2 : ℝ)) * A) *
          (ENNReal.ofReal CRm * eLpNorm P (ENNReal.ofReal p) volume) +
          1 * (ENNReal.ofReal CRm * eLpNorm Q (ENNReal.ofReal p) volume)) := by
        refine mul_le_mul' le_rfl (add_le_add ?_ ?_)
        · exact h1.trans (mul_le_mul' eP (hRP.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (hCRle i)) le_rfl)))
        · refine h2.trans (mul_le_mul' (by simp) (hRQ.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (hCRle i)) le_rfl)))
    _ ≤ ENNReal.ofReal (sa16y6_cs d * (CRm * (A + 1)) * a ^ (-(1 / 2 : ℝ))) *
          (eLpNorm P (ENNReal.ofReal p) volume + eLpNorm Q (ENNReal.ofReal p) volume) := by
        have hw : 0 ≤ a ^ (-(1 / 2 : ℝ)) * (A + 1) := by positivity
        have c1 : ENNReal.ofReal (a ^ (-(1 / 2 : ℝ)) * A) ≤ ENNReal.ofReal (a ^ (-(1 / 2 : ℝ)) * (A + 1)) :=
          ENNReal.ofReal_le_ofReal (by nlinarith)
        have c2 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (a ^ (-(1 / 2 : ℝ)) * (A + 1)) := by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (by nlinarith)
        have key : ENNReal.ofReal (a ^ (-(1 / 2 : ℝ)) * A) *
              (ENNReal.ofReal CRm * eLpNorm P (ENNReal.ofReal p) volume) +
              1 * (ENNReal.ofReal CRm * eLpNorm Q (ENNReal.ofReal p) volume) ≤
            ENNReal.ofReal (a ^ (-(1 / 2 : ℝ)) * (A + 1)) * ENNReal.ofReal CRm *
              (eLpNorm P (ENNReal.ofReal p) volume + eLpNorm Q (ENNReal.ofReal p) volume) := by
          calc _ ≤ ENNReal.ofReal (a ^ (-(1 / 2 : ℝ)) * (A + 1)) *
                (ENNReal.ofReal CRm * eLpNorm P (ENNReal.ofReal p) volume) +
              ENNReal.ofReal (a ^ (-(1 / 2 : ℝ)) * (A + 1)) *
                (ENNReal.ofReal CRm * eLpNorm Q (ENNReal.ofReal p) volume) :=
                add_le_add (mul_le_mul' c1 le_rfl) (mul_le_mul' c2 le_rfl)
            _ = _ := by ring
        have e2 : ENNReal.ofReal (sa16y6_cs d * (CRm * (A + 1)) * a ^ (-(1 / 2 : ℝ))) =
            ENNReal.ofReal (sa16y6_cs d) * (ENNReal.ofReal (a ^ (-(1 / 2 : ℝ)) * (A + 1)) * ENNReal.ofReal CRm) := by
          rw [show sa16y6_cs d * (CRm * (A + 1)) * a ^ (-(1 / 2 : ℝ)) =
              sa16y6_cs d * ((a ^ (-(1 / 2 : ℝ)) * (A + 1)) * CRm) by ring,
            ENNReal.ofReal_mul hcs, ENNReal.ofReal_mul hw]
        rw [e2, mul_assoc]
        exact mul_le_mul' le_rfl key

end Tc5

end HRS.Whole.AppendixA.Phase2SA16R
