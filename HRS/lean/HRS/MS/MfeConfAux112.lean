import HRS.MS.MfeConfAux111

/-!
# S.B.1, packet F9 (part 15): uniform integrability of the level-`M` commutator energy under the dominated laws

Under the canonical-Gibbs domination `μ^M ≤ c · e^{-β H_M} dX` and the envelope `|C^M| ≤ K (A₁ (P_M + ℓ) + A₂)` the tails
`∫_{|C^M| ≥ L} |C^M| dμ^M` are small uniformly in `M` (`sb1_Ck_tail`), and `sb1_Cmean_limit` passes to the limit.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

theorem sb1_sumV_lower {V : Euc d → ℝ} {cV CV : ℝ} (hcV : 0 < cV) (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ V x)
    (Z : Whole.EucConfig d N) : cV * ‖Z‖ ^ 2 - N * CV ≤ ∑ i, V (Z i) := by
  calc cV * ‖Z‖ ^ 2 - N * CV ≤ cV * ∑ i, ‖Z i‖ ^ 2 - N * CV := by
        have := mul_le_mul_of_nonneg_left (sb1_pi_norm_sq_le Z) hcV.le
        linarith
    _ = ∑ i, (cV * ‖Z i‖ ^ 2 - CV) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; simp
    _ ≤ ∑ i, V (Z i) := Finset.sum_le_sum fun i _ => hV (Z i)

/-- the Gaussian majorant of the tilted weight `e^{βNℓ} e^{-βΣV}` -/
theorem sb1_Phi_int {V : Euc d → ℝ} (hVm : Measurable V) {cV CV : ℝ} (hcV : 0 < cV)
    (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ V x) {β : ℝ} (hβ : 0 < β) (hN : 1 ≤ N) :
    Integrable (fun Z : Whole.EucConfig d N => Real.exp (β * N * (‖Z‖ + 1 / 2)) * Real.exp (-β * ∑ i, V (Z i)))
      volume := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hg : Integrable (fun Ξ : Whole.EucConfig d N =>
      Real.exp (β * N * (1 / 2) + β * N * CV + β * (N : ℝ) ^ 2 / (2 * cV)) * Real.exp (-(β * cV / 2 * ‖Ξ‖ ^ 2))) volume :=
    (p4g_integrable_gauss_pi (c := β * cV / 2) (by positivity)).const_mul _
  refine hg.mono' ?_ (Eventually.of_forall fun Z => ?_)
  · exact ((Real.measurable_exp.comp ((measurable_norm.add_const _).const_mul _)).mul
      (Real.measurable_exp.comp ((Finset.measurable_sum _ fun i _ => hVm.comp (measurable_pi_apply i)).const_mul _))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)), ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 := sb1_sumV_lower (N := N) hcV hV Z
    have h2 : (N : ℝ) * ‖Z‖ ≤ (cV / 2) * ‖Z‖ ^ 2 + (N : ℝ) ^ 2 / (2 * cV) := by
      have : 0 ≤ (cV * ‖Z‖ - N) ^ 2 / (2 * cV) := by positivity
      have e : (cV * ‖Z‖ - N) ^ 2 / (2 * cV) = (cV / 2) * ‖Z‖ ^ 2 - N * ‖Z‖ + (N : ℝ) ^ 2 / (2 * cV) := by
        field_simp; ring
      linarith
    have h1' := mul_le_mul_of_nonneg_left h1 hβ.le
    have h2' := mul_le_mul_of_nonneg_left h2 hβ.le
    have e : β * (N : ℝ) ^ 2 / (2 * cV) = β * ((N : ℝ) ^ 2 / (2 * cV)) := by ring
    rw [e]
    linarith

theorem sb1_tail_pt {q μ' L' : ℝ} (hq : 0 ≤ q) (hμ : 0 < μ') (hqL : L' ≤ q) :
    q * Real.exp (-μ' * q) ≤ (2 / μ') * Real.exp (-μ' * L' / 2) := by
  set u := μ' * q with hu
  have hu0 : 0 ≤ u := by positivity
  have h1 : u ≤ 2 * Real.exp (u / 2) := by
    have := Real.add_one_le_exp (u / 2)
    linarith
  have e1 : q * Real.exp (-μ' * q) = (1 / μ') * (u * Real.exp (-u)) := by
    rw [hu]; field_simp
  have h2 : u * Real.exp (-u) ≤ 2 * Real.exp (-(u / 2)) :=
    calc u * Real.exp (-u) ≤ 2 * Real.exp (u / 2) * Real.exp (-u) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = 2 * Real.exp (-(u / 2)) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have h3 : Real.exp (-(u / 2)) ≤ Real.exp (-μ' * L' / 2) := by
    apply Real.exp_le_exp.2
    rw [hu]
    nlinarith
  rw [e1]
  calc (1 / μ') * (u * Real.exp (-u)) ≤ (1 / μ') * (2 * Real.exp (-μ' * L' / 2)) :=
        mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h3 (by norm_num))) (by positivity)
    _ = (2 / μ') * Real.exp (-μ' * L' / 2) := by ring

/-- the pointwise tail estimate, a statement about real numbers -/
theorem sb1_real_tail {β Nr A1 A2 Kr L PM ell SV zn Cabs : ℝ} (hβ : 0 < β) (hN : 0 < Nr) (hA1 : 0 < A1)
    (hA2 : 0 ≤ A2) (hKr : 0 < Kr) (hC0 : 0 ≤ Cabs) (hC : Cabs ≤ Kr * (A1 * (PM + ell) + A2))
    (hell : ell ≤ zn + 1 / 2) (hL : L ≤ Cabs) (hL0 : 0 ≤ L) :
    Cabs * Real.exp (-β * (Nr * PM + SV)) ≤
      (Kr * (2 / (β * Nr / A1)) * Real.exp (β * Nr * A2 / A1) * Real.exp (-(β * Nr / A1) * (L / Kr) / 2)) *
        (Real.exp (β * Nr * (zn + 1 / 2)) * Real.exp (-β * SV)) := by
  set q := A1 * (PM + ell) + A2 with hq
  have hμ : 0 < β * Nr / A1 := by positivity
  have hq0 : 0 ≤ q := by
    have : 0 ≤ Kr * q := hC0.trans hC
    exact (mul_nonneg_iff_of_pos_left hKr).1 this
  have hLq : L / Kr ≤ q := by
    rw [div_le_iff₀ hKr]
    nlinarith
  have hPM : PM = (q - A2) / A1 - ell := by rw [hq]; field_simp; ring
  have hexp : Real.exp (-β * (Nr * PM + SV)) ≤ Real.exp (-(β * Nr / A1) * q) * Real.exp (β * Nr * A2 / A1) *
      Real.exp (β * Nr * (zn + 1 / 2)) * Real.exp (-β * SV) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have e : -β * (Nr * PM + SV) = -(β * Nr / A1) * q + β * Nr * A2 / A1 + β * Nr * ell + -β * SV := by
      rw [hPM]; field_simp; ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hell (by positivity : 0 ≤ β * Nr)]
  have hqt := sb1_tail_pt hq0 hμ hLq
  calc Cabs * Real.exp (-β * (Nr * PM + SV)) ≤ (Kr * q) * Real.exp (-β * (Nr * PM + SV)) :=
        mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le
    _ ≤ (Kr * q) * (Real.exp (-(β * Nr / A1) * q) * Real.exp (β * Nr * A2 / A1) *
          Real.exp (β * Nr * (zn + 1 / 2)) * Real.exp (-β * SV)) :=
        mul_le_mul_of_nonneg_left hexp (mul_nonneg hKr.le hq0)
    _ = Kr * (q * Real.exp (-(β * Nr / A1) * q)) * Real.exp (β * Nr * A2 / A1) *
          (Real.exp (β * Nr * (zn + 1 / 2)) * Real.exp (-β * SV)) := by ring
    _ ≤ Kr * ((2 / (β * Nr / A1)) * Real.exp (-(β * Nr / A1) * (L / Kr) / 2)) * Real.exp (β * Nr * A2 / A1) *
          (Real.exp (β * Nr * (zn + 1 / 2)) * Real.exp (-β * SV)) := by
        gcongr
    _ = _ := by ring

end HRS.MS.MfeConf
