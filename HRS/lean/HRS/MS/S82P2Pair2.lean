import HRS.MS.S82P2Pair1
import HRS.MS.S82P2QF1

/-!
# S8.2 (S82P2): row facts for the corrector differences `ψ_{x,y} = Q(y,·) - Q(x,·)` (UNCOMPILED DRAFT)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

lemma s82p2_Q_row_measurable {d : ℕ} {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) (x : Euc d) :
    Measurable (Q x) :=
  hQ.measurable.comp (measurable_prodMk_left (x := x))

lemma s82p2_Q_meas_pair {d n : ℕ} {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) (k l : Fin n) :
    Measurable (fun X : EucConfig d n => Q (X k) (X l)) := by
  have h2 : Measurable (fun X : EucConfig d n => (X k, X l)) :=
    (measurable_pi_apply k).prodMk (measurable_pi_apply l)
  exact hQ.measurable.comp h2

/-- integrability of the squared rows and the real bound. -/
lemma s82p2_Q_sq_integrable {d : ℕ} {a beta M A K0 : ℝ} (hK0 : 0 ≤ K0) {rho : Euc d → ℝ}
    {f : Euc d → ℝ} {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q)
    (hK : ∀ x : Euc d, ∫⁻ z, ENNReal.ofReal (Q x z ^ 2) ∂HRS.Whole.withDensityReal rho ≤
        ENNReal.ofReal (4 * A ^ 2 * K0 * jbracket x ^ (4 * M))) (x : Euc d) :
    Integrable (fun z => Q x z ^ 2) (HRS.Whole.withDensityReal rho) ∧
      ∫ z, Q x z ^ 2 ∂HRS.Whole.withDensityReal rho ≤ 4 * A ^ 2 * K0 * jbracket x ^ (4 * M) := by
  have hm : Measurable (fun z => Q x z ^ 2) := (s82p2_Q_row_measurable hQ x).pow_const 2
  have hint : Integrable (fun z => Q x z ^ 2) (HRS.Whole.withDensityReal rho) :=
    ⟨hm.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => sq_nonneg _)).2
        (lt_of_le_of_lt (hK x) ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  have h1 := ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun z => sq_nonneg _)
  have h2 : ENNReal.ofReal (∫ z, Q x z ^ 2 ∂HRS.Whole.withDensityReal rho) ≤
      ENNReal.ofReal (4 * A ^ 2 * K0 * jbracket x ^ (4 * M)) := by rw [h1]; exact hK x
  have hpos : 0 ≤ 4 * A ^ 2 * K0 * jbracket x ^ (4 * M) :=
    mul_nonneg (by positivity) (s82p2_jb_rpow_nonneg _ x)
  exact (ENNReal.ofReal_le_ofReal_iff hpos).1 h2

/-- The difference `ψ_{x,y} = Q(y,·) - Q(x,·)`: all hypotheses of the centered-sum lemma. -/
lemma s82p2_psi_facts {d : ℕ} {a beta M A K0 : ℝ} (hK0 : 0 ≤ K0) {rho : Euc d → ℝ}
    {f : Euc d → ℝ} {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q)
    (hK : ∀ x : Euc d, ∫⁻ z, ENNReal.ofReal (Q x z ^ 2) ∂HRS.Whole.withDensityReal rho ≤
        ENNReal.ofReal (4 * A ^ 2 * K0 * jbracket x ^ (4 * M))) (x y : Euc d) :
    Measurable (fun z => Q y z - Q x z) ∧
    Integrable (fun z => (Q y z - Q x z) ^ 2) (HRS.Whole.withDensityReal rho) ∧
    (∫ z, (Q y z - Q x z) ∂HRS.Whole.withDensityReal rho = 0) ∧
    ∫ z, (Q y z - Q x z) ^ 2 ∂HRS.Whole.withDensityReal rho ≤
      8 * A ^ 2 * K0 * (jbracket x ^ (4 * M) + jbracket y ^ (4 * M)) := by
  obtain ⟨hix, hbx⟩ := s82p2_Q_sq_integrable hK0 hQ hK x
  obtain ⟨hiy, hby⟩ := s82p2_Q_sq_integrable hK0 hQ hK y
  have hmx := s82p2_Q_row_measurable hQ x
  have hmy := s82p2_Q_row_measurable hQ y
  have hm : Measurable (fun z => Q y z - Q x z) := hmy.sub hmx
  have hpt : ∀ z, (Q y z - Q x z) ^ 2 ≤ 2 * Q y z ^ 2 + 2 * Q x z ^ 2 := fun z => by
    nlinarith [sq_nonneg (Q y z + Q x z)]
  have hint2 : Integrable (fun z => 2 * Q y z ^ 2 + 2 * Q x z ^ 2)
      (HRS.Whole.withDensityReal rho) := (hiy.const_mul 2).add (hix.const_mul 2)
  have hint : Integrable (fun z => (Q y z - Q x z) ^ 2) (HRS.Whole.withDensityReal rho) :=
    hint2.mono' (hm.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt z)
  refine ⟨hm, hint, ?_, ?_⟩
  · have h1 := hQ.canonical.2.1 x
    have h2 := hQ.canonical.2.1 y
    rw [integral_sub h2 h1, hQ.canonical.2.2.2 y, hQ.canonical.2.2.2 x]
    simp
  · refine (integral_mono hint hint2 hpt).trans ?_
    rw [integral_add (hiy.const_mul 2) (hix.const_mul 2), integral_const_mul, integral_const_mul]
    nlinarith [hbx, hby]

end HRS.MS.S82P2
