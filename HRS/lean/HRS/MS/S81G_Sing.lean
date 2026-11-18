import HRS.MS.MfeConfAux100
import HRS.MS.MfeConfAux19
import HRS.Whole.HeadlineStatement

/-!
# S81G, packet G1: the singular canonical Gibbs law as an `sb1Gam`

For the quadratic gradient dynamics `D = quadraticGradientDyn d s a β` and the Riesz kernel `g`:
* `s81g_canonical_eq`: `canonicalGibbs g (confinement a) N β = sb1Gam D g N` (even kernel, `0 < Z`);
* `s81g_gam_prob`: probability measure under measurability of `sb1Hs` (the S.B.1 lemmas ask continuity);
* `s81g_pot`: `Sb1Pot (confinement a) B`, the lower bound `a/2 ‖x‖² ≤ confinement a x`;
* Riesz kernel: even, measurable, `-log(1+|x|) ≤ g` (`0 ≤ s`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.MS.MfeConf HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S81G

variable {d N : ℕ}

theorem s81g_sum_erase (f : Fin N → Fin N → ℝ) (hf : ∀ i j, f i j = f j i) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, f i j =
      2 * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), f i j := by
  have h1 : ∀ i, ∑ j ∈ Finset.univ.erase i, f i j =
      ∑ j, (if i < j then f i j else 0) + ∑ j, (if j < i then f i j else 0) := by
    intro i
    rw [← Finset.filter_ne' Finset.univ i, Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne', not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne, not_lt.2 h.le]
  simp_rw [h1, Finset.sum_add_distrib]
  have h2 : ∑ i : Fin N, ∑ j : Fin N, (if j < i then f i j else 0) =
      ∑ i : Fin N, ∑ j : Fin N, (if i < j then f i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hf]
  rw [h2]
  simp_rw [Finset.sum_filter]
  ring

theorem s81g_riesz_even (s : ℝ) (x : Euc d) :
    Whole.rieszKernel d s (-x) = Whole.rieszKernel d s x := by
  simp [Whole.rieszKernel]

theorem s81g_riesz_meas (s : ℝ) : Measurable (Whole.rieszKernel d s) := by
  unfold Whole.rieszKernel
  by_cases hs : s = 0
  · simp only [hs, ite_true]
    exact (Real.measurable_log.comp measurable_norm).neg
  · simp only [hs, ite_false]
    exact measurable_norm.pow_const _

theorem s81g_riesz_lower {s : ℝ} (_hs : 0 ≤ s) (x : Euc d) :
    -Real.log (1 + ‖x‖) ≤ Whole.rieszKernel d s x := by
  unfold Whole.rieszKernel
  by_cases h0 : s = 0
  · simp only [h0, ite_true]
    have : Real.log ‖x‖ ≤ Real.log (1 + ‖x‖) := by
      rcases (norm_nonneg x).eq_or_lt with h | h
      · rw [← h]; simp
      · exact Real.log_le_log h (by linarith)
    linarith
  · simp only [h0, ite_false]
    have h1 : 0 ≤ Real.log (1 + ‖x‖) := Real.log_nonneg (by linarith [norm_nonneg x])
    have h2 : 0 ≤ ‖x‖ ^ (-s) := Real.rpow_nonneg (norm_nonneg _) _
    linarith

theorem s81g_pot (a : ℝ) : ∃ B : ℝ, Sb1Pot (Whole.confinement a : Euc d → ℝ) B := by
  refine sb1_pot_quad (a • (1 : Matrix (Fin d) (Fin d) ℝ)) 0 0 fun x => ?_
  simp [Whole.confinement, Torus.matVec, inner_smul_right]
  ring

theorem s81g_conf_lower (a : ℝ) (x : Euc d) :
    a / 2 * ‖x‖ ^ 2 - 0 ≤ Whole.confinement a x := by
  simp [Whole.confinement]; ring_nf; exact le_rfl

theorem s81g_Hs_meas (D : Whole.WholeDyn d) {k : Euc d → ℝ} (hk : Measurable k) (hV : Continuous D.V)
    (N : ℕ) : Measurable (sb1Hs D k N) := by
  unfold sb1Hs p4k_pairSum
  refine Measurable.add (Measurable.const_mul ?_ _) ?_
  · refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    exact hk.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))
  · exact Finset.measurable_sum _ fun i _ => hV.measurable.comp (measurable_pi_apply i)

section Gen

variable {D : Whole.WholeDyn d} {k : Euc d → ℝ}

theorem s81g_Gw_meas (hHm : Measurable (sb1Hs D k N)) :
    Measurable fun x : Whole.EucConfig d N => Real.exp (-D.invβ⁻¹ * sb1Hs D k N x) :=
  Real.measurable_exp.comp (measurable_const.mul hHm)

theorem s81g_Gw_int (hθ : 0 < D.invβ) (hHm : Measurable (sb1Hs D k N))
    (hlow : ∀ x, -Real.log (1 + ‖x‖) ≤ k x)
    {cV CV : ℝ} (hcV : 0 < cV) (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x) :
    Integrable fun x : Whole.EucConfig d N => Real.exp (-D.invβ⁻¹ * sb1Hs D k N x) := by
  have hβ : 0 < D.invβ⁻¹ := inv_pos.2 hθ
  have hg : Integrable (fun Ξ : Whole.EucConfig d N =>
      Real.exp (D.invβ⁻¹ * (N * CV + (N : ℝ) ^ 2 / cV)) * Real.exp (-(D.invβ⁻¹ * cV / 2 * ‖Ξ‖ ^ 2))) volume :=
    (p4g_integrable_gauss_pi (c := D.invβ⁻¹ * cV / 2) (by positivity)).const_mul _
  refine hg.mono' (s81g_Gw_meas hHm).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact sb1_Gw_le hθ hlow hcV hV x

theorem s81g_gz_pos (hθ : 0 < D.invβ) (hHm : Measurable (sb1Hs D k N))
    (hlow : ∀ x, -Real.log (1 + ‖x‖) ≤ k x)
    {cV CV : ℝ} (hcV : 0 < cV) (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x) : 0 < sb1Gz D k N := by
  unfold sb1Gz
  exact integral_exp_pos (s81g_Gw_int hθ hHm hlow hcV hV)

theorem s81g_Gq_lintegral (hθ : 0 < D.invβ) (hHm : Measurable (sb1Hs D k N))
    (hlow : ∀ x, -Real.log (1 + ‖x‖) ≤ k x) {cV CV : ℝ} (hcV : 0 < cV)
    (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x) :
    ∫⁻ x, ENNReal.ofReal (sb1Gq D k N x) = 1 := by
  have hi := s81g_Gw_int hθ hHm hlow hcV hV
  have hz := s81g_gz_pos hθ hHm hlow hcV hV
  have hqi : Integrable (sb1Gq D k N) := hi.div_const _
  rw [← ofReal_integral_eq_lintegral_ofReal hqi (Eventually.of_forall fun x =>
    (div_pos (Real.exp_pos _) hz).le)]
  have : ∫ x, sb1Gq D k N x = 1 := by
    unfold sb1Gq
    rw [integral_div]
    exact div_self hz.ne'
  rw [this, ENNReal.ofReal_one]

theorem s81g_gam_prob (hθ : 0 < D.invβ) (hHm : Measurable (sb1Hs D k N))
    (hlow : ∀ x, -Real.log (1 + ‖x‖) ≤ k x) {cV CV : ℝ} (hcV : 0 < cV)
    (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x) :
    IsProbabilityMeasure (sb1Gam D k N) :=
  sb1Dm_prob (s81g_Gq_lintegral hθ hHm hlow hcV hV)

/-- the Hamiltonians agree for an even kernel -/
theorem s81g_Hs_eq (hev : ∀ x, k (-x) = k x) (Z : Whole.EucConfig d N) :
    sb1Hs D k N Z = Whole.canonicalHamiltonian k D.V Z := by
  unfold sb1Hs Whole.canonicalHamiltonian p4k_pairSum
  have h := s81g_sum_erase (N := N) (fun i j => k (Z i - Z j)) fun i j => by
    rw [← hev (Z i - Z j)]; simp
  rw [h, add_comm]
  congr 1
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0; simp
  · have : (N : ℝ) ≠ 0 := by exact_mod_cast h0.ne'
    field_simp <;> ring

/-- `canonicalGibbs` is `sb1Gam` -/
theorem s81g_canonical_eq {β : ℝ} (hβ : D.invβ⁻¹ = β) (hev : ∀ x, k (-x) = k x)
    (hz : 0 < sb1Gz D k N) :
    Whole.canonicalGibbs k D.V N β = sb1Gam D k N := by
  have hZ : Whole.canonicalPartition k D.V N β = sb1Gz D k N := by
    unfold Whole.canonicalPartition sb1Gz
    refine integral_congr_ae (Eventually.of_forall fun Z => ?_)
    simp only [s81g_Hs_eq hev Z, hβ]
  unfold Whole.canonicalGibbs sb1Gam sb1Dm sb1Gq
  rw [hZ, ← withDensity_smul' _ _ (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hz).ne')]
  congr 1
  funext Z
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [ENNReal.ofReal_div_of_pos hz, div_eq_mul_inv, mul_comm]
  rw [hβ, s81g_Hs_eq hev Z]

end Gen

end HRS.MS.S81G
