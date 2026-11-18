import HRS.MS.SA16Y3Ex5
import HRS.MS.SA16SNl3

/-!
# S.A.16 (SA16Y3) L2: pairing of the zeroth component with a function bounded on a ball and zero outside

`sa16y3_ell_sup_bound`: for `G ∈ WmpSpace d m p` and `N` a.e. strongly measurable with `|N| ≤ c` on `closedBall 0 R`
and `N = 0` outside: `|∫ wrep G · N| ≤ c · vol(closedBall 0 R)^{1/q} · ‖G‖` (`q` the conjugate exponent).
The constant depends only on `c, R, d, p`, i.e. it is uniform over all `N` with the same sup bound and support radius.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section L2
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

theorem sa16y3_ell_sup_bound {m : ℕ} (G : WmpSpace d m p) {N : Euc d → ℝ}
    (hNm : AEStronglyMeasurable N volume) {R c : ℝ} (hc : 0 ≤ c)
    (hN : ∀ x, |N x| ≤ c * (closedBall (0 : Euc d) R).indicator (fun _ => (1 : ℝ)) x) :
    |∫ x, wrep d m p G x * N x| ≤
      c * (volume (closedBall (0 : Euc d) R)).toReal ^ (1 / Real.conjExponent p) * ‖G‖ := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hp1 : 1 < p := by linarith
  have hpq := Real.HolderConjugate.conjExponent hp1
  set q := Real.conjExponent p with hq
  have hq1 : 1 < q := hpq.symm.lt
  have hq0 : 0 < q := by linarith
  have hB : MeasurableSet (closedBall (0 : Euc d) R) := measurableSet_closedBall
  have hBfin : volume (closedBall (0 : Euc d) R) ≠ ⊤ := measure_closedBall_lt_top.ne
  -- the two factors
  have hfmem : MemLp (fun x => ‖wrep d m p G x‖) (ENNReal.ofReal p) volume := (sa16y3_wrep_memLp G).norm
  have hgmem : MemLp (fun x => ‖N x‖) (ENNReal.ofReal q) volume := by
    have hind : MemLp ((closedBall (0 : Euc d) R).indicator (fun _ => c)) (ENNReal.ofReal q) volume :=
      memLp_indicator_const _ hB c (Or.inr hBfin)
    refine (hind.norm).mono hNm.norm ?_
    refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ closedBall (0 : Euc d) R
    · simp only [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg hc]
      simpa [Set.indicator_of_mem hx] using hN x
    · simp only [Set.indicator_of_notMem hx, norm_zero]
      have := hN x
      simp only [Set.indicator_of_notMem hx, mul_zero] at this
      simpa using this
  have h1 : |∫ x, wrep d m p G x * N x| ≤ ∫ x, ‖wrep d m p G x‖ * ‖N x‖ := by
    have := norm_integral_le_integral_norm (μ := (volume : Measure (Euc d))) (fun x => wrep d m p G x * N x)
    simpa [norm_mul] using this
  have h2 := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (μ := (volume : Measure (Euc d)))
    (f := fun x => ‖wrep d m p G x‖) (g := fun x => ‖N x‖) (Eventually.of_forall fun x => norm_nonneg _)
    (Eventually.of_forall fun x => norm_nonneg _) hfmem hgmem
  -- first factor
  have hF : (∫ x, ‖wrep d m p G x‖ ^ p) ^ (1 / p) ≤ ‖G‖ := by
    have hp0 : ENNReal.ofReal p ≠ 0 := by simpa using (by linarith : 0 < p)
    have e := (sa16y3_wrep_memLp G).eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top
    rw [ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ p)] at e
    have h3 := sa16y3_wrep_eLp G
    rw [e] at h3
    rw [← one_div] at h3
    exact (ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)).1 h3
  have hF0 : 0 ≤ (∫ x, ‖wrep d m p G x‖ ^ p) ^ (1 / p) :=
    Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _
  -- second factor
  have hGq : (∫ x, ‖N x‖ ^ q) ^ (1 / q) ≤
      c * (volume (closedBall (0 : Euc d) R)).toReal ^ (1 / q) := by
    have hint : Integrable ((closedBall (0 : Euc d) R).indicator (fun _ => c ^ q)) volume :=
      (integrable_indicator_iff hB).2 (integrableOn_const hBfin)
    have hle : ∫ x, ‖N x‖ ^ q ≤ (volume (closedBall (0 : Euc d) R)).toReal * c ^ q := by
      have h4 : ∫ x, ‖N x‖ ^ q ≤ ∫ x, (closedBall (0 : Euc d) R).indicator (fun _ => c ^ q) x := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _) hint
          (Eventually.of_forall fun x => ?_)
        by_cases hx : x ∈ closedBall (0 : Euc d) R
        · simp only [Set.indicator_of_mem hx]
          have := hN x
          simp only [Set.indicator_of_mem hx, mul_one] at this
          rw [Real.norm_eq_abs]
          exact Real.rpow_le_rpow (abs_nonneg _) this hq0.le
        · simp only [Set.indicator_of_notMem hx]
          have := hN x
          simp only [Set.indicator_of_notMem hx, mul_zero] at this
          have h5 : ‖N x‖ = 0 := by rw [Real.norm_eq_abs]; exact le_antisymm this (abs_nonneg _)
          rw [h5, Real.zero_rpow hq0.ne']
      refine h4.trans (le_of_eq ?_)
      rw [integral_indicator hB, setIntegral_const, smul_eq_mul]
      rfl
    calc (∫ x, ‖N x‖ ^ q) ^ (1 / q) ≤ ((volume (closedBall (0 : Euc d) R)).toReal * c ^ q) ^ (1 / q) :=
          Real.rpow_le_rpow (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) hle
            (by positivity)
      _ = (volume (closedBall (0 : Euc d) R)).toReal ^ (1 / q) * (c ^ q) ^ (1 / q) :=
          Real.mul_rpow ENNReal.toReal_nonneg (Real.rpow_nonneg hc _)
      _ = c * (volume (closedBall (0 : Euc d) R)).toReal ^ (1 / q) := by
          rw [one_div, Real.rpow_rpow_inv hc hq0.ne']; ring
  calc |∫ x, wrep d m p G x * N x| ≤ ∫ x, ‖wrep d m p G x‖ * ‖N x‖ := h1
    _ ≤ _ := h2
    _ ≤ ‖G‖ * (c * (volume (closedBall (0 : Euc d) R)).toReal ^ (1 / q)) :=
        mul_le_mul hF hGq (Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _) (norm_nonneg _)
    _ = _ := by ring

end L2

end HRS.Whole.AppendixA.Phase2SA16R
