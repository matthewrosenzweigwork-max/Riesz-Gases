import HRS.MS.R26T8AO03b4

/-!
# S8.2 T8A O03b (part 5): integrability of the pair statistic under the Gibbs law; linearity of `Psi`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U HRS.MS.S82W HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_o03b_psi_add {a beta M C : ℝ} {rho : Euc d → ℝ} {Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ}
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi) {A B : ℝ} {f g : Euc d → ℝ}
    (hf : TestBound (testOrder d) A f) (hg : TestBound (testOrder d) B g) :
    Psi (f + g) = Psi f + Psi g := by
  have := hPsi.linear f g A B hf hg 1
  simpa using this

theorem r26t8a_o03b_psi_smul {a beta M C : ℝ} {rho : Euc d → ℝ} {Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ}
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi) {A : ℝ} {f : Euc d → ℝ}
    (hf : TestBound (testOrder d) A f) (c : ℝ) : Psi (c • f) = c • Psi f := by
  have h0 : TestBound (testOrder d) 0 (fun _ : Euc d => (0 : ℝ)) := by
    refine ⟨contDiff_const, fun j hj1 hjk x => ?_⟩
    have : iteratedFDeriv ℝ j (fun _ : Euc d => (0 : ℝ)) x = 0 := by
      simp [iteratedFDeriv_const_of_ne (by omega : j ≠ 0)]
    rw [this, norm_zero]
  have := hPsi.linear (fun _ => 0) f 0 A h0 hf c
  have e : (fun _ : Euc d => (0 : ℝ)) + c • f = c • f := by funext x; simp
  rw [e, hPsi.constants 0] at this
  simpa using this

set_option maxHeartbeats 6400000 in
theorem r26t8a_o03b_ps_int (hd : 2 ≤ d) (N : ℕ) (hN : 2 ≤ N) (a beta M : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (hM : 0 ≤ M) {rho : Euc d → ℝ} (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    {f : Euc d → ℝ} {B : ℝ} (hB : 0 ≤ B) {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M B f Q) :
    Integrable (pairStatistic (N := N) Q) (canonicalP d N a beta) := by
  have hN0 : 0 < N := by omega
  haveI hPp : IsProbabilityMeasure (canonicalP d N a beta) := HRS.MS.S82U.u4_prob (N := N) hd ha hbeta
  set P := canonicalP d N a beta with hPdef
  obtain ⟨K1, Cb, M', hK10, hCb0, hMM', hSt⟩ := r26t8a_o02_stat_bounds hd a beta M ha hbeta hM hrho
  have hM'0 : 0 ≤ M' := le_trans hM hMM'
  obtain ⟨Cg, p, q, hCg, hp, hq, hG⟩ := r26t8a_o02_tame (N := N) hd hM hM'0
  have hEint : Integrable (u4Env (d := d) (N := N) p q) P := by
    refine Integrable.mono' (u4_env_L2 hd hN0 ha hbeta hp hq) (u4_Env_meas (d := d) (N := N) p q).aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => ?_)
    have h1 := u4Env_ge_one (d := d) (N := N) hp (q := q) X
    rw [Real.norm_of_nonneg (by linarith)]
    nlinarith
  have hae0 : ∀ᵐ X ∂P, X ∉ eucCollisionSet d N := by
    rw [ae_iff]; simpa using HRS.MS.S82U.u4_P_coll hd N a beta
  have hmeas : AEStronglyMeasurable (pairStatistic (N := N) Q) P := by
    have key : ∀ i j : Fin N, Measurable (fun X : EucConfig d N => Q (X i) (X j)) := fun i j => by
      have h2 : Measurable (fun X : EucConfig d N => (X i, X j)) :=
        (measurable_pi_apply i).prodMk (measurable_pi_apply j)
      exact hQ.measurable.comp h2
    have : Measurable (pairStatistic (N := N) Q) := by
      unfold pairStatistic Phase2S82.pairSum
      refine measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_)
      exact key i j
    exact this.aestronglyMeasurable
  refine Integrable.mono' ((hEint.const_mul Cg).const_mul (5 * (N : ℝ) ^ (-(3 / 2 : ℝ)) * B)) hmeas ?_
  filter_upwards [hae0] with X hX
  rw [Real.norm_eq_abs]
  have h1 := (hSt f B hB Q hQ N X hX).1
  have h2 := (r26t8a_o02_each_le (hG X hX)).1
  refine h1.trans ?_
  have : 0 ≤ 5 * (N : ℝ) ^ (-(3 / 2 : ℝ)) * B := by
    have := Real.rpow_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (-(3 / 2 : ℝ)); positivity
  calc 5 * (N : ℝ) ^ (-(3 / 2 : ℝ)) * (B * r26t8a_o02_Wb M X)
      = 5 * (N : ℝ) ^ (-(3 / 2 : ℝ)) * B * r26t8a_o02_Wb M X := by ring
    _ ≤ 5 * (N : ℝ) ^ (-(3 / 2 : ℝ)) * B * (Cg * u4Env (d := d) (N := N) p q X) :=
        mul_le_mul_of_nonneg_left h2 this

end HRS.MS.R26T8A
