import HRS.MS.R26T8AB01a

/-!
# S8.2 T8A B02c: `L²` bound of the drift field `V = D - Q'` along the process at a fixed time
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd

theorem r26t8a_b02_transfer {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (μ : Measure E) (Xt : Omega → E) (g : E → ℝ)
    (hXm : AEMeasurable Xt P) (hlaw : P.map Xt = μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun w => g (Xt w)) 2 P = eLpNorm g 2 μ := by
  rw [← hlaw] at hg ⊢
  exact (eLpNorm_map_measure hg hXm).symm

set_option maxHeartbeats 6400000 in
theorem r26t8a_b02_Vnorm (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) (a beta m M C : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ) (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    {Omega : Type} [mOmega : MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (X0 : Omega → EucConfig d N) (W : ℝ≥0 → Omega → Fin N → Euc d) (X : ℝ≥0 → Omega → EucConfig d N)
    (hX : IsCanonicalRealization d (criticalS d) a beta N P X0 W X) (r : ℝ) (hr : 0 ≤ r)
    (alpha : MultiIndex d) (m' : ℝ) (i : ℕ) (v : ℝ) {A : ℝ}
    (hf0 : TestBound (testOrder d) A (r26t8a_ageTest a beta m' rho alpha i v))
    (hf1 : TestBound (testOrder d) A (r26t8a_ageTest a beta m' rho alpha (i + 1) v)) :
    MemLp (fun w => r26t8a_VAge a beta m' rho Psi alpha i v (X r.toNNReal w)) 2 P ∧
    eLpNorm (fun w => r26t8a_VAge a beta m' rho Psi alpha i v (X r.toNNReal w)) 2 P ≤
      ENNReal.ofReal (2 * (C * A * (N : ℝ) ^ (-(1 / 2 : ℝ)))) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  haveI hPp : IsProbabilityMeasure (canonicalP d N a beta) := HRS.MS.S82U.u4_prob (N := N) hd ha hbeta
  have hk : 1 ≤ testOrder d := by unfold testOrder; omega
  have hA := r26t8a_o03b_tb_nonneg hk hf0
  set t : ℝ≥0 := r.toNNReal with ht
  have hlaw : law P (X t) = canonicalP d N a beta :=
    hX.invariant P (t : ℝ) X0 W X hX.brownian hX.indep hX.init (hX.solution t) t le_rfl
  have hXm : Measurable (X t) := (hX.solution (t : ℝ)).adapted t
  have hEnn : ENNReal.ofReal (C * A * (N : ℝ) ^ (-(1 / 2 : ℝ))) ≠ ⊤ := ENNReal.ofReal_ne_top
  -- the two fields
  have hQm : ∀ f : Euc d → ℝ, ∀ B : ℝ, TestBound (testOrder d) B f →
      Measurable (r26t8a_correctedQ (N := N) a beta Psi f) := by
    intro f B hf
    have hB := r26t8a_o03b_tb_nonneg hk hf
    have hQ := hPsi.corrector f B hB hf
    have key : ∀ i j : Fin N, Measurable (fun Y : EucConfig d N => Psi f (Y i) (Y j)) := fun i j => by
      have h2 : Measurable (fun Y : EucConfig d N => (Y i, Y j)) :=
        (measurable_pi_apply i).prodMk (measurable_pi_apply j)
      exact hQ.measurable.comp h2
    have hps : Measurable (pairStatistic (N := N) (Psi f)) := by
      unfold pairStatistic Phase2S82.pairSum
      exact measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => key i j)
    exact hps.sub measurable_const
  have hbd : ∀ f : Euc d → ℝ, TestBound (testOrder d) A f →
      MemLp (r26t8a_correctedD (N := N) a beta rho Psi f) 2 (canonicalP d N a beta) ∧
      eLpNorm (r26t8a_correctedD (N := N) a beta rho Psi f) 2 (canonicalP d N a beta) ≤
        ENNReal.ofReal (C * A * (N : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      eLpNorm (r26t8a_correctedQ (N := N) a beta Psi f) 2 (canonicalP d N a beta) ≤
        ENNReal.ofReal (C * A * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
    intro f hf
    obtain ⟨hDm, hb⟩ := hPsi.bound N hN f A hA hf
    exact ⟨hDm, le_add_self.trans hb, (le_self_add.trans le_self_add).trans hb⟩
  obtain ⟨hD0m, hD0, -⟩ := hbd _ hf0
  obtain ⟨-, -, hQ1⟩ := hbd _ hf1
  have hDc : eLpNorm (fun w => r26t8a_correctedD (N := N) a beta rho Psi (r26t8a_ageTest a beta m' rho alpha i v)
      (X t w)) 2 P = eLpNorm (r26t8a_correctedD (N := N) a beta rho Psi (r26t8a_ageTest a beta m' rho alpha i v)) 2
        (canonicalP d N a beta) :=
    r26t8a_b02_transfer P _ (X t) _ hXm.aemeasurable hlaw hD0m.aestronglyMeasurable
  have hQc : eLpNorm (fun w => r26t8a_correctedQ (N := N) a beta Psi (r26t8a_ageTest a beta m' rho alpha (i + 1) v)
      (X t w)) 2 P = eLpNorm (r26t8a_correctedQ (N := N) a beta Psi (r26t8a_ageTest a beta m' rho alpha (i + 1) v)) 2
        (canonicalP d N a beta) :=
    r26t8a_b02_transfer P _ (X t) _ hXm.aemeasurable hlaw (hQm _ A hf1).aestronglyMeasurable
  have hDmem : MemLp (fun w => r26t8a_correctedD (N := N) a beta rho Psi (r26t8a_ageTest a beta m' rho alpha i v)
      (X t w)) 2 P :=
    memLp_iff.2 (by rw [hDc]; exact lt_of_le_of_lt hD0 ENNReal.ofReal_lt_top)
  have hQmem : MemLp (fun w => r26t8a_correctedQ (N := N) a beta Psi (r26t8a_ageTest a beta m' rho alpha (i + 1) v)
      (X t w)) 2 P :=
    memLp_iff.2 (by rw [hQc]; exact lt_of_le_of_lt hQ1 ENNReal.ofReal_lt_top)
  have hV : (fun w => r26t8a_VAge a beta m' rho Psi alpha i v (X t w)) =
      (fun w => r26t8a_correctedD (N := N) a beta rho Psi (r26t8a_ageTest a beta m' rho alpha i v) (X t w)) -
      (fun w => r26t8a_correctedQ (N := N) a beta Psi (r26t8a_ageTest a beta m' rho alpha (i + 1) v) (X t w)) := rfl
  rw [hV]
  refine ⟨hDmem.sub hQmem, ?_⟩
  refine (eLpNorm_sub_le (by norm_num)).trans ?_
  rw [hDc, hQc]
  calc _ ≤ ENNReal.ofReal (C * A * (N : ℝ) ^ (-(1 / 2 : ℝ))) + ENNReal.ofReal (C * A * (N : ℝ) ^ (-(1 / 2 : ℝ))) :=
        add_le_add hD0 hQ1
    _ = ENNReal.ofReal (2 * (C * A * (N : ℝ) ^ (-(1 / 2 : ℝ)))) := by
        have h0 : 0 ≤ C * A * (N : ℝ) ^ (-(1 / 2 : ℝ)) := mul_nonneg (mul_nonneg hC hA) (Real.rpow_nonneg hN0.le _)
        rw [two_mul, ENNReal.ofReal_add h0 h0]

end HRS.MS.R26T8A

end
