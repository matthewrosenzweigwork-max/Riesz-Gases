import HRS.MS.SA12X3L8
import HRS.MS.SA12AssemblyDefs
import HRS.MS.SA12LimitL13

/-!
# S.A.12 P2 (SA12X3), part A: `IsPerSol` is monotone in the regularity level; measurability of the periodic weak operator;
the time increment of the pairings of a weak solution
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Assembly

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12Limit

variable {d : ℕ}

theorem sa12x3p_isPerSol_mono {N N' : ℕ} (hN : N' ≤ N) {L : ℝ} {γ : Euc d → ℝ} {M : Matrix (Fin d) (Fin d) ℝ}
    {ν : ℝ} {μ : ℝ → Euc d → ℝ} {b : ℝ → Euc d → Euc d} {S : ℝ → Euc d → ℝ} {t : ℝ} {F : ℝ → Euc d → ℝ}
    (h : IsPerSol N L γ M ν μ b S t F) : IsPerSol N' L γ M ν μ b S t F :=
  ⟨⟨h.sol.smooth, h.sol.contF, h.sol.contG, fun j hj => h.sol.deriv_t j (hj.trans hN)⟩, h.periodic,
    fun τ hτ => ⟨(h.bdd τ hτ).1, fun j hj => (h.bdd τ hτ).2 j (hj.trans hN)⟩⟩

theorem sa12x3p_weakOpPer_aesm {L : ℝ} {γ : Euc d → ℝ} (hγ : LocallyIntegrable γ volume)
    {M : Matrix (Fin d) (Fin d) ℝ} {ν : ℝ} {μ : ℝ → Euc d → ℝ} {b : ℝ → Euc d → Euc d} {σ : ℝ}
    (hμ : ContDiff ℝ 1 (μ σ)) (hb : ContDiff ℝ 1 (b σ)) {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) :
    AEStronglyMeasurable (weakOpPer L γ M ν μ b σ ψ) volume := by
  have hψ2 : ContDiff ℝ 2 ψ := hψ.1.of_le (by simp)
  have hψ1 : ContDiff ℝ 1 ψ := hψ.1.of_le (by simp)
  have hlap : Continuous (Laplacian.laplacian ψ) := by
    have e : Laplacian.laplacian ψ = fun y => ∑ i, HRS.MS.UniqT3.D1 i (HRS.MS.UniqT3.D1 i ψ) y :=
      funext fun y => HRS.MS.UniqT3.lap_eq hψ2 y
    rw [e]
    exact continuous_finsetSum _ fun i _ => HRS.MS.UniqN2b.n2b_D1D1_cont hψ2 i i
  have hmov : Continuous (movDiv (fun y => ψ y • b σ y)) := by
    have hF1 : ContDiff ℝ 1 (fun y => ψ y • b σ y) := hψ1.smul hb
    unfold movDiv
    refine continuous_finsetSum _ fun i _ => ?_
    have := (hF1.continuous_fderiv one_ne_zero).clm_apply
      (continuous_const (y := (EuclideanSpace.single i (1 : ℝ) : Euc d)))
    exact (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp this
  have hnl : Continuous (nonlocalTestPer L γ M (μ σ) ψ) := by
    have e : nonlocalTestPer L γ M (μ σ) ψ = fun x => ∑ i : Fin d, ∑ j : Fin d, M j i *
        (fderiv ℝ (μ σ) x (EuclideanSpace.single j (1 : ℝ)) * HRS.Whole.convFun γ (HRS.MS.UniqT3.D1 i ψ) x +
          μ σ x * HRS.Whole.convFun γ (HRS.MS.UniqT3.D1 j (HRS.MS.UniqT3.D1 i ψ)) x) :=
      funext fun x => sa12x3n_nlper_eq hγ hψ.1 hψ.2 M hμ x
    rw [e]
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => continuous_const.mul ?_
    have hD1 : ContDiff ℝ ∞ (HRS.MS.UniqT3.D1 i ψ) := (hψ.1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hc1 := (sa12x3n_convFun_contDiff hγ (n := 1) ((hD1.of_le (by simp)))
      (HRS.MS.UniqT3.D1_supp hψ.2 i)).continuous
    have hD2 : ContDiff ℝ 1 (HRS.MS.UniqT3.D1 j (HRS.MS.UniqT3.D1 i ψ)) :=
      HRS.MS.UniqT3.D1_contDiff (hD1.of_le (by simp)) j
    have hc2 := (sa12x3n_convFun_contDiff hγ (n := 1) hD2
      (HRS.MS.UniqT3.D1_supp (HRS.MS.UniqT3.D1_supp hψ.2 i) j)).continuous
    have hfd : Continuous (fun x => fderiv ℝ (μ σ) x (EuclideanSpace.single j (1 : ℝ))) :=
      (hμ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact (hfd.mul hc1).add (hμ.continuous.mul hc2)
  have hind : AEStronglyMeasurable ((centeredBox d L).indicator (nonlocalTestPer L γ M (μ σ) ψ)) volume := by
    have hm : MeasurableSet (centeredBox d L) := by
      have : centeredBox d L = ⋂ i, ({z : Euc d | -(L / 2) ≤ z i} ∩ {z : Euc d | z i < L / 2}) := by
        ext z; simp [centeredBox]
      rw [this]
      have hproj : ∀ i : Fin d, Measurable fun z : Euc d => z i := fun i =>
        (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.measurable
      exact MeasurableSet.iInter fun i =>
        (measurableSet_le measurable_const (hproj i)).inter (measurableSet_lt (hproj i) measurable_const)
    exact (hnl.aestronglyMeasurable).indicator hm
  unfold weakOpPer
  exact ((continuous_const.mul hlap).aestronglyMeasurable.sub hmov.aestronglyMeasurable).sub hind

end HRS.MH.AdjointRd.Phase2SA12Assembly
