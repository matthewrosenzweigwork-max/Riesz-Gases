import HRS.MS.R26T8AA09a1
import HRS.MS.S82TFinal
import HRS.MS.S82TAe
import HRS.MS.S82TForce

/-!
# S8.2 observed-time layer, packet T8A.A09a2: integrability of the error statistic from the pair-corrector envelopes

For a `PairCorrector` `Q` (no pin, no moment hypothesis), `errorStatistic C rho Q` is the sum of the pair statistic of
`pairJ`, the pair sum of `repeatedB` and the triple sum of `tripleG`, each of which is dominated off collisions by the
polynomial pole envelope (A09a1, using the measurable models `Jt`, `B0` and the triple model `G`), hence lies in `L²(canonicalP)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U

theorem r26t8a_a09a2_err_memLp (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) (a beta M A : ℝ) (ha : 0 < a)
    (hbeta : 0 < beta) (hM : 0 ≤ M) (hA : 0 ≤ A) (rho : Euc d → ℝ)
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) (f : Euc d → ℝ)
    (Q : Euc d → Euc d → ℝ) (hQ : PairCorrector a beta rho M A f Q) :
    MemLp (errorStatistic (critCoeff d a beta rho) rho Q) 2 (canonicalP d N a beta) := by
  classical
  have hN0 : 0 < N := by omega
  have hrho_eq := critical_thermal_eq d hd a beta ha hbeta hrho
  subst hrho_eq
  set rho := HRS.Whole.thermalDensity d (criticalS d) a beta with hrhodef
  set mu := HRS.Whole.withDensityReal rho with hmudef
  haveI hP : IsProbabilityMeasure (canonicalP d N a beta) := HRS.MS.S82U.u4_prob (N := N) hd ha hbeta
  have hae0 : ∀ᵐ X ∂(canonicalP d N a beta), X ∉ eucCollisionSet d N := by
    rw [ae_iff]; simpa using HRS.MS.S82U.u4_P_coll hd N a beta
  have hs0 : 0 ≤ criticalS d := by unfold criticalS; positivity
  have hsd : criticalS d < d := by
    unfold criticalS
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨Cth, cth, BU, hTh⟩ := S45.s45_thermal_data hd hs0 hsd ha hbeta
  haveI hμ : IsProbabilityMeasure mu := HRS.Whole.Q09A.measure_isProb hTh.prob
  have hρm : Measurable ((critCoeff d a beta rho).ρ 0) := hTh.prob.measurable
  have hmeas_sum : ∀ {F : Euc d → Euc d → ℝ}, Measurable (Function.uncurry F) →
      Measurable (fun X : EucConfig d N => Phase2S82.pairSum F X) := fun {F} hF => by
    unfold Phase2S82.pairSum
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    exact Measurable.comp (g := Function.uncurry F) (f := fun X : EucConfig d N => (X i, X j)) hF ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
  have hnoc : ∀ X : EucConfig d N, X ∉ eucCollisionSet d N → ∀ i j : Fin N, i ≠ j → X i ≠ X j :=
    fun X hX i j hij h => hX ⟨i, j, hij, h⟩
  -- the J part
  set Jt := HRS.MS.S82T.s82t_Jt (critCoeff d a beta rho) mu (HRS.MS.S82P2.s82p2_gt Q) with hJt
  have hJm : Measurable (Function.uncurry Jt) :=
    HRS.MS.S82T.s82t_Jt_measurable (critCoeff d a beta rho) mu hρm (HRS.MS.S82P2.s82p2_gt_measurable Q)
  have hJtame : u4Tame (fun X : EucConfig d N => (N : ℝ) ^ (-(3 / 2 : ℝ)) * Phase2S82.pairSum Jt X) :=
    u4Tame_const_mul _ (r26t8a_a09a1_pairSum_tame hd hM hA 1 fun x y hxy => by
      rw [hJt, ← HRS.MS.S82T.s82t_pairJ_eq hd hQ x y hxy, pow_one]
      exact (hQ.nonlocal.2 x y hxy))
  have hJmem : MemLp (fun X : EucConfig d N => (N : ℝ) ^ (-(3 / 2 : ℝ)) * Phase2S82.pairSum Jt X) 2
      (canonicalP d N a beta) :=
    u4Tame_memLp hd hN0 ha hbeta hJtame ((measurable_const.mul (hmeas_sum hJm)).aestronglyMeasurable)
  -- the B part
  obtain ⟨Kf, hKf0, hFmm, hKf⟩ := HRS.MS.S82T.s82t_forceMean_bdd hd ha hbeta
  set B0 := HRS.MS.S82T.s82t_B0 (forceMean rho) (HRS.MS.S82P2.s82p2_gt Q) with hB0
  have hBm : Measurable (Function.uncurry B0) :=
    HRS.MS.S82T.s82t_B0_measurable hFmm (HRS.MS.S82P2.s82p2_gt_measurable Q)
  have hσ0 : 0 ≤ HRS.Whole.movtr_sigma (criticalS d) :=
    HRS.MS.S82T.s82t_sigma_nonneg _ (by unfold criticalS; positivity)
  have hBtame : u4Tame (fun X : EucConfig d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) * Phase2S82.pairSum B0 X) :=
    u4Tame_const_mul _ (r26t8a_a09a1_pairSum_tame hd hM
      (mul_nonneg (by positivity : 0 ≤ 2 * HRS.Whole.movtr_sigma (criticalS d) + 2 * Kf) hA) 2
      fun x y hxy => by
        have := HRS.MS.S82T.s82t_B0_bound hd hQ hA hKf0 hKf x y hxy
        calc |B0 x y| ≤ _ := this
          _ = _ := by ring)
  have hBmem : MemLp (fun X : EucConfig d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) * Phase2S82.pairSum B0 X) 2
      (canonicalP d N a beta) :=
    u4Tame_memLp hd hN0 ha hbeta hBtame ((measurable_const.mul (hmeas_sum hBm)).aestronglyMeasurable)
  -- the triple part
  obtain ⟨CA, M', hCA, hM', H1⟩ := canonical_triple_and_bounds d hd a beta M ha hbeta hM
  obtain ⟨G, hGm, hGc, hGb, hBb⟩ := H1 rho hrho f A hA Q hQ
  have hTtame : u4Tame (fun X : EucConfig d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) * Phase2S82.tripleSum G X) :=
    u4Tame_const_mul _ (r26t8a_a09a1_tripleSum_tame hd hM' (mul_nonneg hCA hA)
      fun x y z hxy hxz hyz => by
        have := (hGb x y z hxy hxz hyz).2
        calc |G x y z| ≤ _ := this
          _ = _ := by ring)
  have hTmeas : Measurable (fun X : EucConfig d N => Phase2S82.tripleSum G X) := by
    unfold Phase2S82.tripleSum
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      Finset.measurable_sum _ fun k _ => ?_
    exact Measurable.comp (g := fun p : Euc d × Euc d × Euc d => G p.1 p.2.1 p.2.2)
      (f := fun X : EucConfig d N => (X i, X j, X k)) hGm
      ((measurable_pi_apply i).prodMk ((measurable_pi_apply j).prodMk (measurable_pi_apply k)))
  have hTmem : MemLp (fun X : EucConfig d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) * Phase2S82.tripleSum G X) 2
      (canonicalP d N a beta) :=
    u4Tame_memLp hd hN0 ha hbeta hTtame ((measurable_const.mul hTmeas).aestronglyMeasurable)
  -- assemble
  have hmem : MemLp (fun X : EucConfig d N => (-(2 / (N : ℝ))) * ((N : ℝ) ^ (-(3 / 2 : ℝ)) * Phase2S82.pairSum Jt X) +
      (N : ℝ) ^ (-(5 / 2 : ℝ)) * Phase2S82.tripleSum G X - (N : ℝ) ^ (-(5 / 2 : ℝ)) * Phase2S82.pairSum B0 X) 2
      (canonicalP d N a beta) :=
    ((hJmem.const_mul (-(2 / (N : ℝ)))).add hTmem).sub hBmem
  refine hmem.ae_eq ?_
  filter_upwards [hae0] with X hX
  have hGeq : Phase2S82.tripleSum G X = Phase2S82.tripleSum (tripleG (critCoeff d a beta rho) rho Q) X := by
    unfold Phase2S82.tripleSum
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => ?_
    have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk
    have hki : k ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
    exact (hGb (X i) (X j) (X k) (fun h => hX ⟨i, j, hij, h⟩) (fun h => hX ⟨i, k, hki.symm, h⟩)
      (fun h => hX ⟨j, k, hkj.symm, h⟩)).1
  have hJeq : Phase2S82.pairSum (pairJ (critCoeff d a beta rho) mu Q) X = Phase2S82.pairSum Jt X :=
    HRS.MS.S82T.s82t_pairSum_congr (hnoc X hX) (fun x y hxy => HRS.MS.S82T.s82t_pairJ_eq hd hQ x y hxy)
  have hBeq : Phase2S82.pairSum (repeatedB rho Q) X = Phase2S82.pairSum B0 X :=
    HRS.MS.S82T.s82t_pairSum_congr (hnoc X hX) (fun x y hxy => HRS.MS.S82T.s82t_repeatedB_eq hQ x y hxy)
  have hJeq' : Phase2S82.pairSum (pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q) X =
      Phase2S82.pairSum Jt X := hJeq
  simp only [errorStatistic, Phase2S82.pairStatistic]
  rw [hJeq', hBeq, ← hGeq]
  ring

end HRS.MS.R26T8A
