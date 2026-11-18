import HRS.MS.WsInitGAux7
import HRS.MS.R2IidPathTie

/-!
# S21 packet G, part 8: the particle initial path in the cosine coordinates

* `s21g_coord_series`: `√N (pair μ_N U - HRS.Whole.pair ν U) = ∑_n κ_n e_n(t) √N (pair μ_N f_{n,α} - HRS.Whole.pair ν f_{n,α})`.
* `s21g_Theta_feature`: the `(n,α)` coordinate of `Θ (featureVec φ ν x)` is `√N (pair μ_N f_{n,α} - HRS.Whole.pair ν f_{n,α})`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21

open HRS HRS.Whole

variable {d : ℕ}

theorem s21g_coord_series {C : WholeCoeff d} {M T : ℝ} (hT : 0 < T) {k : ℕ}
    (hmem : ∀ n α, MemCb k (r2CosOrbitTest C M T n α))
    (hsum : Summable fun q : ℕ × MultiIndex d => cbNorm k (r2CosOrbitTest C M T q.1 q.2))
    (hcont : ∀ (α : MultiIndex d) (x : Euc d),
      ContinuousOn (fun t => propagatorW C 0 t (oscTestFun M α) x) (Set.Icc (0 : ℝ) T))
    {N : ℕ} (hN : 1 ≤ N) (ν : Measure (Euc d)) [IsProbabilityMeasure ν] (x : EucConfig d N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (α : MultiIndex d) :
    Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical x) (propagatorW C 0 t (oscTestFun M α)) -
        HRS.Whole.pair ν (propagatorW C 0 t (oscTestFun M α))) =
      ∑' n : ℕ, s11p_kap n * r2CosBasis T n t * (Real.sqrt N *
        (HRS.Whole.pair (HRS.Whole.empirical x) (r2CosOrbitTest C M T n α) - HRS.Whole.pair ν (r2CosOrbitTest C M T n α))) := by
  have hU := s11p_series C M hT hmem hsum hcont
  have h1 : HasSum (fun n : ℕ => s11p_kap n * r2CosBasis T n t * HRS.Whole.pair (HRS.Whole.empirical x) (r2CosOrbitTest C M T n α))
      (HRS.Whole.pair (HRS.Whole.empirical x) (propagatorW C 0 t (oscTestFun M α))) := by
    have e : ∀ n : ℕ, s11p_kap n * r2CosBasis T n t * HRS.Whole.pair (HRS.Whole.empirical x) (r2CosOrbitTest C M T n α) =
        (N : ℝ)⁻¹ * ∑ i, s11p_kap n * r2CosBasis T n t * r2CosOrbitTest C M T n α (x i) := by
      intro n
      rw [HRS.Whole.pair_empirical (by omega), ← Finset.mul_sum]; ring
    simp_rw [e]
    rw [HRS.Whole.pair_empirical (by omega)]
    refine (hasSum_sum (s := Finset.univ) (f := fun (i : Fin N) (n : ℕ) =>
      s11p_kap n * r2CosBasis T n t * r2CosOrbitTest C M T n α (x i))
      (a := fun i => propagatorW C 0 t (oscTestFun M α) (x i)) fun i _ => ?_).mul_left (N : ℝ)⁻¹
    exact s11p_orbit_hasSum C M hT hmem hsum hcont α (x i) t ht
  have h2 := s11p_mu_series (D := s11p_orbitData C M hmem hsum) (U := fun α t x => propagatorW C 0 t (oscTestFun M α) x)
    ν hT hU α t ht
  have h3 : HasSum (fun n : ℕ => Real.sqrt N * (s11p_kap n * r2CosBasis T n t *
        HRS.Whole.pair (HRS.Whole.empirical x) (r2CosOrbitTest C M T n α) -
        s11p_kap n * r2CosBasis T n t * HRS.Whole.pair ν (r2CosOrbitTest C M T n α)))
      (Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical x) (propagatorW C 0 t (oscTestFun M α)) -
        HRS.Whole.pair ν (propagatorW C 0 t (oscTestFun M α)))) := (h1.sub h2).mul_left (Real.sqrt N)
  refine h3.tsum_eq.symm.trans (tsum_congr fun n => ?_)
  ring

theorem s21g_Theta_feature {C : WholeCoeff d} {M T : ℝ} {k : ℕ} (σ : ℕ ≃ ℕ × MultiIndex d)
    (hφ : IsSummableFeatureFamily k (fun j => r2CosOrbitTest C M T (σ j).1 (σ j).2)) {N : ℕ} (hN : 1 ≤ N)
    (ν : Measure (Euc d)) [IsProbabilityMeasure ν] (x : EucConfig d N) (n : ℕ) (α : MultiIndex d) :
    (s21gTheta σ (featureVec (fun j => r2CosOrbitTest C M T (σ j).1 (σ j).2) ν x)).c (n, α) =
      Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical x) (r2CosOrbitTest C M T n α) - HRS.Whole.pair ν (r2CosOrbitTest C M T n α)) := by
  have h := s21gTheta_c σ (featureVec (fun j => r2CosOrbitTest C M T (σ j).1 (σ j).2) ν x) (σ.symm (n, α))
  rw [Equiv.apply_symm_apply] at h
  rw [h]
  unfold featureVec
  rw [S45.s45_coord_ofSeq (S45.s45_feature_memℓp hN hφ x)]
  simp

end HRS.MS.S21
