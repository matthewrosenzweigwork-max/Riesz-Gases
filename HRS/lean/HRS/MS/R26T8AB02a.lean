import HRS.MS.R26T8AO03b
import HRS.MS.R26T8AO06j

/-!
# S8.2 T8A B02a: joint continuity of `QAge j` for `j ≤ 2`

`r26t8a_o06_QAge_cont` stops at `j ≤ 1` because the age derivative is only claimed there; the continuity itself needs only the
bounds and the continuity of the feature orbits for `j ≤ 2` (`FeatureOrbits.bound`, `.continuity`).  Needed for the age
derivative `V1 = D1 - Q2` of the drift field.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set Metric
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U HRS.MS.S82W HRS.MS.Wad

set_option maxHeartbeats 6400000 in
theorem r26t8a_b02_QAge_cont (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) (a beta m M C Cf c : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) (alpha : MultiIndex d) (j : ℕ) (hj : j ≤ 2) :
    ContinuousOn (fun q : ℝ × EucConfig d N => r26t8a_QAge a beta m rho Psi alpha j q.1 q.2)
      (Set.Ici 0 ×ˢ (eucCollisionSet d N)ᶜ) := by
  have hGj : ∀ s : ℝ, 0 ≤ s → ∃ A, TestBound (testOrder d) A (r26t8a_ageTest a beta m rho alpha j s) :=
    fun s hs => ⟨_, horb.bound alpha s hs j hj⟩
  have hmain : ContinuousOn (fun p : ℝ × EucConfig d N =>
      iteratedFDeriv ℝ 0 (r26t8a_QAge a beta m rho Psi alpha j p.1) p.2)
      (Set.Ici 0 ×ˢ (eucCollisionSet d N)ᶜ) := by
    intro p hp
    obtain ⟨v0, x0⟩ := p
    obtain ⟨hv0, hx0⟩ := hp
    obtain ⟨r, hr, hrK, hrc⟩ := r26t8a_o03b_nbhd (N := N) (d := d) hx0
    obtain ⟨CK, hCK, hCKb⟩ := r26t8a_normal_local_bound d N hd hN a beta M C ha hbeta hM hC rho hrho Psi hPsi
      (closedBall x0 r) hrc hrK
    refine r26t8a_o03b_cont (T := EucConfig d N)
      (fun x f => iteratedFDeriv ℝ 0 (r26t8a_correctedQ (N := N) a beta Psi f) x) (eucCollisionSet d N)ᶜ
      (r26t8a_ageTest a beta m rho alpha j) v0 hv0 x0 hx0
      (fun x hx => r26t8a_o03b_Q_lin N hd hN a beta M C ha hbeta hM hC rho hrho Psi hPsi hx 0 (by norm_num))
      ⟨closedBall x0 r, mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x0 hr), CK, hCK,
        fun x hx f A hA hTB => (hCKb f A hA hTB).1 0 (by norm_num) x hx⟩
      hGj ?_ ?_
    · exact horb.continuity alpha j hj v0 hv0
    · obtain ⟨A0, hA0⟩ := hGj v0 hv0
      exact (r26t8a_o03b_Q_jet_contOn N hd a beta M C hC rho Psi hPsi hA0 0 (by norm_num) x0 hx0)
  let L0 : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => EucConfig d N) ℝ →L[ℝ] ℝ :=
    (continuousMultilinearCurryFin0 ℝ (EucConfig d N) ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have hL0 : ∀ (g : EucConfig d N → ℝ) (x : EucConfig d N), L0 (iteratedFDeriv ℝ 0 g x) = g x := by
    intro g x
    simp [L0, iteratedFDeriv_zero_eq_comp]
  have := L0.continuous.comp_continuousOn hmain
  refine this.congr fun p hp => ?_
  simp only [Function.comp, hL0]

end HRS.MS.R26T8A

end
