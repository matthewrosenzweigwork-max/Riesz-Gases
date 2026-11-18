import HRS.MS.R26T8AO03b17

/-!
# S8.2 T8A O03b (part 18): the `D` clauses (joint continuity and age derivative)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U HRS.MS.S82W HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem r26t8a_o03b_D_claims (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) (a beta m M C Cf c : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) (alpha : MultiIndex d) (j : ℕ) (hj : j ≤ 1) :
    ContinuousOn (fun p : ℝ × EucConfig d N => r26t8a_DAge a beta m rho Psi alpha j p.1 p.2)
      (Set.Ici 0 ×ˢ (eucCollisionSet d N)ᶜ) ∧
    (∀ X ∉ eucCollisionSet d N, ∀ v : ℝ, 0 ≤ v →
      HasDerivWithinAt (fun u => r26t8a_DAge a beta m rho Psi alpha j u X)
        (r26t8a_DAge a beta m rho Psi alpha (j + 1) v X) (Set.Ici 0) v) := by
  have hGj : ∀ s : ℝ, 0 ≤ s → ∃ A, TestBound (testOrder d) A (r26t8a_ageTest a beta m rho alpha j s) :=
    fun s hs => ⟨_, horb.bound alpha s hs j (by omega)⟩
  have hGj1 : ∀ s : ℝ, 0 ≤ s → ∃ A, TestBound (testOrder d) A (r26t8a_ageTest a beta m rho alpha (j + 1) s) :=
    fun s hs => ⟨_, horb.bound alpha s hs (j + 1) (by omega)⟩
  refine ⟨?_, fun X hX v hv => ?_⟩
  · intro p hp
    obtain ⟨v0, x0⟩ := p
    obtain ⟨hv0, hx0⟩ := hp
    obtain ⟨r, hr, hrK, hrc⟩ := r26t8a_o03b_nbhd (N := N) (d := d) hx0
    obtain ⟨CK, hCK, hCKb⟩ := r26t8a_normal_local_bound d N hd hN a beta M C ha hbeta hM hC rho hrho Psi hPsi
      (closedBall x0 r) hrc hrK
    refine r26t8a_o03b_cont (T := EucConfig d N)
      (fun x f => r26t8a_correctedD (N := N) a beta rho Psi f x) (eucCollisionSet d N)ᶜ
      (r26t8a_ageTest a beta m rho alpha j) v0 hv0 x0 hx0
      (fun x hx => r26t8a_o03b_D_lin N hd hN a beta M C ha hbeta hM hC rho hrho Psi hPsi hx)
      ⟨closedBall x0 r, mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x0 hr), CK, hCK,
        fun x hx f A hA hTB => by
          rw [Real.norm_eq_abs]
          exact (hCKb f A hA hTB).2 x hx⟩
      hGj ?_ ?_
    · exact horb.continuity alpha j (by omega) v0 hv0
    · obtain ⟨A0, hA0⟩ := hGj v0 hv0
      exact (r26t8a_o03b_D_contOn N hd hN a beta M C ha hbeta hC rho hrho Psi hPsi hA0) x0 hx0
  · obtain ⟨CK, hCK, hCKb⟩ := r26t8a_normal_local_bound d N hd hN a beta M C ha hbeta hM hC rho hrho Psi hPsi
      {X} isCompact_singleton (by simpa using hX)
    exact r26t8a_o03b_deriv (Φ := fun f => r26t8a_correctedD (N := N) a beta rho Psi f X)
      (r26t8a_o03b_D_lin N hd hN a beta M C ha hbeta hM hC rho hrho Psi hPsi hX) hCK
      (fun f A hA hTB => by
        rw [Real.norm_eq_abs]
        exact (hCKb f A hA hTB).2 X rfl)
      (r26t8a_ageTest a beta m rho alpha j) (r26t8a_ageTest a beta m rho alpha (j + 1)) v hv hGj
      (hGj1 v hv) (r26t8a_age_difference_quotient a beta m Cf c rho horb alpha j hj v hv)

end HRS.MS.R26T8A
