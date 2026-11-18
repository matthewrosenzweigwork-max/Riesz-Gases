import HRS.MS.R26T8AO05c

/-!
# S8.2 T8A O04 (part a): the coordinates of the configuration gradient of the age corrector are continuous off collisions
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d N : ℕ}

theorem r26t8a_o04_cg_coord {F : EucConfig d N → ℝ} {X : EucConfig d N} (hF : DifferentiableAt ℝ F X)
    (i : Fin N) (k : Fin d) :
    Phase2S82.configGrad F X i k =
      fderiv ℝ F X (r26t8a_o03b_iota d N i (EuclideanSpace.single k (1 : ℝ))) := by
  have h := r26t8a_o03b_slice_grad hF i (EuclideanSpace.single k (1 : ℝ))
  rw [← h]
  simp [EuclideanSpace.inner_single_left]

set_option maxHeartbeats 6400000 in
theorem r26t8a_o04_H_contOn (d N : ℕ) (hd : 2≤d) (hN : 2≤N) (a beta m M C Cf c : ℝ)
    (ha : 0<a) (hbeta : 0<beta) (hM : 0≤M) (hC : 0≤C)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) (alpha : MultiIndex d) (j : ℕ) (hj : j ≤ 1)
    (i : Fin N) (k : Fin d) :
    ContinuousOn (fun q : ℝ × EucConfig d N =>
      Phase2S82.configGrad (r26t8a_QAge (N := N) a beta m rho Psi alpha j q.1) q.2 i k)
      (Set.Ici 0 ×ˢ (eucCollisionSet d N)ᶜ) := by
  obtain ⟨hQc, -, -, -⟩ := r26t8a_normal_age_FTC d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi
    horb alpha j hj
  have h1 := (r26t8a_o05c_eval_cont (E := EucConfig d N)
    (fun _ : Fin 1 => r26t8a_o03b_iota d N i (EuclideanSpace.single k (1 : ℝ)))).comp_continuousOn
    (hQc 1 (by norm_num))
  refine h1.congr fun q hq => ?_
  obtain ⟨A, hA⟩ : ∃ A, TestBound (testOrder d) A (r26t8a_ageTest a beta m rho alpha j q.1) :=
    ⟨_, horb.bound alpha q.1 hq.1 j (by omega)⟩
  have hdiff : DifferentiableAt ℝ (r26t8a_QAge (N := N) a beta m rho Psi alpha j q.1) q.2 :=
    (r26t8a_o03b_Q_contDiffAt N hd a beta M C hC rho Psi hPsi hA hq.2).differentiableAt (by norm_num)
  simp only [Function.comp]
  rw [r26t8a_o04_cg_coord hdiff i k, iteratedFDeriv_one_apply]

end HRS.MS.R26T8A

end
