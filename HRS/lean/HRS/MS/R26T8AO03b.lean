import HRS.MS.R26T8AO02
import HRS.MS.R26T8AO03a
import HRS.MS.R26T8AO03b7
import HRS.MS.R26T8AO03b18

/-!
# S8.2 T8A O03b: `r26t8a_normal_age_FTC` (Pro contract, verbatim)
Q and D age derivatives and the full pair-gradient FTC.  Assembled from the jet clauses (O03b7) and the `D`
clauses (O03b18); see the O03b1-18 files for the linearity, joint continuity and difference-quotient arguments.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd

theorem r26t8a_normal_age_FTC (d N : ℕ) (hd : 2≤d) (hN : 2≤N) (a beta m M C Cf c : ℝ)
    (ha : 0<a) (hbeta : 0<beta) (hM : 0≤M) (hC : 0≤C)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) (alpha : MultiIndex d) (j : ℕ) (hj : j≤1) :
    (∀ ell≤2, ContinuousOn (fun p : ℝ×EucConfig d N =>
      iteratedFDeriv ℝ ell (r26t8a_QAge a beta m rho Psi alpha j p.1) p.2)
      (Set.Ici 0 ×ˢ (eucCollisionSet d N)ᶜ)) ∧
    (∀ X∉eucCollisionSet d N, ∀ v : ℝ, 0≤v → ∀ ell≤2,
      HasDerivWithinAt (fun u => iteratedFDeriv ℝ ell (r26t8a_QAge a beta m rho Psi alpha j u) X)
        (iteratedFDeriv ℝ ell (r26t8a_QAge a beta m rho Psi alpha (j+1) v) X) (Set.Ici 0) v) ∧
    ContinuousOn (fun p : ℝ×EucConfig d N => r26t8a_DAge a beta m rho Psi alpha j p.1 p.2)
      (Set.Ici 0 ×ˢ (eucCollisionSet d N)ᶜ) ∧
    (∀ X∉eucCollisionSet d N, ∀ v : ℝ, 0≤v →
      HasDerivWithinAt (fun u => r26t8a_DAge a beta m rho Psi alpha j u X)
        (r26t8a_DAge a beta m rho Psi alpha (j+1) v X) (Set.Ici 0) v) := by
  obtain ⟨hQ1, hQ2⟩ := r26t8a_o03b_Q_claims d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb
    alpha j hj
  obtain ⟨hD1, hD2⟩ := r26t8a_o03b_D_claims d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb
    alpha j hj
  exact ⟨hQ1, hQ2, hD1, hD2⟩

end HRS.MS.R26T8A

end
