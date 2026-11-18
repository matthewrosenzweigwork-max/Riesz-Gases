import HRS.MS.R26T8AO06i
import HRS.MS.R26T8AO05c

/-!
# S8.2 T8A O06 (part j): the Itô drift of the backward corrector along a collision-free configuration
`itoDrift b (r ↦ QAge 0 (b-r)) X ... = -QAge 1 (b-s) X + DAge 0 (b-s) X - scalarForcing (ageTest 0 (b-s)) X`, and the
age values are jointly continuous.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MH.DualityRd

set_option maxHeartbeats 6400000 in
theorem r26t8a_o06_QAge_cont (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) (a beta m M C Cf c : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) (alpha : MultiIndex d) (j : ℕ) (hj : j ≤ 1) :
    ContinuousOn (fun q : ℝ × EucConfig d N => r26t8a_QAge a beta m rho Psi alpha j q.1 q.2)
      (Set.Ici 0 ×ˢ (eucCollisionSet d N)ᶜ) := by
  obtain ⟨hQc, -, -, -⟩ := r26t8a_normal_age_FTC d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi
    horb alpha j hj
  let L0 : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => EucConfig d N) ℝ →L[ℝ] ℝ :=
    (continuousMultilinearCurryFin0 ℝ (EucConfig d N) ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have hL0 : ∀ (g : EucConfig d N → ℝ) (x : EucConfig d N), L0 (iteratedFDeriv ℝ 0 g x) = g x := by
    intro g x
    simp [L0, iteratedFDeriv_zero_eq_comp]
  have := L0.continuous.comp_continuousOn (hQc 0 (by norm_num))
  refine this.congr fun p hp => ?_
  simp only [Function.comp, hL0]

set_option maxHeartbeats 6400000 in
theorem r26t8a_o06_drift_eq (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) (a beta m M C Cf c : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) (alpha : MultiIndex d) (b : ℝ) (hb : 0 < b)
    {Omega : Type*} (X : ℝ≥0 → Omega → EucConfig d N) (w : Omega) (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) b)
    (hX : X s.toNNReal w ∉ eucCollisionSet d N) :
    itoDrift b (fun r => r26t8a_QAge (N := N) a beta m rho Psi alpha 0 (b - r)) (ofNNRealTime X)
      (ofNNRealTime (fun (s : ℝ≥0) (ξ : Omega) => particleDriftW (quadraticGradientDyn d (criticalS d) a beta) (X s ξ)))
      (fun _ _ => noiseDir (quadraticGradientDyn d (criticalS d) a beta)) s w =
    -r26t8a_QAge a beta m rho Psi alpha 1 (b - s) (X s.toNNReal w) +
      r26t8a_DAge a beta m rho Psi alpha 0 (b - s) (X s.toNNReal w) -
      scalarForcing a beta rho (r26t8a_ageTest a beta m rho alpha 0 (b - s)) (X s.toNNReal w) := by
  obtain ⟨hC12, htime⟩ := r26t8a_backward_corrector_c12 d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi
    horb alpha b hb
  obtain ⟨A, hA⟩ : ∃ A, TestBound (testOrder d) A (r26t8a_ageTest a beta m rho alpha 0 (b - s)) :=
    ⟨_, horb.bound alpha (b - s) (sub_nonneg.2 hs.2) 0 (by norm_num)⟩
  have hk : 1 ≤ testOrder d := by unfold testOrder; omega
  have hA0 := r26t8a_o03b_tb_nonneg hk hA
  have h2 : ContDiffOn ℝ 2 (r26t8a_QAge (N := N) a beta m rho Psi alpha 0 (b - s)) (eucCollisionSet d N)ᶜ :=
    r26t8a_o03b_Q_contDiffOn N hd a beta M C hC rho Psi hPsi hA
  have hconv := r26t8a_o06_drift_conv (quadraticGradientDyn d (criticalS d) a beta)
    (by show 0 ≤ beta⁻¹; positivity) h2 hX
  have hid := hPsi.identity N hN _ A hA0 hA (X s.toNNReal w) hX
  have hder := htime s hs (X s.toNNReal w) hX
  unfold itoDrift
  simp only [ofNNRealTime_apply]
  rw [hder]
  have hid' : scalarForcing a beta rho (r26t8a_ageTest a beta m rho alpha 0 (b - s)) (X s.toNNReal w) =
      -particleGenerator (quadraticGradientDyn d (criticalS d) a beta)
        (r26t8a_QAge (N := N) a beta m rho Psi alpha 0 (b - s)) (X s.toNNReal w) +
      r26t8a_DAge (N := N) a beta m rho Psi alpha 0 (b - s) (X s.toNNReal w) := hid
  linarith [hconv, hid']

end HRS.MS.R26T8A

end
