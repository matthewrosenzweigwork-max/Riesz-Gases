import HRS.MS.R26T8AB06a

/-!
# S8.2 T8A B06 (part b): the triangular pathwise FTC for the noise profile
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

set_option maxHeartbeats 12800000 in
theorem r26t8a_b06_tri_ftc (d N : ℕ) (hd : 2≤d) (hN : 2≤N) (a beta m M C Cf c : ℝ)
    (ha : 0<a) (hbeta : 0<beta) (hM : 0≤M) (hC : 0≤C)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) (alpha : MultiIndex d)
    {Omega : Type*} (X : ℝ≥0 → Omega → EucConfig d N) (w : Omega) (r e : ℝ) (hr : 0 ≤ r)
    (hx : X r.toNNReal w ∉ eucCollisionSet d N) (i : Fin N × Fin d) :
    IntegrableOn (fun t => r26t8a_noiseAge a beta m rho Psi alpha X 1 t r w i) (Set.Icc r e) ∧
    ∀ t ∈ Set.Icc r e, r26t8a_noiseAge a beta m rho Psi alpha X 0 t r w i =
      r26t8a_noiseAge a beta m rho Psi alpha X 0 r r w i +
        ∫ v in Set.Icc r t, r26t8a_noiseAge a beta m rho Psi alpha X 1 v r w i := by
  classical
  obtain ⟨hc1, hftc⟩ := r26t8a_b03_cg_ftc d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha
    (X r.toNNReal w) hx 0 (e - r) le_rfl i.1 i.2
  have hform : ∀ (jj : ℕ) (t : ℝ), r ≤ t → r26t8a_noiseAge a beta m rho Psi alpha X jj t r w i =
      Real.sqrt (2 / beta) * Phase2S82.configGrad (r26t8a_QAge (N := N) a beta m rho Psi alpha jj (0 + (t - r)))
        (X r.toNNReal w) i.1 i.2 := by
    intro jj t ht
    unfold r26t8a_noiseAge
    rw [if_pos ⟨hr, ht, hx⟩, zero_add]
  refine ⟨?_, fun t ht => ?_⟩
  · have hcont : ContinuousOn (fun t : ℝ => Phase2S82.configGrad (r26t8a_QAge (N := N) a beta m rho Psi alpha 1
        (0 + (t - r))) (X r.toNNReal w) i.1 i.2) (Set.Icc r e) := by
      exact ContinuousOn.comp (g := fun u : ℝ => Phase2S82.configGrad
        (r26t8a_QAge (N := N) a beta m rho Psi alpha 1 (0 + u)) (X r.toNNReal w) i.1 i.2)
        (f := fun t : ℝ => t - r) hc1 (continuousOn_id.sub continuousOn_const)
        (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    have := hcont.const_smul (Real.sqrt (2 / beta))
    refine (this.congr (fun t ht => ?_)).integrableOn_Icc
    simp only [smul_eq_mul]
    exact hform 1 t ht.1
  · have e1 := hform 0 t ht.1
    have e0 := hform 0 r le_rfl
    have hu : t - r ∈ Set.Icc (0 : ℝ) (e - r) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h1 := hftc (t - r) hu
    have h2 : ∫ v in Set.Icc r t, r26t8a_noiseAge a beta m rho Psi alpha X 1 v r w i =
        Real.sqrt (2 / beta) * ∫ s in Set.Icc 0 (t - r),
          Phase2S82.configGrad (r26t8a_QAge (N := N) a beta m rho Psi alpha 1 (0 + s)) (X r.toNNReal w) i.1 i.2 := by
      rw [← integral_const_mul]
      have h3 : ∫ v in Set.Icc r t, r26t8a_noiseAge a beta m rho Psi alpha X 1 v r w i =
          ∫ v in Set.Icc r t, Real.sqrt (2 / beta) *
            Phase2S82.configGrad (r26t8a_QAge (N := N) a beta m rho Psi alpha 1 (0 + (v - r))) (X r.toNNReal w) i.1 i.2 :=
        setIntegral_congr_fun measurableSet_Icc fun v hv => hform 1 v hv.1
      rw [h3, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.1,
        intervalIntegral.integral_comp_sub_right (fun s => Real.sqrt (2 / beta) *
          Phase2S82.configGrad (r26t8a_QAge (N := N) a beta m rho Psi alpha 1 (0 + s)) (X r.toNNReal w) i.1 i.2) r,
        sub_self, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [ht.1])]
    rw [e1, e0, h2, h1]
    ring

end HRS.MS.R26T8A

end
