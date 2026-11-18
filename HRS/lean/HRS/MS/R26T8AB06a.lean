import HRS.MS.R26T8AB03

/-!
# S8.2 T8A B06 (part a): the diagonal noise `r ↦ noiseAge 0 r r` is progressive `L²` on `[a, a+T]` with energy `≤ K T`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

set_option maxHeartbeats 12800000 in
theorem r26t8a_b06_diag_energy (d N : ℕ) (hd : 2≤d) (hN : 2≤N) (a beta m M C Cf c : ℝ)
    (ha : 0<a) (hbeta : 0<beta) (hM : 0≤M) (hC : 0≤C)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) {Omega : Type} [mOmega : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X0 : Omega → EucConfig d N) (W : ℝ≥0 → Omega → Fin N → Euc d)
    (X : ℝ≥0 → Omega → EucConfig d N)
    (hX : IsCanonicalRealization d (criticalS d) a beta N P X0 W X)
    (F : Filtration ℝ mOmega) (W' : ℝ≥0 → Omega → (Fin N×Fin d) → ℝ)
    (hfilt : IsWholeFilteredSolution P F W' W X) (alpha : MultiIndex d)
    (a0 T : ℝ) (ha0 : 0 ≤ a0) (hT : 0 ≤ T) :
    r26t8a_itoEnergy P (fun r w i => r26t8a_noiseAge a beta m rho Psi alpha X 0 r r w i) a0 (a0 + T) ≤
      ENNReal.ofReal ((2 / beta) * (C * Cf * HRS.MS.S82BD.s82Weight d m alpha) ^ 2 / (N : ℝ) * T) := by
  classical
  set K : ℝ := (2 / beta) * (C * Cf * HRS.MS.S82BD.s82Weight d m alpha) ^ 2 / (N : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  have hXm : Measurable (fun q : ℝ × Omega => X q.1.toNNReal q.2) :=
    r26t8a_o04_X_meas hfilt.progressive
  have hmeas : Measurable (fun p : Omega × ℝ =>
      ∑ i : Fin N × Fin d, ‖r26t8a_noiseAge a beta m rho Psi alpha X 0 p.2 p.2 p.1 i‖ₑ ^ 2) := by
    refine Finset.measurable_sum _ fun i _ => ?_
    have hG := r26t8a_o04_G_meas d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha 0
      (by norm_num) i
    have hcomp : Measurable (fun p : Omega × ℝ => (p.2, p.2, X p.2.toNNReal p.1)) :=
      measurable_snd.prodMk (measurable_snd.prodMk (hXm.comp (measurable_snd.prodMk measurable_fst)))
    exact (hG.comp hcomp).enorm.pow_const 2
  unfold r26t8a_itoEnergy
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  calc ∫⁻ r in Set.Icc a0 (a0 + T), ∫⁻ w, ∑ i, ‖r26t8a_noiseAge a beta m rho Psi alpha X 0 r r w i‖ₑ ^ 2 ∂P
      ≤ ∫⁻ r in Set.Icc a0 (a0 + T), ENNReal.ofReal K := by
        refine setLIntegral_mono' measurableSet_Icc fun r hr => ?_
        have := r26t8a_o04_energy_at d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb P X0 W X hX F
          W' hfilt alpha 0 (by norm_num) r r (ha0.trans hr.1) le_rfl
        simpa [sub_self] using this
    _ = ENNReal.ofReal (K * T) := by
        rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
        rw [← ENNReal.ofReal_mul hK0]
        congr 1; ring

end HRS.MS.R26T8A

end
