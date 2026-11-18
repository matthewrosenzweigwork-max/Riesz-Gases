import HRS.MS.R26T8AO04e

/-!
# S8.2 T8A O04 (part f): progressive measurability of a time-and-state dependent functional of a progressive path
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_o04_prog_time {Omega : Type*} [mOmega : MeasurableSpace Omega] {F : Filtration ℝ mOmega}
    {E γ : Type*} [MeasurableSpace E] [MeasurableSpace γ] {u : ℝ → Omega → E} (hu : IsProgressive F u)
    {g : ℝ × E → γ} (hg : Measurable g) :
    IsProgressive F (fun s w => g (s, u s w)) := by
  intro i
  have h1 : Measurable[Subtype.instMeasurableSpace.prod (F i)] (fun p : Set.Iic i × Omega => (p.1 : ℝ)) :=
    measurable_subtype_coe.comp measurable_fst
  exact hg.comp (h1.prodMk (hu i))

theorem r26t8a_o04_energy_total (d N : ℕ) (hd : 2≤d) (hN : 2≤N) (a beta m M C Cf c : ℝ)
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
    (hfilt : IsWholeFilteredSolution P F W' W X) (alpha : MultiIndex d) (j : ℕ) (hj : j≤1) :
    ∀ l b : ℝ, 0≤l → l≤b →
      r26t8a_itoEnergy P (r26t8a_noiseAge a beta m rho Psi alpha X j b) l b ≤
        ENNReal.ofReal ((2/beta)*(C*Cf*HRS.MS.S82BD.s82Weight d m alpha)^2/(N:ℝ))*
          ∫⁻ r in Set.Icc l b, ENNReal.ofReal (Real.exp (-2*c*(b-r))) := by
  intro l b hl hlb
  classical
  set K : ℝ := (2 / beta) * (C * Cf * HRS.MS.S82BD.s82Weight d m alpha) ^ 2 / (N : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  have hXm : Measurable (fun q : ℝ × Omega => X q.1.toNNReal q.2) :=
    r26t8a_o04_X_meas hfilt.progressive
  have hmeas : Measurable (fun p : Omega × ℝ =>
      ∑ i : Fin N × Fin d, ‖r26t8a_noiseAge a beta m rho Psi alpha X j b p.2 p.1 i‖ₑ ^ 2) := by
    refine Finset.measurable_sum _ fun i _ => ?_
    have hG := r26t8a_o04_G_meas d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha j hj i
    have hcomp : Measurable (fun p : Omega × ℝ => (b, p.2, X p.2.toNNReal p.1)) :=
      measurable_const.prodMk (measurable_snd.prodMk (hXm.comp (measurable_snd.prodMk measurable_fst)))
    exact (hG.comp hcomp).enorm.pow_const 2
  unfold r26t8a_itoEnergy
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  calc ∫⁻ r in Set.Icc l b, ∫⁻ w, ∑ i, ‖r26t8a_noiseAge a beta m rho Psi alpha X j b r w i‖ₑ ^ 2 ∂P
      ≤ ∫⁻ r in Set.Icc l b, ENNReal.ofReal (K * Real.exp (-2 * c * (b - r))) :=
        setLIntegral_mono' measurableSet_Icc fun r hr =>
          r26t8a_o04_energy_at d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb P X0 W X hX F W'
            hfilt alpha j hj b r (hl.trans hr.1) hr.2
    _ = ENNReal.ofReal K * ∫⁻ r in Set.Icc l b, ENNReal.ofReal (Real.exp (-2 * c * (b - r))) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun r => ?_
        rw [ENNReal.ofReal_mul hK0]

end HRS.MS.R26T8A

end
