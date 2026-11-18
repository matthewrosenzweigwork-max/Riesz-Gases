import HRS.MS.R26T8AB01
import HRS.MS.R26T8AS05

/-!
# S8.2 T8A B03 (part a): clipping a progressive `L²` integrand to a sub-interval; the noise energy on `[l,h]`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_b03_clip_L2 {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I]
    {P : Measure Omega} {F : Filtration ℝ mOmega} {Φ : ℝ → Omega → I → ℝ} (hΦ : IsProgressiveL2 P F Φ)
    (l h : ℝ) : IsProgressiveL2 P F (r26t8a_clipIntegrand l h Φ) := by
  classical
  refine ⟨?_, fun T => ?_⟩
  · intro i
    letI : MeasurableSpace (Set.Iic i × Omega) := Subtype.instMeasurableSpace.prod (F i)
    have h1 := hΦ.prog i
    have hs : MeasurableSet {p : Set.Iic i × Omega | (p.1 : ℝ) ∈ Set.Icc l h} :=
      (measurable_subtype_coe.comp measurable_fst) measurableSet_Icc
    refine measurable_pi_iff.2 fun k => ?_
    exact Measurable.ite hs ((measurable_pi_apply k).comp h1) measurable_const
  · refine lt_of_le_of_lt (sqIntegralOn_mono_of_enorm_le (g := Φ) (fun s w k => ?_) T) (hΦ.sq T)
    unfold r26t8a_clipIntegrand
    by_cases hs : s ∈ Set.Icc l h <;> simp [hs]

set_option maxHeartbeats 12800000 in
theorem r26t8a_b03_energy_interval (d N : ℕ) (hd : 2≤d) (hN : 2≤N) (a beta m M C Cf c : ℝ)
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
    (hfilt : IsWholeFilteredSolution P F W' W X) (alpha : MultiIndex d) (j : ℕ) (hj : j≤1)
    (l h b E : ℝ) (hl : 0 ≤ l) (hlh : l ≤ h) (hhb : h ≤ b) (hE : ∀ r ∈ Set.Icc l h, Real.exp (-2 * c * (b - r)) ≤ E) :
    r26t8a_itoEnergy P (r26t8a_noiseAge a beta m rho Psi alpha X j b) l h ≤
      ENNReal.ofReal ((2 / beta) * (C * Cf * HRS.MS.S82BD.s82Weight d m alpha) ^ 2 / (N : ℝ) * E * (h - l)) := by
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
  calc ∫⁻ r in Set.Icc l h, ∫⁻ w, ∑ i, ‖r26t8a_noiseAge a beta m rho Psi alpha X j b r w i‖ₑ ^ 2 ∂P
      ≤ ∫⁻ r in Set.Icc l h, ENNReal.ofReal (K * E) := by
        refine setLIntegral_mono' measurableSet_Icc fun r hr => ?_
        refine (r26t8a_o04_energy_at d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb P X0 W X hX F
          W' hfilt alpha j hj b r (hl.trans hr.1) (hr.2.trans hhb)).trans ?_
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hE r hr) hK0)
    _ = ENNReal.ofReal (K * E * (h - l)) := by
        rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
        have hE0 : 0 ≤ E := (Real.exp_pos _).le.trans (hE l ⟨le_rfl, hlh⟩)
        rw [← ENNReal.ofReal_mul (by positivity)]

end HRS.MS.R26T8A

end
