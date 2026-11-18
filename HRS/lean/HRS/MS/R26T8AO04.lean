import HRS.MS.R26T8AO03b
import HRS.MS.R26T8AO04f

/-!
# S8.2 T8A O04: `r26t8a_noise_regular` (Pro contract, verbatim)
The actual normal-form noise is jointly measurable, progressive and square-integrable.  Joint measurability from
O04c (profile `G`) and O04b (joint measurability of `X`); progressive by O04f (time-and-state dependent
functional of the progressive path); the energy bound from O04e (Gibbs law at each time and the `NormalFormFamily`
bound for `ageTest j (b - r)`) integrated in O04f.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd

set_option maxHeartbeats 6400000 in
theorem r26t8a_noise_regular (d N : ℕ) (hd : 2≤d) (hN : 2≤N) (a beta m M C Cf c : ℝ)
    (ha : 0<a) (hbeta : 0<beta) (hM : 0≤M) (hC : 0≤C)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) {Omega : Type} [mOmega : MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (X0 : Omega → EucConfig d N) (W : ℝ≥0 → Omega → Fin N → Euc d)
    (X : ℝ≥0 → Omega → EucConfig d N)
    (hX : IsCanonicalRealization d (criticalS d) a beta N P X0 W X)
    (F : Filtration ℝ mOmega) (W' : ℝ≥0 → Omega → (Fin N×Fin d) → ℝ)
    (hfilt : IsWholeFilteredSolution P F W' W X) (alpha : MultiIndex d) (j : ℕ) (hj : j≤1) :
    Measurable (fun p : (ℝ×ℝ)×Omega => if 0≤p.1.2 ∧ p.1.2≤p.1.1 then
      r26t8a_noiseAge a beta m rho Psi alpha X j p.1.1 p.1.2 p.2 else 0) ∧
    (∀ b : ℝ, 0≤b → IsProgressiveL2 P F
      (r26t8a_clipIntegrand 0 b (r26t8a_noiseAge a beta m rho Psi alpha X j b))) ∧
    (∀ l b : ℝ, 0≤l → l≤b →
      r26t8a_itoEnergy P (r26t8a_noiseAge a beta m rho Psi alpha X j b) l b ≤
        ENNReal.ofReal ((2/beta)*(C*Cf*HRS.MS.S82BD.s82Weight d m alpha)^2/(N:ℝ))*
          ∫⁻ r in Set.Icc l b, ENNReal.ofReal (Real.exp (-2*c*(b-r)))) := by
  classical
  have hGm := fun i => r26t8a_o04_G_meas d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha j hj i
  have hXm : Measurable (fun q : ℝ × Omega => X q.1.toNNReal q.2) := r26t8a_o04_X_meas hfilt.progressive
  have hen := r26t8a_o04_energy_total d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb P X0 W X hX F
    W' hfilt alpha j hj
  refine ⟨?_, fun b hb => ?_, hen⟩
  · -- joint measurability
    have heq : (fun p : (ℝ×ℝ)×Omega => if 0≤p.1.2 ∧ p.1.2≤p.1.1 then
        r26t8a_noiseAge a beta m rho Psi alpha X j p.1.1 p.1.2 p.2 else 0) =
        fun p i => r26t8a_o04_G d N a beta m rho Psi alpha j p.1.1 p.1.2 (X p.1.2.toNNReal p.2) i := by
      funext p
      by_cases h : 0 ≤ p.1.2 ∧ p.1.2 ≤ p.1.1
      · simp only [h, and_self, if_true]; rfl
      · funext i
        simp only [h, if_false]
        unfold r26t8a_o04_G
        rw [if_neg (fun h' => h ⟨h'.1, h'.2.1⟩)]
        rfl
    rw [heq]
    refine measurable_pi_iff.2 fun i => ?_
    have hcomp : Measurable (fun p : (ℝ×ℝ)×Omega => (p.1.1, p.1.2, X p.1.2.toNNReal p.2)) :=
      (measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk (hXm.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
    exact (hGm i).comp hcomp
  · -- progressive and square integrable
    have hGc : Measurable (fun q : ℝ × EucConfig d N => fun i : Fin N × Fin d =>
        if q.1 ∈ Set.Icc (0 : ℝ) b then r26t8a_o04_G d N a beta m rho Psi alpha j b q.1 q.2 i else 0) := by
      refine measurable_pi_iff.2 fun i => ?_
      refine Measurable.ite (measurableSet_Icc.preimage measurable_fst) ?_ measurable_const
      exact (hGm i).comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))
    have hprog := r26t8a_o04_prog_time hfilt.progressive hGc
    refine ⟨hprog, fun T => ?_⟩
    have hle : sqIntegralOn P (r26t8a_clipIntegrand 0 b (r26t8a_noiseAge a beta m rho Psi alpha X j b)) T ≤
        r26t8a_itoEnergy P (r26t8a_noiseAge a beta m rho Psi alpha X j b) 0 b := by
      unfold sqIntegralOn r26t8a_itoEnergy
      refine lintegral_mono fun w => ?_
      have hpt : ∀ s : ℝ, ∑ i, ‖r26t8a_clipIntegrand 0 b (r26t8a_noiseAge a beta m rho Psi alpha X j b) s w i‖ₑ ^ 2 =
          (Set.Icc (0 : ℝ) b).indicator
            (fun s => ∑ i, ‖r26t8a_noiseAge a beta m rho Psi alpha X j b s w i‖ₑ ^ 2) s := by
        intro s
        by_cases hs : s ∈ Set.Icc (0 : ℝ) b
        · simp [r26t8a_clipIntegrand, hs]
        · simp [r26t8a_clipIntegrand, hs]
      simp_rw [hpt]
      calc ∫⁻ s in Set.Icc (0 : ℝ) T, (Set.Icc (0 : ℝ) b).indicator
            (fun s => ∑ i, ‖r26t8a_noiseAge a beta m rho Psi alpha X j b s w i‖ₑ ^ 2) s
          ≤ ∫⁻ s, (Set.Icc (0 : ℝ) b).indicator
            (fun s => ∑ i, ‖r26t8a_noiseAge a beta m rho Psi alpha X j b s w i‖ₑ ^ 2) s :=
            setLIntegral_le_lintegral _ _
        _ = ∫⁻ s in Set.Icc (0 : ℝ) b, ∑ i, ‖r26t8a_noiseAge a beta m rho Psi alpha X j b s w i‖ₑ ^ 2 :=
            lintegral_indicator measurableSet_Icc _
    refine lt_of_le_of_lt hle (lt_of_le_of_lt (hen 0 b le_rfl hb) ?_)
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
    have hint : Integrable (fun r : ℝ => Real.exp (-2 * c * (b - r))) (volume.restrict (Set.Icc (0 : ℝ) b)) := by
      have hcont : Continuous (fun r : ℝ => Real.exp (-2 * c * (b - r))) := by fun_prop
      exact hcont.integrableOn_Icc
    exact hint.lintegral_lt_top

end HRS.MS.R26T8A

end
