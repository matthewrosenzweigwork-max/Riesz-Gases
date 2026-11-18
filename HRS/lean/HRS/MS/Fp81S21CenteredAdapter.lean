import HRS.MS.Fp81S21LeadingAdapter2
import HRS.MS.ProClosureS111WindowRestriction

/-!
# HRS S2.1(iii), SOL26 packet 8: centered-path adapter

Target statements, in the order required by the packet:

1. For `η_N = flucPathW ...` and `ζ_N = zetaPathW ...`, with
   `M_N := ∫ ω, η_N ω ∂P` as a Bochner integral in `OscPath`, prove
   `η_N =ᵐ[P] fun ω => ζ_N ω + M_N`.  The evaluation identity needed here is
   `L (∫ ω, η_N ω ∂P) = ∫ ω, L (η_N ω) ∂P` for each continuous linear
   evaluation functional `L`; the path identity also needs the moving
   empirical/mean-field evaluation identity and the a.e. continuity clauses.
2. Restrict a length `L + T` comparison at
   `b = max (a₀ - L) 0` to the recent interval.  The existing
   `fp81s21_recentWindowRestriction` supplies the offset geometry, and
   `physicalWindowRestriction` is the continuous linear map of norm at most
   one.  This file proves its law/W₁ contraction.
3. The intended mean-path bound is
   `‖M_N‖ ≤ C / Real.sqrt N`, with `C` uniform in the window start and the
   particle/Gaussian realizations.  See the author report for the missing
   horizon-uniform forcing input that prevents this statement from being
   exported from the present interfaces.
4. The intended centered envelope combines the raw bound and this translation
   bound, using that a Gaussian window has zero Bochner mean.

The first lemma below records the evaluation/interchange step.  The second
proves the restriction-map transfer used in item 2.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HRS.Fp81.S21

open HRS HRS.Whole

/-- Continuous linear evaluation commutes with the Bochner expectation of an
`OscPath`-valued random variable. -/
theorem fp81s21_pathIntegral_eval
    {d : ℕ} {m T : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (Y : Ω → OscPath d m T)
    (L : OscPath d m T →L[ℝ] ℝ) (hY : Integrable Y P) :
    L (∫ ω, Y ω ∂P) = ∫ ω, L (Y ω) ∂P := by
  exact (ContinuousLinearMap.integral_comp_comm L hY).symm

/-- The pointwise fluctuation identity in the whole-space dual:
mean-field centering equals actual-marginal centering plus the deterministic
mean-field bias. -/
theorem fp81s21_etaField_eq_zeta_add_mean
    {d N : ℕ} {m : ℝ} (hm : (d : ℝ) < m)
    (P : Measure (HRS.Whole.EucConfig d N)) [IsProbabilityMeasure P]
    (X : HRS.Whole.EucConfig d N) (μ : Measure (HRS.Euc d)) [IsProbabilityMeasure μ]
    (hN : 1 ≤ N) :
    HRS.Whole.etaB m X μ = HRS.Whole.zetaB m P X +
      Real.sqrt N • OscDual.ofMeasureDiff m (HRS.Whole.meanEmpirical P) μ := by
  exact HRS.Whole.eta_eq_zeta_add m hm P μ X hN

/-- A continuous linear map of norm at most one cannot increase `W₁`.
For `physicalWindowRestriction`, the norm premise is supplied by
`physicalWindowRestriction_norm_le`. -/
theorem fp81s21_wasserstein_restrict_clm
    {B B' : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [MeasurableSpace B] [BorelSpace B]
    [NormedAddCommGroup B'] [NormedSpace ℝ B']
    [MeasurableSpace B'] [BorelSpace B']
    (L : B →L[ℝ] B') (hL : ‖L‖ ≤ 1)
    (P Q : Measure B) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    wassersteinE 1 (P.map L) (Q.map L) ≤ wassersteinE 1 P Q := by
  calc
    wassersteinE 1 (P.map L) (Q.map L) ≤
        ENNReal.ofReal ‖L‖ * wassersteinE 1 P Q :=
      HRS.Main.wassersteinE_map_clm_le L 1 le_rfl P Q
    _ ≤ 1 * wassersteinE 1 P Q :=
      by
        gcongr
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hL
    _ = wassersteinE 1 P Q := one_mul _

/-- Law-level form of the restriction contraction.  The a.e. measurability
hypotheses ensure these are the genuine pushforward laws. -/
theorem fp81s21_law_restrict_wasserstein
    {d : ℕ} {m H T : ℝ} {u : ℝ} (hu : 0 ≤ u) (hH : u + T ≤ H)
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Q : Measure Ω'} [IsProbabilityMeasure Q]
    (Y : Ω → OscPath d m H) (Z : Ω' → OscPath d m H)
    (hY : AEMeasurable Y P) (hZ : AEMeasurable Z Q) :
    wassersteinE 1
      (law P (fun ω => HRS.MS.ProClosureS111.physicalWindowRestriction hu hH (Y ω)))
      (law Q (fun ω => HRS.MS.ProClosureS111.physicalWindowRestriction hu hH (Z ω))) ≤
    wassersteinE 1 (law P Y) (law Q Z) := by
  let R := HRS.MS.ProClosureS111.physicalWindowRestriction (d := d) (m := m) hu hH
  have hLawY : law P (fun ω => R (Y ω)) = (law P Y).map R := by
    unfold law
    exact (AEMeasurable.map_map_of_aemeasurable R.continuous.measurable.aemeasurable hY).symm
  have hLawZ : law Q (fun ω => R (Z ω)) = (law Q Z).map R := by
    unfold law
    exact (AEMeasurable.map_map_of_aemeasurable R.continuous.measurable.aemeasurable hZ).symm
  haveI : IsProbabilityMeasure (law P Y) :=
    (Measure.isProbabilityMeasure_map_iff hY).2 inferInstance
  haveI : IsProbabilityMeasure (law Q Z) :=
    (Measure.isProbabilityMeasure_map_iff hZ).2 inferInstance
  rw [hLawY, hLawZ]
  exact fp81s21_wasserstein_restrict_clm R
    (by
      apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1) fun w => ?_
      simpa [R] using HRS.MS.ProClosureS111.physicalWindowRestriction_norm_le hu hH w)
    (law P Y) (law Q Z)

#print axioms fp81s21_pathIntegral_eval
#print axioms fp81s21_etaField_eq_zeta_add_mean
#print axioms fp81s21_wasserstein_restrict_clm
#print axioms fp81s21_law_restrict_wasserstein

end HRS.Fp81.S21

end
