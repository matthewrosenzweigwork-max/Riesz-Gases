import HRS.MS.S82P2Grad6
import HRS.MS.S82P2Pair6

/-!
# S8.2 (S82P2): the pair-statistic moment bound for a fixed weak-reference setup (UNCOMPILED DRAFT)
Conditional on the centering of `∇_x Q` (`hcenter`); the variance part is unconditional.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

theorem s82p2_pair_moments_fixed {d : ℕ} (hd : 2 ≤ d) {a beta C0 C1 M : ℝ} (hM : 0 ≤ M)
    (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (G c : ℝ) (hG : 0 < G) (hc : 0 < c) (hρ : HRS.Whole.IsProbDensity rho)
    (hρG : HRS.Whole.HasR2GaussianUpper G c rho) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Euc d → ℝ) (h : ℕ → Euc d → ℝ),
      WeakReferenceSetup d a beta rho q h C0 → PinComparison beta rho q h C1 →
      ∀ (A : ℝ), 0 ≤ A → ∀ (f : Euc d → ℝ) (Q : Euc d → Euc d → ℝ),
      PairCorrector a beta rho M A f Q →
      (∀ᵐ x ∂HRS.Whole.withDensityReal rho,
        ∫ z, s82p2_gt Q x z ∂HRS.Whole.withDensityReal rho = 0) →
      ∀ N : ℕ, 2 ≤ N →
        MemLp (Phase2S82.pairStatistic (N := N) Q) 2 (canonicalP d N a beta) ∧
        (∀ i, MemLp (fun X : EucConfig d N =>
          Phase2S82.configGrad (Phase2S82.pairStatistic Q) X i) 2 (canonicalP d N a beta)) ∧
        evariance (Phase2S82.pairStatistic (N := N) Q) (canonicalP d N a beta) +
          (∫⁻ X, ∑ i, ‖Phase2S82.configGrad (Phase2S82.pairStatistic Q) X i‖ₑ ^ 2
            ∂canonicalP d N a beta) ≤ ENNReal.ofReal (C * A ^ 2 / N) := by
  haveI hmu : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) :=
    HRS.Whole.Q09A.measure_isProb hρ
  obtain ⟨CE, hCE0, hCE'⟩ := s82p2_pair_evariance_canonical hd hM hbeta (C0 := C0) (C1 := C1) G c hG hc hρ hρG
  obtain ⟨CG, hCG0, hCG'⟩ := s82p2_gradModel_bound hd hM hbeta (C0 := C0) (C1 := C1) G c hG hc hρ hρG
  refine ⟨CE + |C0| * CG, by positivity, ?_⟩
  intro q h hW hP A hA f Q hQ hcenter N hN
  have hC0 := hW.positive
  have hCE := hCE' q h hW hP
  have hCG := hCG' q h hW hP
  rw [abs_of_pos hC0]
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  haveI := s82p2_canonicalP_prob hW hN
  have hdom := hW.domination (m + 1) hN
  let pins0 : Fin 0 → Euc d := fun i => i.elim0
  have hprob0 : IsProbabilityMeasure (referenceLaw q h (HRS.Whole.withDensityReal rho) beta
      (m + 1) (m + 1) pins0) := hW.probability (m + 1) hN 0 (m + 1) (by omega) (by omega) pins0
  have hacP : canonicalP d (m + 1) a beta ≪ unpinnedReference q h
      (HRS.Whole.withDensityReal rho) beta (m + 1) :=
    Measure.absolutelyContinuous_of_le_smul hdom
  have hgae := s82p2_gradModel_ae hd hW hQ hm
  have hgaeP : ∀ᵐ X ∂canonicalP d (m + 1) a beta, ∀ i : Fin (m + 1),
      Phase2S82.configGrad (Phase2S82.pairStatistic (N := m + 1) Q) X i = s82p2_gradModel Q i X :=
    hacP.ae_le hgae
  -- L² membership of F
  have hFmemRef := s82p2_pair_memLp hd hM hbeta G c hG hc hρ hρG hW hP hA hQ hm
  have hFmem : MemLp (Phase2S82.pairStatistic (N := m + 1) Q) 2 (canonicalP d (m + 1) a beta) :=
    (hFmemRef.smul_measure ENNReal.ofReal_ne_top).mono_measure hdom
  -- the gradient integral
  have hgradInt : ∫⁻ X, ∑ i, ‖Phase2S82.configGrad (Phase2S82.pairStatistic Q) X i‖ₑ ^ 2
        ∂canonicalP d (m + 1) a beta ≤ ENNReal.ofReal (C0 * (CG * A ^ 2 / ((m + 1 : ℕ) : ℝ))) := by
    have h1 : ∫⁻ X, ∑ i, ‖Phase2S82.configGrad (Phase2S82.pairStatistic Q) X i‖ₑ ^ 2
          ∂canonicalP d (m + 1) a beta = ∫⁻ X, ∑ i, ENNReal.ofReal (‖s82p2_gradModel Q i X‖ ^ 2)
          ∂canonicalP d (m + 1) a beta := by
      refine lintegral_congr_ae (hgaeP.mono fun X hX => ?_)
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hX i, s82p2_enorm_sq_vec]
    rw [h1]
    calc ∫⁻ X, ∑ i, ENNReal.ofReal (‖s82p2_gradModel Q i X‖ ^ 2) ∂canonicalP d (m + 1) a beta
        ≤ ∫⁻ X, ∑ i, ENNReal.ofReal (‖s82p2_gradModel Q i X‖ ^ 2)
            ∂(ENNReal.ofReal C0 • unpinnedReference q h (HRS.Whole.withDensityReal rho) beta (m + 1)) :=
          lintegral_mono' hdom le_rfl
      _ = ENNReal.ofReal C0 * ∑ i, ∫⁻ X, ENNReal.ofReal (‖s82p2_gradModel Q i X‖ ^ 2)
            ∂unpinnedReference q h (HRS.Whole.withDensityReal rho) beta (m + 1) := by
          rw [lintegral_smul_measure, smul_eq_mul, lintegral_finset_sum]
          intro i _
          exact ENNReal.measurable_ofReal.comp ((s82p2_gradModel_measurable Q i).norm.pow_const 2)
      _ ≤ ENNReal.ofReal C0 * ∑ i : Fin (m + 1),
            ENNReal.ofReal (CG * A ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2) := by
          gcongr with i _
          exact hCG A hA f Q hQ hcenter m hm i
      _ = ENNReal.ofReal (C0 * (CG * A ^ 2 / ((m + 1 : ℕ) : ℝ))) := by
          have hNr : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ← ENNReal.ofReal_mul hC0.le]
          congr 1
          field_simp
  -- memLp of each gradient
  have hgradMem : ∀ i, MemLp (fun X : EucConfig d (m + 1) =>
      Phase2S82.configGrad (Phase2S82.pairStatistic Q) X i) 2 (canonicalP d (m + 1) a beta) := by
    intro i
    have hmeas : AEStronglyMeasurable (fun X : EucConfig d (m + 1) =>
        Phase2S82.configGrad (Phase2S82.pairStatistic Q) X i) (canonicalP d (m + 1) a beta) :=
      ((s82p2_gradModel_measurable Q i).aestronglyMeasurable).congr
        (hgaeP.mono fun X hX => (hX i).symm)
    refine (memLp_two_iff_integrable_sq_norm hmeas).2 ⟨(hmeas.norm.aemeasurable.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun X => sq_nonneg _)]
    refine lt_of_le_of_lt ?_ (lt_of_le_of_lt hgradInt ENNReal.ofReal_lt_top)
    have : ∀ X : EucConfig d (m + 1), ENNReal.ofReal (‖Phase2S82.configGrad (Phase2S82.pairStatistic Q) X i‖ ^ 2) ≤
        ∑ j, ‖Phase2S82.configGrad (Phase2S82.pairStatistic Q) X j‖ₑ ^ 2 := fun X => by
      rw [← s82p2_enorm_sq_vec]
      exact Finset.single_le_sum (f := fun j => ‖Phase2S82.configGrad (Phase2S82.pairStatistic Q) X j‖ₑ ^ 2)
        (fun _ _ => bot_le) (Finset.mem_univ i)
    exact lintegral_mono this
  refine ⟨hFmem, hgradMem, ?_⟩
  have hv := hCE A hA f Q hQ (m + 1) hN
  calc evariance (Phase2S82.pairStatistic (N := m + 1) Q) (canonicalP d (m + 1) a beta) +
        ∫⁻ X, ∑ i, ‖Phase2S82.configGrad (Phase2S82.pairStatistic Q) X i‖ₑ ^ 2 ∂canonicalP d (m + 1) a beta
      ≤ ENNReal.ofReal (CE * A ^ 2 / ((m + 1 : ℕ) : ℝ)) +
          ENNReal.ofReal (C0 * (CG * A ^ 2 / ((m + 1 : ℕ) : ℝ))) := add_le_add hv hgradInt
    _ = ENNReal.ofReal ((CE + C0 * CG) * A ^ 2 / ((m + 1 : ℕ) : ℝ)) := by
        have hNr : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end HRS.MS.S82P2
