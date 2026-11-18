import HRS.MS.S82P2Canon1
import HRS.MS.S82P2Var1

/-!
# S8.2 (S82P2): variance of the pair statistic (UNCOMPILED DRAFT)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

theorem s82p2_pair_evariance_ref {d : ℕ} (hd : 2 ≤ d) {a beta C0 C1 M : ℝ} (hM : 0 ≤ M)
    (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (G c : ℝ) (hG : 0 < G) (hc : 0 < c) (hρ : HRS.Whole.IsProbDensity rho)
    (hρG : HRS.Whole.HasR2GaussianUpper G c rho) :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∀ (q : Euc d → ℝ) (h : ℕ → Euc d → ℝ),
      WeakReferenceSetup d a beta rho q h C0 → PinComparison beta rho q h C1 →
      ∀ (A : ℝ), 0 ≤ A → ∀ (f : Euc d → ℝ) (Q : Euc d → Euc d → ℝ),
      PairCorrector a beta rho M A f Q → ∀ m : ℕ, 1 ≤ m →
      evariance (Phase2S82.pairStatistic (N := m + 1) Q)
        (referenceLaw q h (HRS.Whole.withDensityReal rho) beta (m + 1) (m + 1)
          (fun i : Fin 0 => i.elim0)) ≤
        ENNReal.ofReal (CE * A ^ 2 / ((m + 1 : ℕ) : ℝ)) := by
  obtain ⟨CV, hCV0, hCV'⟩ := s82p2_pair_resample_i hd hM hbeta (C0 := C0) (C1 := C1) G c hG hc hρ hρG
  refine ⟨|C0| * CV, by positivity, ?_⟩
  intro q h hW hP A hA f Q hQ m hm
  have hC0 := hW.positive
  have hCV := hCV' q h hW hP
  rw [abs_of_pos hC0]
  have hN : 2 ≤ m + 1 := by omega
  have hNr : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hvar := hW.resampling (m + 1) hN 0 (m + 1) (by omega) (by omega) (by omega)
    (fun i : Fin 0 => i.elim0) (Phase2S82.pairStatistic (N := m + 1) Q)
    (s82p2_pair_memLp hd hM hbeta G c hG hc hρ hρG hW hP hA hQ hm)
  refine hvar.trans ?_
  calc ENNReal.ofReal C0 * ∑ i : Fin (m + 1), ∫⁻ X, ∫⁻ y, ENNReal.ofReal
        ((Phase2S82.pairStatistic (N := m + 1) Q (Function.update X i y) -
          Phase2S82.pairStatistic (N := m + 1) Q X) ^ 2)
        ∂resampleLaw q h (HRS.Whole.withDensityReal rho) beta (m + 1)
          (fun i : Fin 0 => i.elim0) i X
        ∂referenceLaw q h (HRS.Whole.withDensityReal rho) beta (m + 1) (m + 1)
          (fun i : Fin 0 => i.elim0)
      ≤ ENNReal.ofReal C0 * ∑ i : Fin (m + 1),
          ENNReal.ofReal (CV * A ^ 2 / ((m + 1 : ℕ) : ℝ) ^ 2) := by
        gcongr with i _
        exact hCV A hA f Q hQ m hm i
    _ = ENNReal.ofReal (C0 * CV * A ^ 2 / ((m + 1 : ℕ) : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_mul hC0.le]
        congr 1
        field_simp

theorem s82p2_pair_evariance_canonical {d : ℕ} (hd : 2 ≤ d) {a beta C0 C1 M : ℝ} (hM : 0 ≤ M)
    (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (G c : ℝ) (hG : 0 < G) (hc : 0 < c) (hρ : HRS.Whole.IsProbDensity rho)
    (hρG : HRS.Whole.HasR2GaussianUpper G c rho) :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∀ (q : Euc d → ℝ) (h : ℕ → Euc d → ℝ),
      WeakReferenceSetup d a beta rho q h C0 → PinComparison beta rho q h C1 →
      ∀ (A : ℝ), 0 ≤ A → ∀ (f : Euc d → ℝ) (Q : Euc d → Euc d → ℝ),
      PairCorrector a beta rho M A f Q → ∀ N : ℕ, 2 ≤ N →
      evariance (Phase2S82.pairStatistic (N := N) Q) (canonicalP d N a beta) ≤
        ENNReal.ofReal (CE * A ^ 2 / N) := by
  obtain ⟨CE0, hCE0, hCE'⟩ := s82p2_pair_evariance_ref hd hM hbeta (C0 := C0) (C1 := C1) G c hG hc hρ hρG
  refine ⟨|C0| * CE0, by positivity, ?_⟩
  intro q h hW hP A hA f Q hQ N hN
  have hC0 := hW.positive
  have hCE := hCE' q h hW hP
  rw [abs_of_pos hC0]
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  haveI := s82p2_canonicalP_prob hW hN
  haveI : IsProbabilityMeasure (unpinnedReference q h (HRS.Whole.withDensityReal rho) beta (m + 1)) :=
    hW.probability (m + 1) hN 0 (m + 1) (by omega) (by omega) (fun i : Fin 0 => i.elim0)
  have hFm : Measurable (Phase2S82.pairStatistic (N := m + 1) Q) := by
    unfold Phase2S82.pairStatistic Phase2S82.pairSum
    refine measurable_const.mul (Finset.measurable_sum _ fun k _ =>
      Finset.measurable_sum _ fun l _ => ?_)
    exact s82p2_Q_meas_pair hQ k l
  have h1 := s82p2_evariance_le_of_le_smul (P := canonicalP d (m + 1) a beta)
    (Q := unpinnedReference q h (HRS.Whole.withDensityReal rho) beta (m + 1))
    (c := ENNReal.ofReal C0) ENNReal.ofReal_ne_top (hW.domination (m + 1) hN)
    (Phase2S82.pairStatistic (N := m + 1) Q) hFm.aestronglyMeasurable
  refine h1.trans ?_
  refine (mul_le_mul_of_nonneg_left (hCE A hA f Q hQ m hm) bot_le).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul hC0.le]
  congr 1
  ring

end HRS.MS.S82P2
