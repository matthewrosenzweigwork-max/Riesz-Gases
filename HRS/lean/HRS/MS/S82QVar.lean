import HRS.MS.S82QSum
import HRS.MS.S82P2Canon1

/-!
# S8.2 (S82Q): variance of pair-type statistics from one-site rows, transfer to the physical law
* `s82q_var_rows`: if a one-site update changes `F` by `a (rho_i (update) - rho_i)`, then
  `evariance F <= C0 sum_i 4 a^2 int rho_i^2` (resampling + reversibility).
* `s82q_pair_template`: for a symmetric kernel `K`, `F = c * pairSum K`; the row second moment is
  disintegrated over the pinned coordinate and bounded by a function `Psi` with `int Psi dmu <= J`.
* `s82q_transfer`: `evariance` under `canonicalP` from `evariance` under the unpinned reference.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82Q
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2

lemma s82q_memLp_two_of_lintegral {α : Type*} [MeasurableSpace α] {P : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f P) (hfin : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂P ≠ ⊤) :
    MemLp f 2 P := by
  refine (memLp_two_iff_integrable_sq hf).2 ⟨(hf.pow 2), ?_⟩
  exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => sq_nonneg _)).2 (lt_top_iff_ne_top.2 hfin)

theorem s82q_var_rows {d : ℕ} {a beta C0 : ℝ} {rho : Euc d → ℝ} {q : Euc d → ℝ}
    {h : ℕ → Euc d → ℝ} [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
    (hW : WeakReferenceSetup d a beta rho q h C0) (hbeta : 0 < beta)
    {N : ℕ} (hN : 2 ≤ N) {p m : ℕ} (hp : p ≤ 2) (hnp : m + 1 + p ≤ N) (hNn : N - (m + 1 + p) ≤ 2)
    (pins : Fin p → Euc d) (F : EucConfig d (m + 1) → ℝ)
    (hF : MemLp F 2 (referenceLaw q h (HRS.Whole.withDensityReal rho) beta N (m + 1) pins))
    (rw' : Fin (m + 1) → EucConfig d (m + 1) → ℝ) (hrm : ∀ i, Measurable (rw' i)) (c : ℝ)
    (hdiff : ∀ i X y, F (Function.update X i y) - F X =
      c * (rw' i (Function.update X i y) - rw' i X)) :
    evariance F (referenceLaw q h (HRS.Whole.withDensityReal rho) beta N (m + 1) pins) ≤
      ENNReal.ofReal C0 * ∑ i : Fin (m + 1), ENNReal.ofReal (4 * c ^ 2) *
        ∫⁻ X, ENNReal.ofReal (rw' i X ^ 2)
          ∂referenceLaw q h (HRS.Whole.withDensityReal rho) beta N (m + 1) pins := by
  set mu := HRS.Whole.withDensityReal rho
  set ref := referenceLaw q h mu beta N (m + 1) pins with href
  have hvar := hW.resampling N hN p (m + 1) hp hnp hNn pins F hF
  refine hvar.trans ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) bot_le
  have hgm : Measurable (fun X : EucConfig d (m + 1) => ENNReal.ofReal (rw' i X ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((hrm i).pow_const 2)
  have hinv := s82q_inv_hw hW hbeta hN hp hnp pins i _ hgm
  have pt : ∀ (X : EucConfig d (m + 1)),
      ∫⁻ y, ENNReal.ofReal ((F (Function.update X i y) - F X) ^ 2)
          ∂resampleLaw q h mu beta N pins i X ≤
        ENNReal.ofReal (2 * c ^ 2) * (∫⁻ y, ENNReal.ofReal (rw' i (Function.update X i y) ^ 2)
          ∂resampleLaw q h mu beta N pins i X + ENNReal.ofReal (rw' i X ^ 2)) := by
    intro X
    haveI := s82q_res_prob hW hbeta hN pins i X
    calc ∫⁻ y, ENNReal.ofReal ((F (Function.update X i y) - F X) ^ 2)
            ∂resampleLaw q h mu beta N pins i X
        ≤ ∫⁻ y, ENNReal.ofReal (2 * c ^ 2) * (ENNReal.ofReal (rw' i (Function.update X i y) ^ 2) +
            ENNReal.ofReal (rw' i X ^ 2)) ∂resampleLaw q h mu beta N pins i X := by
          refine lintegral_mono fun y => ?_
          rw [hdiff, ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
            ← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          nlinarith [sq_nonneg (rw' i (Function.update X i y) + rw' i X), sq_nonneg c]
      _ = ENNReal.ofReal (2 * c ^ 2) * (∫⁻ y, ENNReal.ofReal (rw' i (Function.update X i y) ^ 2)
          ∂resampleLaw q h mu beta N pins i X + ENNReal.ofReal (rw' i X ^ 2)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_right _ measurable_const]
          simp
  calc ∫⁻ X, ∫⁻ y, ENNReal.ofReal ((F (Function.update X i y) - F X) ^ 2)
          ∂resampleLaw q h mu beta N pins i X ∂ref
      ≤ ∫⁻ X, ENNReal.ofReal (2 * c ^ 2) * (∫⁻ y, ENNReal.ofReal (rw' i (Function.update X i y) ^ 2)
          ∂resampleLaw q h mu beta N pins i X + ENNReal.ofReal (rw' i X ^ 2)) ∂ref :=
        lintegral_mono pt
    _ = ENNReal.ofReal (2 * c ^ 2) * (∫⁻ X, ∫⁻ y, ENNReal.ofReal (rw' i (Function.update X i y) ^ 2)
          ∂resampleLaw q h mu beta N pins i X ∂ref + ∫⁻ X, ENNReal.ofReal (rw' i X ^ 2) ∂ref) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_right _ hgm]
    _ = ENNReal.ofReal (4 * c ^ 2) * ∫⁻ X, ENNReal.ofReal (rw' i X ^ 2) ∂ref := by
        have h4 : ENNReal.ofReal (4 * c ^ 2) = ENNReal.ofReal (2 * c ^ 2) * 2 := by
          rw [show (4 * c ^ 2 : ℝ) = 2 * c ^ 2 * 2 by ring, ENNReal.ofReal_mul (by positivity)]
          simp
        rw [hinv, h4, mul_assoc, ← two_mul]

end HRS.MS.S82Q
