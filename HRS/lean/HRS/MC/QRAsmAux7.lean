import HRS.MC.QRVocab
import HRS.MC.QRAsmAux6

/-!
# QRAsm, auxiliary file 7: the sum over output modes and the facts about the regime's densities
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace HRS.MC.QRSpec.Asm

open HRS.Sec7

variable {Ω : Type} [MeasurableSpace Ω]

/-- If every Fourier coefficient of `Z` is `≤ M ⟨k⟩^{(d+3)/2}` in `L^q`, then `‖Z‖_{E_r}` is `≤ M · const` in `L^q`. -/
lemma asm_final_sum {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} {r : ℝ} (hr : r = 2 * (d : ℝ) + 6)
    (Z : Ω → NegSobolev d r) (hZm : Measurable Z) {q : ℝ} (hq : 2 ≤ q) (M : ℝ) (hM : 0 ≤ M)
    (hmodes : ∀ k : NonzeroLattice d, eLpNorm (fun ω => NegSobolev.fourierCoeff (Z ω) k)
      (ENNReal.ofReal q) P ≤ ENNReal.ofReal (M * Lattice.jp k.1 ^ (((d : ℝ) + 3) / 2))) :
    eLpNorm (fun ω => ‖Z ω‖) (ENNReal.ofReal q) P ≤ ENNReal.ofReal (M * Real.sqrt
      (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-2 * r) * (Lattice.jp k.1 ^ (((d : ℝ) + 3) / 2)) ^ 2)) := by
  have hsum : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-2 * r) *
      (M * Lattice.jp k.1 ^ (((d : ℝ) + 3) / 2)) ^ 2 := by
    refine ((asm_summable_wm hr).mul_left (M ^ 2)).congr fun k => ?_
    ring
  have h := asm_er_norm Z hZm hq (fun k => M * Lattice.jp k.1 ^ (((d : ℝ) + 3) / 2))
    (fun k => mul_nonneg hM (Real.rpow_nonneg (Torus.jp_pos k.1).le _)) hmodes hsum
  refine h.trans (le_of_eq ?_)
  congr 1
  have e : (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-2 * r) *
      (M * Lattice.jp k.1 ^ (((d : ℝ) + 3) / 2)) ^ 2) = M ^ 2 * ∑' k : NonzeroLattice d,
      Lattice.jp k.1 ^ (-2 * r) * (Lattice.jp k.1 ^ (((d : ℝ) + 3) / 2)) ^ 2 := by
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    ring
  rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hM]

/-- The densities `ρ^t` (`t ≥ 0`) and `ρ_β` of the regime are probability densities with a common upper bound. -/
lemma asm_regime_density {d : ℕ} (R : Regime d) : ∃ Mρ : ℝ,
    (∀ t : ℝ, 0 ≤ t → IsProbDensity (R.ρ t) ∧ ∀ x, R.ρ t x ≤ Mρ) ∧
      IsProbDensity R.ρβ ∧ ∀ x, R.ρβ x ≤ Mρ := by
  obtain ⟨m₀, M₀, -, hb⟩ := R.bounds
  obtain ⟨hth, hsm, -⟩ := R.thermal
  have hc : Continuous R.ρβ := HRS.MC.L2C6Aux.l2c6_cont_of_smooth hsm
  obtain ⟨Mβ, hMβ⟩ := (isCompact_range hc).bddAbove
  refine ⟨max M₀ Mβ, fun t ht => ⟨(R.mf (t + 1) (by linarith)).density t ⟨ht, by linarith⟩,
    fun x => ((hb t ht x).2).trans (le_max_left _ _)⟩, hth.1, fun x => ?_⟩
  exact (hMβ ⟨x, rfl⟩).trans (le_max_right _ _)

end HRS.MC.QRSpec.Asm

end
