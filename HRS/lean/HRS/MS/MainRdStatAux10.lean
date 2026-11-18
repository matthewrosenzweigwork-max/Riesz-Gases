import HRS.MS.MainRdStatAux9
import HRS.MS.PathFidiAux7
import HRS.Main.A8PAux23

/-!
# SA2, packet 7: the per-`N` smooth-metric bound for a finite family

`sa2_family`: orbit data of a family of tests; `sa2_smooth_N`: `smoothDist 2 ≤ E‖R‖ + E‖I_emp - Ĩ‖ + ½ cov` with every term bounded.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Uniform HRS.GF HRS.Whole.AppendixALemmas
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MainRdStat

variable {d : ℕ}

theorem sa2_two_le_mStar : 2 ≤ mStar d := by unfold mStar; omega

theorem sa2_family {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) {Kad T : ℝ} {C : WholeCoeff d}
    (hA : AdjointInputRd (ulocClass (mStar d) χ) (ulocClass (mStar d) χ) 2 C T Kad) {q : ℕ}
    (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T) (φ : Fin q → Euc d → ℝ)
    (hφ : ∀ a, (ulocClass (mStar d) χ).mem (φ a)) :
    (∀ a, IsClassicalAdjointW C (ts a) (φ a) (fun r => propagatorW C r (ts a) (φ a))) ∧
    (∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a), MemCb 2 (propagatorW C rr (ts a) (φ a)) ∧
      cbNorm 2 (propagatorW C rr (ts a) (φ a)) ≤ max Kad 0 * (ulocNormE (mStar d) χ (φ a)).toReal) ∧
    (∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a), ulocNormE (mStar d) χ (propagatorW C rr (ts a) (φ a)) ≤
      ENNReal.ofReal (max Kad 0 * (ulocNormE (mStar d) χ (φ a)).toReal)) := by
  have h := fun a => sa2_orbit hχ hA (hts a) (hφ a)
  exact ⟨fun a => (h a).cl, fun a rr hr => (h a).cb rr hr, fun a rr hr => (h a).ul rr hr⟩

theorem sa2_norm_nonneg_B {Kad : ℝ} {q : ℕ} {χ : Euc d → ℝ} (φ : Fin q → Euc d → ℝ) (a : Fin q) :
    0 ≤ max Kad 0 * (ulocNormE (mStar d) χ (φ a)).toReal :=
  mul_nonneg (le_max_right _ _) ENNReal.toReal_nonneg

end HRS.MS.MainRdStat
