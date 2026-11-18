import HRS.MS.S82RN12
import HRS.MS.S82RA2
import HRS.MS.S82P2Mar1
import HRS.MS.S82P2Local
import HRS.MS.QsfCorr2
import HRS.Equilibrium.MarginalDensity

/-!
# S8.2 R02 (S82R), N13: helper facts for the `PinComparison` assembly
`delta_N -> 0`, crude one-coordinate density bounds, and `refMarginal` as the cavity marginal.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82R
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

lemma s82r_delta_tendsto (hd : 2 ≤ d) :
    Tendsto (fun N : ℕ => HRS.MS.Phase2S82.deltaN N) atTop (𝓝 0) := by
  have h := HRS.MarginalAux.tendsto_deltaN (d := d) (s := criticalS d) (s82r_criticalS_pos (by omega)).le
    (s82r_criticalS_lt (by omega)) (by omega)
  simpa [s82r_deltaN_eq] using h

lemma s82r_eventually_C0_delta (hd : 2 ≤ d) (C0 : ℝ) :
    ∃ N1 : ℕ, 2 ≤ N1 ∧ ∀ N, N1 ≤ N → C0 * HRS.MS.Phase2S82.deltaN N ≤ 1 / 4 := by
  have h := (s82r_delta_tendsto hd).eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (4 * (|C0| + 1)) by positivity))
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 h
  refine ⟨max N1 2, le_max_right _ _, fun N hN => ?_⟩
  have hN' : N1 ≤ N := (le_max_left _ _).trans hN
  have h1 := hN1 N hN'
  have hδ0 : 0 ≤ HRS.MS.Phase2S82.deltaN N := s82r_deltaN_nonneg (by have := le_max_right N1 2; omega)
  have hC : 0 < |C0| + 1 := by positivity
  calc C0 * HRS.MS.Phase2S82.deltaN N ≤ |C0| * HRS.MS.Phase2S82.deltaN N :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hδ0
    _ ≤ (|C0| + 1) * (1 / (4 * (|C0| + 1))) := by
        refine mul_le_mul (by linarith) h1.le hδ0 hC.le
    _ = 1 / 4 := by field_simp

open HRS.External in
/-- Crude density bound for any one-coordinate marginal of a pinned ensemble. -/
lemma s82r_marg_density_le {μ : Measure (Euc d)} [IsProbabilityMeasure μ] (V : WeakPotential μ)
    {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN0 : 0 < N) {B : Type*} [Fintype B] (pins : B → Euc d) {n : ℕ}
    (hn : n + Fintype.card B ≤ N) (i : Fin n) :
    ∀ᵐ z ∂μ, (((pinnedLaw V (β / N) n pins).map (fun y => y i)).rnDeriv μ z).toReal ≤
      Real.exp (V.M + V.M' + β * V.γ) := by
  have hlam : 0 ≤ β / (N : ℝ) := div_nonneg hβ (Nat.cast_nonneg N)
  haveI := isProb_pinnedLaw V hlam n pins
  exact s82r_rn_le (Real.exp_pos _).le (RefMarg.marginal_le_smul V hβ hN0 hn pins i)

open HRS.External in
/-- `refMarginal` is the cavity marginal of the pinned-weak-ensemble presentation. -/
lemma s82r_refMarg_eq {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {q : Euc d → ℝ}
    {h : ℕ → Euc d → ℝ} {β : ℝ} {N : ℕ} (hN0 : 0 < N) (V : WeakPotential μ)
    (hVφ : V.φ = s82r_phi q h μ β N) (hVq : ∀ x y, V.q x y = q (x - y)) (hβ : 0 ≤ β) :
    haveI : NeZero N := ⟨hN0.ne'⟩
    refMarginal q h μ β N = RefMarg.cavMarg V (β / N) N := by
  haveI : NeZero N := ⟨hN0.ne'⟩
  unfold refMarginal
  rw [dif_pos hN0]
  unfold unpinnedReference
  rw [s82r_referenceLaw_eq_pot V hVφ hVq hβ, s82r_pinnedLaw_zero V]
  unfold RefMarg.cavMarg
  rw [RefMarg.pinnedLaw_empty V (β / N) N (fun e : Empty => e.elim)]
  rfl

end HRS.MS.S82R

end
