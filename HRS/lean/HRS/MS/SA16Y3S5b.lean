import HRS.MS.SA16Y3L2
import HRS.MS.SA16SNl3

/-!
# S.A.16 (SA16Y3) S5b: convergence of zeroth-component pairings with uniformly convergent test functions

`sa16y3_pair_tendsto`: if `g_j ∈ WmpSpace d m p` are bounded by `Bm` and converge weakly to `G`, and the continuous test
functions `N_j` (supported in `closedBall 0 R0`) converge uniformly to the continuous `N` (supported in the same ball), then
`∫ wrep g_j · N_j → ∫ wrep G · N`.  This is the pointwise-in-time convergence of the transport pairing
`ℓ_{div(b_n ψ)}(g_n σ)` of the weak identity (`b_n → b` locally uniformly with first derivatives, `supp ψ ⊂ B_{R0}`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section S5b
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y3_memLp_ball {N : Euc d → ℝ} (hN : Continuous N) {R0 : ℝ} (h0 : ∀ x, R0 < ‖x‖ → N x = 0) :
    MemLp N (ENNReal.conjExponent (ENNReal.ofReal p)) volume := by
  refine hN.memLp_of_hasCompactSupport ?_
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Euc d) R0) ?_
  intro x hx
  by_contra hxc
  exact hx (h0 x (by simpa [not_le] using hxc))

theorem sa16y3_pair_tendsto {m : ℕ} {Bm R0 : ℝ} (gs : ℕ → WmpSpace d m p) (G : WmpSpace d m p)
    (hbd : ∀ j, ‖gs j‖ ≤ Bm)
    (hw : ∀ ℓ : StrongDual ℝ (WmpSpace d m p), Tendsto (fun j => ℓ (gs j)) atTop (𝓝 (ℓ G)))
    (Nn : ℕ → Euc d → ℝ) (N : Euc d → ℝ) (hNc : ∀ j, Continuous (Nn j)) (hNc' : Continuous N)
    (hN0 : ∀ j x, R0 < ‖x‖ → Nn j x = 0) (hN0' : ∀ x, R0 < ‖x‖ → N x = 0)
    (huni : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ x, |Nn j x - N x| ≤ ε) :
    Tendsto (fun j => ∫ x, wrep d m p (gs j) x * Nn j x) atTop (𝓝 (∫ x, wrep d m p G x * N x)) := by
  have hBm : 0 ≤ Bm := (norm_nonneg _).trans (hbd 0)
  set V : ℝ := (volume (closedBall (0 : Euc d) R0)).toReal ^ (1 / Real.conjExponent p) with hV
  have hV0 : 0 ≤ V := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hmemN := sa16y3_memLp_ball (p := p) hNc' hN0'
  have hmemj : ∀ j, MemLp (Nn j) (ENNReal.conjExponent (ENNReal.ofReal p)) volume :=
    fun j => sa16y3_memLp_ball (p := p) (hNc j) (hN0 j)
  have hwj : ∀ j, MemLp (fun x => wrep d m p (gs j) x) (ENNReal.ofReal p) volume := fun j => sa16y3_wrep_memLp _
  have hpq : (ENNReal.ofReal p).HolderConjugate (ENNReal.conjExponent (ENNReal.ofReal p)) :=
    ENNReal.HolderConjugate.conjExponent (by
      have hp2 : (2 : ℝ) ≤ p := Fact.out
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith))
  -- the weak convergence of the fixed functional
  have h1 : Tendsto (fun j => ∫ x, wrep d m p (gs j) x * N x) atTop (𝓝 (∫ x, wrep d m p G x * N x)) := by
    simp_rw [← sa16so_ellN_apply m hmemN]
    exact hw _
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε' : 0 < ε / 2 / (Bm * V + 1) := by positivity
  obtain ⟨j1, hj1⟩ := Metric.tendsto_atTop.1 h1 (ε / 2) (by linarith)
  obtain ⟨j2, hj2⟩ := eventually_atTop.1 (huni _ hε')
  refine ⟨max j1 j2, fun j hj => ?_⟩
  have hjd : |(∫ x, wrep d m p (gs j) x * Nn j x) - ∫ x, wrep d m p (gs j) x * N x| ≤ ε / 2 := by
    have hsub : (∫ x, wrep d m p (gs j) x * Nn j x) - ∫ x, wrep d m p (gs j) x * N x =
        ∫ x, wrep d m p (gs j) x * (Nn j x - N x) := by
      have hi1 : Integrable (fun x => wrep d m p (gs j) x * Nn j x) := (hwj j).integrable_mul (hmemj j)
      have hi2 : Integrable (fun x => wrep d m p (gs j) x * N x) := (hwj j).integrable_mul hmemN
      rw [← integral_sub hi1 hi2]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      ring
    rw [hsub]
    have hb := sa16y3_ell_sup_bound (p := p) (gs j) (N := fun x => Nn j x - N x)
      ((hNc j).sub hNc').aestronglyMeasurable (R := R0) (c := ε / 2 / (Bm * V + 1)) hε'.le (fun x => by
        by_cases hx : x ∈ closedBall (0 : Euc d) R0
        · rw [Set.indicator_of_mem hx, mul_one]
          exact hj2 j (le_trans (le_max_right _ _) hj) x
        · rw [Set.indicator_of_notMem hx, mul_zero]
          have hxn : R0 < ‖x‖ := by simpa using hx
          simp [hN0 j x hxn, hN0' x hxn])
    refine hb.trans ?_
    rw [← hV]
    calc ε / 2 / (Bm * V + 1) * V * ‖gs j‖ ≤ ε / 2 / (Bm * V + 1) * V * Bm :=
          mul_le_mul_of_nonneg_left (hbd j) (by positivity)
      _ = ε / 2 * (Bm * V / (Bm * V + 1)) := by ring
      _ ≤ ε / 2 * 1 := mul_le_mul_of_nonneg_left (by rw [div_le_one (by positivity)]; linarith) (by linarith)
      _ = ε / 2 := by ring
  have hj1' := hj1 j (le_trans (le_max_left _ _) hj)
  rw [Real.dist_eq] at hj1' ⊢
  show |(∫ x, wrep d m p (gs j) x * Nn j x) - ∫ x, wrep d m p G x * N x| < ε
  calc |(∫ x, wrep d m p (gs j) x * Nn j x) - ∫ x, wrep d m p G x * N x|
      = |((∫ x, wrep d m p (gs j) x * Nn j x) - ∫ x, wrep d m p (gs j) x * N x) +
          ((∫ x, wrep d m p (gs j) x * N x) - ∫ x, wrep d m p G x * N x)| := by ring_nf
    _ ≤ |(∫ x, wrep d m p (gs j) x * Nn j x) - ∫ x, wrep d m p (gs j) x * N x| +
          |(∫ x, wrep d m p (gs j) x * N x) - ∫ x, wrep d m p G x * N x| := abs_add_le _ _
    _ < ε := by linarith

end S5b

end HRS.Whole.AppendixA.Phase2SA16R
