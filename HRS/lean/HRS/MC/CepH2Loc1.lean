import HRS.MC.CepH2Freeze2
import HRS.MC.CepE3
import HRS.Stochastic.SDE

/-!
# CEPH2, G3 (a): pathwise uniqueness for the localised drifts
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

/-- Deterministic uniqueness: two solutions of integral equations with the same noise path whose drifts agree
along one of them, one drift being Lipschitz, coincide. -/
theorem h2_path_eq {B B' : Ch N → Ch N} (hB : Continuous B) {L : ℝ≥0} (hB' : LipschitzWith L B')
    {z₀ : Ch N} {w Y Y' : ℝ → Ch N} (hY : Continuous Y) (hY' : Continuous Y')
    (hYe : ∀ s : ℝ, 0 ≤ s → Y s = z₀ + (∫ r in (0 : ℝ)..s, B (Y r)) + w s)
    (hYe' : ∀ s : ℝ, 0 ≤ s → Y' s = z₀ + (∫ r in (0 : ℝ)..s, B' (Y' r)) + w s) {t : ℝ} (ht : 0 ≤ t)
    (hagree : ∀ r ∈ Icc (0 : ℝ) t, B (Y r) = B' (Y r)) : ∀ s ∈ Icc (0 : ℝ) t, Y' s = Y s := by
  have hint : ∀ (G : Ch N → Ch N) (X : ℝ → Ch N), Continuous G → Continuous X →
      ∀ a b : ℝ, IntervalIntegrable (fun r => G (X r)) volume a b :=
    fun G X hG hX a b => (hG.comp hX).intervalIntegrable a b
  have hBc' : Continuous B' := hB'.continuous
  have hd : ∀ s ∈ Icc (0 : ℝ) t, ∃ f : ℝ → Ch N, (Y' s - Y s) = ∫ r in (0 : ℝ)..s, f r ∧
      ∀ r ∈ Icc (0 : ℝ) s, ‖f r‖ ≤ (L : ℝ) * ‖Y' r - Y r‖ := by
    intro s hs
    refine ⟨fun r => B' (Y' r) - B' (Y r), ?_, fun r hr => ?_⟩
    · rw [hYe' s hs.1, hYe s hs.1]
      have e : (∫ r in (0 : ℝ)..s, B (Y r)) = ∫ r in (0 : ℝ)..s, B' (Y r) := by
        refine intervalIntegral.integral_congr fun r hr => ?_
        rw [uIcc_of_le hs.1] at hr
        exact hagree r ⟨hr.1, hr.2.trans hs.2⟩
      rw [e, intervalIntegral.integral_sub (hint B' Y' hBc' hY' 0 s) (hint B' Y hBc' hY 0 s)]
      abel
    · have := hB'.dist_le_mul (Y' r) (Y r)
      simpa [dist_eq_norm] using this
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn
    (hY'.sub hY).continuousOn
  have := eq_zero_of_integral_bound (d := fun s => Y' s - Y s) (T := t) (L := (L : ℝ)) (M := M) L.2
    (fun s hs => hM s hs) hd
  intro s hs
  have h0 := this s hs
  exact sub_eq_zero.1 h0

end HRS.MC.CepH2
