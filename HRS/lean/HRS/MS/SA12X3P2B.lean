import HRS.MS.SA12X3P2A

/-!
# S.A.12 P2 (SA12X3), part B: the time increment of the pairings of a weak solution (generic operator)
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Assembly

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12Limit

variable {d : ℕ}

theorem sa12x3p_time_pair (hd : 1 ≤ d) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ)
    {A : ℝ → (Euc d → ℝ) → (Euc d → ℝ)} {t : ℝ} {φ0 : Euc d → ℝ} {G : ℝ → Euc d → ℝ}
    (hG : IsWeakSol A t φ0 G) {B' : ℝ} (hB0 : 0 ≤ B')
    (hB : ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE 0 χ (G τ) ≤ ENNReal.ofReal B') {ψ : Euc d → ℝ}
    (hψ : IsCcInfty ψ) {c : ℝ} (hc0 : 0 ≤ c)
    (hmeas : ∀ σ ∈ Icc (0 : ℝ) t, AEStronglyMeasurable (A σ ψ) volume)
    (hcell : ∀ σ ∈ Icc (0 : ℝ) t, cellL2Sum (A σ ψ) ≤ ENNReal.ofReal c) {τ σ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) t) (hσ : σ ∈ Icc (0 : ℝ) t) :
    |(∫ x, G τ x * ψ x) - ∫ x, G σ x * ψ x| ≤ B' * c * |τ - σ| := by
  have hbd : ∀ r ∈ Icc (0 : ℝ) t, ‖∫ x, G r x * A r ψ x‖ ≤ B' * c := by
    intro r hr
    rw [Real.norm_eq_abs]
    have h := (cell_pair_bound hd χ hχ B' hB0 (G r) (A r ψ) (hB r hr) (hmeas r hr)
      ((hcell r hr).trans_lt ENNReal.ofReal_lt_top)).2
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hB0)
    exact ENNReal.toReal_le_of_le_ofReal hc0 (hcell r hr)
  have hint := hG.integrable_σ ψ hψ
  set f : ℝ → ℝ := fun r => ∫ x, G r x * A r ψ x with hf
  have hII : ∀ a ∈ Icc (0 : ℝ) t, IntervalIntegrable f volume 0 a := fun a ha =>
    (intervalIntegrable_iff_integrableOn_Icc_of_le ha.1).2
      (hint.mono_set (Icc_subset_Icc_right ha.2))
  have hconv : ∀ a ∈ Icc (0 : ℝ) t, ∫ r in Icc (0 : ℝ) a, f r = ∫ r in (0 : ℝ)..a, f r := fun a ha => by
    rw [intervalIntegral.integral_of_le ha.1, integral_Icc_eq_integral_Ioc]
  have e : (∫ x, G τ x * ψ x) - ∫ x, G σ x * ψ x = ∫ r in σ..τ, f r := by
    rw [hG.eq ψ hψ τ hτ, hG.eq ψ hψ σ hσ, hconv τ hτ, hconv σ hσ,
      add_sub_add_left_eq_sub, intervalIntegral.integral_interval_sub_left (hII τ hτ) (hII σ hσ)]
  rw [e, ← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const fun r hr => hbd r ?_).trans (le_of_eq ?_)
  · have := Set.uIoc_subset_uIcc hr
    exact (Set.uIcc_subset_Icc hσ hτ) this
  · ring

end HRS.MH.AdjointRd.Phase2SA12Assembly
