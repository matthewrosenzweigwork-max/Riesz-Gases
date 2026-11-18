import HRS.MS.SA12X3C15B

/-!
# S.A.12 C15 (SA12X3), part C: the cell rate is integrable in time

A function that is differentiable (within `[0,t]`) at every point with a bounded derivative has a measurable derivative
(`stronglyMeasurable_derivWithin_Ici`), and the derivative is bounded by `sa12x3_rate_term_bound`; so `cellRate` is integrable on `[0,t]`.
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

variable {d : ℕ}

theorem sa12x3_deriv_aesm {t : ℝ} {f g : ℝ → ℝ}
    (hderiv : ∀ τ ∈ Icc (0 : ℝ) t, HasDerivWithinAt f (g τ) (Icc (0 : ℝ) t) τ) :
    AEStronglyMeasurable g (volume.restrict (Icc (0 : ℝ) t)) := by
  refine (stronglyMeasurable_derivWithin_Ici f).aestronglyMeasurable.congr ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 ?_
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton t : volume ({t} : Set ℝ) = 0)] with x hxt hx
  have hlt : x < t := lt_of_le_of_ne hx.2 hxt
  have h1 : HasDerivWithinAt f (g x) (Icc x t) x := (hderiv x hx).mono (Icc_subset_Icc_left hx.1)
  have h2 : HasDerivWithinAt f (g x) (Ici x) x := by
    rw [← hasDerivWithinAt_inter' (Icc_mem_nhdsGE hlt)]
    rwa [Set.inter_eq_right.2 Icc_subset_Ici_self]
  exact h2.derivWithin (uniqueDiffWithinAt_Ici x)

theorem sa12x3_cellRate_integrable (hd : 1 ≤ d) (m : ℕ) (Cb T : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh)
    (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d) (hb : IsAdvectingDrift m Cb T b)
    (hΨ : IsNegDriftFlow T b Ψ) (ν : ℝ) (G : ℝ → Euc d → ℝ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (F : ℝ → Euc d → ℝ) (hF : IsClassicalSol m ν b G t F) (c : Euc d) :
    IntegrableOn (fun τ => cellRate m χ Ψ τ c ν (b τ) (F τ) (G τ)) (Icc (0 : ℝ) t) := by
  have hderiv : ∀ τ ∈ Icc (0 : ℝ) t, HasDerivWithinAt (fun τ' => cellEnergy m χ Ψ τ' c (F τ'))
      (cellRate m χ Ψ τ c ν (b τ) (F τ) (G τ)) (Icc (0 : ℝ) t) τ :=
    fun τ hτ => cell_energy_derivative hd m Cb T χ χh hχ b Ψ hb hΨ ν G t ht F hF c τ hτ
  have hmeas := sa12x3_deriv_aesm hderiv
  -- the bound of each term
  have hA : ∀ (j : ℕ) (idx : Fin j → Fin d), ∃ A : ℝ, j ≤ m → ∀ σ ∈ Icc (0 : ℝ) t,
      |∫ x, (2 * advCutoff χ Ψ σ c x ^ 2 * (partialDeriv idx (F σ) x *
          partialDeriv idx (fun y => ν * Laplacian.laplacian (F σ) y +
            inner ℝ (b σ y) (gradient (F σ) y) + G σ y) x) +
        2 * advCutoff χ Ψ σ c x * inner ℝ (b σ x) (gradient (advCutoff χ Ψ σ c) x) *
          partialDeriv idx (F σ) x ^ 2)| ≤ A := by
    intro j idx
    by_cases hj : j ≤ m
    · obtain ⟨K, R0, hK0, hR0, hsupp, hbd⟩ :=
        sa12x3_rate_term_bound hd m Cb T χ χh hχ b Ψ hb hΨ ν G t ht F hF c j hj idx
      refine ⟨K * (volume (Metric.closedBall (0 : Euc d) R0)).toReal, fun _ σ hσ => ?_⟩
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Metric.closedBall (0 : Euc d) R0)
        (fun x hx => hsupp σ hσ x (by simpa [mem_closedBall_zero_iff, not_le] using hx))]
      have := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure (Euc d)))
        (s := Metric.closedBall (0 : Euc d) R0) (C := K) measure_closedBall_lt_top
        (f := fun x => (2 * advCutoff χ Ψ σ c x ^ 2 * (partialDeriv idx (F σ) x *
          partialDeriv idx (fun y => ν * Laplacian.laplacian (F σ) y +
            inner ℝ (b σ y) (gradient (F σ) y) + G σ y) x) +
        2 * advCutoff χ Ψ σ c x * inner ℝ (b σ x) (gradient (advCutoff χ Ψ σ c) x) *
          partialDeriv idx (F σ) x ^ 2)) (fun x _ => by rw [Real.norm_eq_abs]; exact hbd σ hσ x)
      simpa only [Real.norm_eq_abs, Measure.real] using this
    · exact ⟨0, fun h => absurd h hj⟩
  choose A hAb using hA
  set Kg : ℝ := ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d, |A j idx| with hKg
  haveI : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) t)) := ⟨by simp⟩
  refine Integrable.of_bound (C := Kg) hmeas ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun τ hτ => ?_)
  rw [Real.norm_eq_abs]
  unfold cellRate
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [hKg]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun idx _ => ?_)
  exact (hAb j idx hjm τ hτ).trans (le_abs_self _)

end HRS.MH.AdjointRd.Phase2SA12Construction
