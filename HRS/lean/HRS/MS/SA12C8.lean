import HRS.MS.SA12C7
import HRS.MS.SA12CellC8B

/-!
# S.A.12(c), packet E7.06 (part 6): the time derivative of one box jet energy

For a classical solution `F` on `[0,t]` (`IsClassicalSol`) with an advecting drift:
`d/dτ ∫_{Q_L} (∂^α F τ)² = ∫_{Q_L} 2 ∂^αF τ ∂^α(νΔF + b·∇F + G)` within `[0,t]`.
(`Q_L` is bounded, so differentiation under the integral sign is the compact-support lemma `sa12y_param_deriv`
applied to the indicator of the box.)
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12Near HRS.MS.UniqT3
open HRS.MH.AdjointRd.Phase2SA12

variable {d : ℕ}

theorem sa12c_box_bounded (L : ℝ) : ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ periodBox d L, ‖x‖ ≤ R := by
  have hK := HRS.MS.ToriCoefB.tcb_compact_Icc (d := d) 0 L
  have hsub : periodBox d L ⊆ {x : Euc d | ∀ i, x i ∈ Icc (0 : ℝ) L} := by
    intro x hx i
    exact ⟨(hx i).1, (hx i).2.le⟩
  obtain ⟨R, hR⟩ := (hK.isBounded.subset hsub).exists_norm_le
  exact ⟨max R 0, le_max_right _ _, fun x hx => (hR x hx).trans (le_max_left _ _)⟩

theorem sa12c_energy_term_deriv {m : ℕ} {Cb T t ν : ℝ} {b : ℝ → Euc d → Euc d}
    (hb : IsAdvectingDrift m Cb T b) {G F : ℝ → Euc d → ℝ} (hF : IsClassicalSol m ν b G t F)
    (htT : t ≤ T) (L : ℝ) {j : ℕ} (hj : j ≤ m) (idx : Fin j → Fin d) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) t) :
    HasDerivWithinAt (fun τ' => ∫ x in periodBox d L, (partialDeriv idx (F τ') x) ^ 2)
      (∫ x in periodBox d L, 2 * (partialDeriv idx (F τ) x * partialDeriv idx
        (fun y => ν * Laplacian.laplacian (F τ) y + inner ℝ (b τ y) (gradient (F τ) y) + G τ y) x))
      (Icc (0 : ℝ) t) τ := by
  have hQm := sa12c20_box_meas (d := d) L
  obtain ⟨R, hR0, hR⟩ := sa12c_box_bounded (d := d) L
  obtain ⟨KF, hKF⟩ := sa12y_jet_bound hF.contF j R
  obtain ⟨KD, hKD⟩ := sa12y_rate_bound hb hF htT R hR0 j hj
  set KF' : ℝ := |KF| with hKF'
  set KD' : ℝ := |KD| with hKD'
  have hKF0 : 0 ≤ KF' := abs_nonneg _
  have hKD0 : 0 ≤ KD' := abs_nonneg _
  set K : ℝ := KF' ^ 2 + 2 * (KF' * KD') with hK
  have hK0 : 0 ≤ K := by positivity
  have hpF : ∀ σ ∈ Icc (0 : ℝ) t, ∀ x : Euc d, ‖x‖ ≤ R → |partialDeriv idx (F σ) x| ≤ KF' := by
    intro σ hσ x hx
    exact (HRS.MP.RdInit.mri_abs_partialDeriv_le idx _ x).trans ((hKF σ hσ x hx).trans (le_abs_self _))
  have hpD : ∀ σ ∈ Icc (0 : ℝ) t, ∀ x : Euc d, ‖x‖ ≤ R →
      |partialDeriv idx (fun y => ν * Laplacian.laplacian (F σ) y +
        inner ℝ (b σ y) (gradient (F σ) y) + G σ y) x| ≤ KD' :=
    fun σ hσ x hx => (hKD idx σ hσ x hx).trans (le_abs_self _)
  have h := sa12y_param_deriv (K := K) (R := R) (t := t)
    (f := fun σ x => (periodBox d L).indicator (fun x => (partialDeriv idx (F σ) x) ^ 2) x)
    (f' := fun σ x => (periodBox d L).indicator (fun x => 2 * (partialDeriv idx (F σ) x * partialDeriv idx
        (fun y => ν * Laplacian.laplacian (F σ) y + inner ℝ (b σ y) (gradient (F σ) y) + G σ y) x)) x)
    ?_ ?_ ?_ ?_ ?_ hτ
  · simp only [integral_indicator hQm] at h
    exact h
  · intro σ hσ
    exact ((sa12c_pd_cont (hF.smooth σ hσ).1 idx).pow 2).aestronglyMeasurable.indicator hQm
  · intro σ hσ x hx
    have : x ∉ periodBox d L := fun hxQ => absurd (hR x hxQ) (not_le.2 hx)
    exact Set.indicator_of_notMem this _
  · intro σ hσ x
    by_cases hxQ : x ∈ periodBox d L
    · rw [Set.indicator_of_mem hxQ, abs_pow]
      have := hpF σ hσ x (hR x hxQ)
      calc |partialDeriv idx (F σ) x| ^ 2 ≤ KF' ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
        _ ≤ K := by rw [hK]; nlinarith [mul_nonneg hKF0 hKD0]
    · rw [Set.indicator_of_notMem hxQ, abs_zero]; exact hK0
  · intro x σ hσ
    by_cases hxQ : x ∈ periodBox d L
    · simp only [Set.indicator_of_mem hxQ]
      have hw := hF.deriv_t j hj idx x σ hσ
      refine (hw.pow 2).congr_deriv ?_
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      ring
    · simp only [Set.indicator_of_notMem hxQ]
      exact hasDerivWithinAt_const _ _ _
  · intro σ hσ x hx
    by_cases hxQ : x ∈ periodBox d L
    · rw [Set.indicator_of_mem hxQ, abs_mul, abs_two, abs_mul]
      have h1 := hpF σ hσ x hx
      have h2 := hpD σ hσ x hx
      calc 2 * (|partialDeriv idx (F σ) x| * |partialDeriv idx
            (fun y => ν * Laplacian.laplacian (F σ) y + inner ℝ (b σ y) (gradient (F σ) y) + G σ y) x|)
          ≤ 2 * (KF' * KD') := by gcongr
        _ ≤ K := by rw [hK]; nlinarith [sq_nonneg KF']
    · rw [Set.indicator_of_notMem hxQ, abs_zero]; exact hK0

end HRS.MH.AdjointRd.Phase2SA12C
