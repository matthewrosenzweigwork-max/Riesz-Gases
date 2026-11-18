import HRS.MS.SA12X3C15H

/-!
# S.A.12 C15 (SA12X3), part I: uniform bounds of the cell energy and the cell dissipation of a periodic classical solution
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

theorem sa12x3_uniform_jets {L : ℝ} (hL : 0 < L) {t : ℝ} {F : ℝ → Euc d → ℝ} (m : ℕ)
    (hcont : ∀ (j : ℕ) (idx : Fin j → Fin d),
      ContinuousOn (fun p : ℝ × Euc d => partialDeriv idx (F p.1) p.2) (Icc (0 : ℝ) t ×ˢ univ))
    (hper : ∀ τ ∈ Icc (0 : ℝ) t, ∀ (x : Euc d) (k : Fin d → ℤ), F τ (x + L • latticePt k) = F τ x) :
    ∃ B : ℝ, ∀ τ ∈ Icc (0 : ℝ) t, ∀ j ≤ m + 1, ∀ idx : Fin j → Fin d, ∀ x, |partialDeriv idx (F τ) x| ≤ B := by
  have h : ∀ (j : ℕ) (idx : Fin j → Fin d), ∃ Bj : ℝ, ∀ τ ∈ Icc (0 : ℝ) t, ∀ x, |partialDeriv idx (F τ) x| ≤ Bj :=
    fun j idx => sa12x3_per_jet_bound hL idx (hcont j idx) hper
  choose Bj hBj using h
  refine ⟨∑ j ∈ Finset.range (m + 2), ∑ idx : Fin j → Fin d, |Bj j idx|, fun τ hτ j hj idx x => ?_⟩
  refine (hBj j idx τ hτ x).trans ((le_abs_self _).trans ?_)
  refine le_trans (Finset.single_le_sum (f := fun idx : Fin j → Fin d => |Bj j idx|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ idx)) ?_
  exact Finset.single_le_sum (f := fun j => ∑ idx : Fin j → Fin d, |Bj j idx|)
    (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_range.2 (by omega))

theorem sa12x3_cell_uniform (hd : 1 ≤ d) (m : ℕ) (Cb T : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh)
    {B : ℝ} (t : ℝ) (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d) (hb : IsAdvectingDrift m Cb T b)
    (hΨ : IsNegDriftFlow T b Ψ) (ht : t ∈ Icc (0 : ℝ) T) (F : ℝ → Euc d → ℝ)
    (hB : ∀ τ ∈ Icc (0 : ℝ) t, ∀ j ≤ m + 1, ∀ idx : Fin j → Fin d, ∀ x, |partialDeriv idx (F τ) x| ≤ B) :
    ∃ Be : ℝ, ∀ τ ∈ Icc (0 : ℝ) t, ∀ c : Euc d,
      cellEnergy m χ Ψ τ c (F τ) ≤ Be ∧ cellDissip m χ Ψ τ c (F τ) ≤ Be := by
  obtain ⟨B1, R, -, -, hf⟩ := advected_cutoff_jets d hd m Cb T χ χh hχ
  set V : ℝ := (volume (closedBall (0 : Euc d) R)).toReal with hV
  set S0 : ℝ := ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * (d : ℝ) ^ j with hS0
  set S1 : ℝ := ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * (d : ℝ) ^ (j + 1) with hS1
  refine ⟨max (S0 * (B ^ 2 * V)) (S1 * (B ^ 2 * V)), fun τ hτ c => ?_⟩
  have hτT : τ ∈ Icc (0 : ℝ) T := ⟨hτ.1, hτ.2.trans ht.2⟩
  have hw : ∀ x, |advCutoff χ Ψ τ c x| ≤ 1 := by
    intro x
    have := hχ.1.2.2.2.1 (Function.invFun (Ψ τ) x - c)
    show |χ (Function.invFun (Ψ τ) x - c)| ≤ 1
    rw [abs_of_nonneg this.1]; exact this.2
  have hs : Function.support (advCutoff χ Ψ τ c) ⊆ closedBall (Ψ τ c) R :=
    (sa12z3_adv_support_le hχ Ψ τ c).trans (hf b Ψ hb hΨ τ hτT c).2.2
  have hvol : (volume (closedBall (Ψ τ c) R)).toReal = V := by
    rw [hV, Measure.addHaar_closedBall_center]
  have h1 := sa12x3_jetSq_le m hw hs (fun j hj idx x => hB τ hτ j (by omega) idx x)
  have h2 := sa12x3_dissipSq_le m hw hs (fun j hj idx x => hB τ hτ j hj idx x)
  rw [hvol] at h1 h2
  exact ⟨h1.trans (le_max_left _ _), h2.trans (le_max_right _ _)⟩

end HRS.MH.AdjointRd.Phase2SA12Construction
