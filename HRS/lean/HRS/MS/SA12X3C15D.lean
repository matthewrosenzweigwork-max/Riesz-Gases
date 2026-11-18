import HRS.MS.SA12X3C15C
import HRS.MS.SA12X3C6A

/-!
# S.A.12 C15 (SA12X3), part D: periodic jets are bounded uniformly in space and in time on `[0,t]`
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

variable {d : ℕ}

theorem sa12x3_per_jet_bound {L : ℝ} (hL : 0 < L) {t : ℝ} {F : ℝ → Euc d → ℝ} {j : ℕ} (idx : Fin j → Fin d)
    (hcont : ContinuousOn (fun p : ℝ × Euc d => partialDeriv idx (F p.1) p.2) (Icc (0 : ℝ) t ×ˢ univ))
    (hper : ∀ τ ∈ Icc (0 : ℝ) t, ∀ (x : Euc d) (k : Fin d → ℤ), F τ (x + L • latticePt k) = F τ x) :
    ∃ B : ℝ, ∀ τ ∈ Icc (0 : ℝ) t, ∀ x : Euc d, |partialDeriv idx (F τ) x| ≤ B := by
  set Q : Set (Euc d) := (WithLp.toLp 2) '' (Set.pi univ fun _ : Fin d => Icc (0 : ℝ) L) with hQ
  have hQc : IsCompact Q := (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
  have hK : IsCompact (Icc (0 : ℝ) t ×ˢ Q) := isCompact_Icc.prod hQc
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hcont.mono (prod_mono subset_rfl (subset_univ _)))
  refine ⟨B, fun τ hτ x => ?_⟩
  set k : Fin d → ℤ := fun i => ⌊x i / L⌋ with hk
  set y : Euc d := x - L • latticePt k with hy
  have hyi : ∀ i, y i = x i - L * (k i : ℝ) := fun i => by simp [hy, latticePt]
  have hyQ : y ∈ Q := by
    refine ⟨fun i => y i, fun i _ => ?_, rfl⟩
    have h1 : (⌊x i / L⌋ : ℝ) ≤ x i / L := Int.floor_le _
    have h2 : x i / L < (⌊x i / L⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    have h3 : L * (⌊x i / L⌋ : ℝ) ≤ x i := by
      have := mul_le_mul_of_nonneg_left h1 hL.le
      rwa [mul_div_cancel₀ _ hL.ne'] at this
    have h4 : x i < L * (⌊x i / L⌋ : ℝ) + L := by
      have := mul_lt_mul_of_pos_left h2 hL
      rw [mul_div_cancel₀ _ hL.ne'] at this
      linarith
    refine ⟨?_, ?_⟩
    · show 0 ≤ y i; rw [hyi]; simp only [hk]; linarith
    · show y i ≤ L; rw [hyi]; simp only [hk]; linarith
  have hx : x = y + L • latticePt k := by rw [hy]; abel
  have hpd : partialDeriv idx (F τ) x = partialDeriv idx (F τ) y := by
    rw [hx, ← sa12x3_pd_shift]
    congr 1
    funext z
    exact hper τ hτ z k
  rw [hpd]
  have := hB (τ, y) ⟨hτ, hyQ⟩
  simpa [Real.norm_eq_abs] using this

end HRS.MH.AdjointRd.Phase2SA12Construction
