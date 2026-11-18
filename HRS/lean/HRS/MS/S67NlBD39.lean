import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD01
import HRS.MS.S67NlBD06
import HRS.MS.S67NlBD38

/-!
# S6.7nl.39: finite `Σ²`-to-`Σ^M` iteration before absorption
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.
Induction on `n` for the level `min(M, 2 + nδ)`: the base is the `Σ²` certificate of packet 06, each
step is one application of packet 38, and a natural `N` with `2 + Nδ ≥ M` reaches level `M`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

set_option maxHeartbeats 1600000 in
theorem s67bd_bootstrap_finite (H : Mov2dTh d s β q ρ₀)
    (M m : ℕ) (hM : 2 ≤ M) (hm : (d : ℝ) / 2 + 7 < m) (hmM : (M : ℝ) + 4 < m)
    (R0 c0 : ℝ) (hR0 : 0 ≤ R0) (hc0 : 0 ≤ c0)
    (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ)
    (hρ : MovInSmallClass d s q β ρ₀ m R0 c0 f0 ρ)
    (T : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ) (hT : 0 ≤ T)
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff ρ) T φ f)
    (hφ : MemOsc (M : ℝ) (s67psi ρ₀ φ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r ∈ Icc (0 : ℝ) T,
      MemOsc (M : ℝ) (s67psi ρ₀ (f r)) ∧ oscNorm (M : ℝ) (s67psi ρ₀ (f r)) ≤ B := by
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have ha2 : movA d s < 2 := by
    unfold movA; exact max_lt (by norm_num) (by linarith [H.hsd])
  have hδ0 : 0 < s67bd_delta d s := by
    show 0 < (2 - movA d s) / 2; linarith
  have key : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ r ∈ Icc (0 : ℝ) T,
      MemOsc (min (M : ℝ) (2 + n * s67bd_delta d s)) (s67psi ρ₀ (f r)) ∧
      oscNorm (min (M : ℝ) (2 + n * s67bd_delta d s)) (s67psi ρ₀ (f r)) ≤ B := by
    intro n
    induction n with
    | zero =>
      obtain ⟨B, hB, h⟩ := s67bd_classical_sigma2 H ρ T φ f hT hf
      refine ⟨B, hB, fun r hr => ?_⟩
      have e : min (M : ℝ) (2 + ((0 : ℕ) : ℝ) * s67bd_delta d s) = 2 := by
        simp [hM2]
      rw [e]
      exact ⟨(h r hr).1, (h r hr).2.1⟩
    | succ n ih =>
      obtain ⟨B, hB, h⟩ := ih
      have hn0 : (0 : ℝ) ≤ n * s67bd_delta d s := by positivity
      obtain ⟨B', hB', h'⟩ := s67bd_bootstrap_step H M m hm hmM R0 c0 hR0 hc0 f0 ρ hρ T φ f hT hf
        hφ (min (M : ℝ) (2 + n * s67bd_delta d s)) (le_min hM2 (by linarith)) (min_le_left _ _)
        B hB h
      refine ⟨B', hB', fun r hr => ?_⟩
      have e : min (M : ℝ) (min (M : ℝ) (2 + n * s67bd_delta d s) + s67bd_delta d s) =
          min (M : ℝ) (2 + ((n + 1 : ℕ) : ℝ) * s67bd_delta d s) := by
        push_cast
        rcases le_total (M : ℝ) (2 + n * s67bd_delta d s) with h1 | h1
        · rw [min_eq_left h1, min_eq_left (by linarith), min_eq_left (by nlinarith)]
        · rw [min_eq_right h1]
          congr 1
          ring
      rw [← e]
      exact h' r hr
  obtain ⟨N, hN⟩ := exists_nat_ge (((M : ℝ) - 2) / s67bd_delta d s)
  obtain ⟨B, hB, h⟩ := key N
  have hN' : (M : ℝ) ≤ 2 + N * s67bd_delta d s := by
    have := (div_le_iff₀ hδ0).1 hN
    linarith
  rw [min_eq_left hN'] at h
  exact ⟨B, hB, h⟩

end HRS.MS.BreakdownS67
