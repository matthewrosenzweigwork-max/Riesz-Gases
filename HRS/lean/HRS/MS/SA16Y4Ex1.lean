import HRS.MS.SA16Y4Ct18
import HRS.MS.SA16Y4Ct19

/-!
# S.A.16 (SA16Y4) Ex1: existence of an `IsLpSolutionRd` for `LpCase.sub` (existence clause of `adjoint_lp`)

`sa16y4_sub_exists`: for `s ≤ d-2`, `d < p(s+1)`, `m ≥ 1`, `IsUlocCutoff χ`, there is `C > 0` such that for every `AdjointRdData`,
`t ∈ (0,T]`, `φ` with `wNormE m p φ < ⊤` there is `F` with `IsLpSolutionRd m p χ (D.coeff μ) t φ F` and
`wNormE m p (F τ) ≤ C e^{Cτ} wNormE m p φ` on `[0,t]` (exactly the first conjunct of `adjoint_lp` for `LpCase.sub`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Ex1
variable {d : ℕ}

lemma sa16y4_shift_cutoff {χ : EuclideanSpace ℝ (Fin d) → ℝ} (hχ : IsUlocCutoff χ) (z : EuclideanSpace ℝ (Fin d)) :
    ContDiff ℝ ∞ (fun x => χ (x - z)) ∧ HasCompactSupport (fun x => χ (x - z)) ∧
      tsupport (fun x => χ (x - z)) ⊆ Metric.closedBall 0 (‖z‖ + 2) := by
  refine ⟨hχ.1.comp (contDiff_id.sub contDiff_const), hχ.2.1.comp_homeomorph (Homeomorph.subRight z), ?_⟩
  refine closure_minimal (fun x hx => ?_) isClosed_closedBall
  have h1 : x - z ∈ tsupport χ := subset_tsupport χ hx
  have h2 : ‖x - z‖ < 2 := by simpa using hχ.2.2.1 h1
  rw [mem_closedBall_zero_iff]
  calc ‖x‖ = ‖(x - z) + z‖ := by congr 1; abel
    _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ ‖z‖ + 2 := by linarith

set_option maxHeartbeats 1600000 in
theorem sa16y4_sub_exists (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m) (p : ℝ)
    [Fact (2 ≤ p)] (MB Λ ΛV G₀ νbar T : ℝ) (χ : EuclideanSpace ℝ (Fin d) → ℝ) (hχ : IsUlocCutoff χ)
    (hsub : s ≤ (d : ℝ) - 2 ∧ (d : ℝ) < p * (s + 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : WholeDyn d) (μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ),
      AdjointRdData s m MB Λ ΛV G₀ νbar D T μ → ∀ t ∈ Ioc (0 : ℝ) T,
      ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, wNormE m p φ < ⊤ →
        ∃ F : ℝ → EuclideanSpace ℝ (Fin d) → ℝ, IsLpSolutionRd m p χ (D.coeff μ) t φ F ∧
          ∀ τ ∈ Icc (0 : ℝ) t, wNormE m p (F τ) ≤ ENNReal.ofReal (C * Real.exp (C * τ)) * wNormE m p φ := by
  obtain ⟨Kc, cE, hKc, H⟩ := sa16y4_sub_limit hd s hs0 hsd m hm p MB Λ ΛV G₀ νbar T hsub
  refine ⟨max (max Kc cE) 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun D μ hD t ht φ hφ => ?_⟩
  obtain ⟨G, hGb, hGw, hGid⟩ := H D μ hD t ht φ hφ
  set w : ℝ := (wNormE m p φ).toReal with hw
  have hw0 : 0 ≤ w := ENNReal.toReal_nonneg
  set Bg : ℝ := Kc * w * Real.exp (|cE| * t) with hBg
  have hbd : ∀ τ ∈ Icc (0 : ℝ) t, ‖G τ‖ ≤ Bg := by
    intro τ hτ
    refine (hGb τ hτ).trans ?_
    have h2 : Real.exp (cE * τ) ≤ Real.exp (|cE| * t) := by
      refine Real.exp_le_exp.2 ?_
      calc cE * τ ≤ |cE| * τ := mul_le_mul_of_nonneg_right (le_abs_self _) hτ.1
        _ ≤ |cE| * t := mul_le_mul_of_nonneg_left hτ.2 (abs_nonneg _)
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hmem : ∀ τ ∈ Icc (0 : ℝ) t, τ ∈ Icc (0 : ℝ) t := fun τ hτ => hτ
  refine ⟨fun τ x => wrep d m p (G τ) x, ⟨⟨?_, ?_, ?_⟩, sa16y3_wcont_of_path (Bg := Bg) G hGw,
    sa16y3_bounded_of_path G hbd, ?_⟩, ?_⟩
  · intro ψ hψ σ hσ
    exact sa16y4_integrable_fields hd s hs0 hsd m hm p MB Λ ΛV G₀ νbar T D μ hD ht (G σ) hψ hσ
  · intro ψ hψ
    exact (hGid hψ).2
  · intro ψ hψ τ hτ
    exact (hGid hψ).1 τ hτ
  · intro m' hm' z τ₀ hτ₀ ε hε
    obtain ⟨h1, h2, h3⟩ := sa16y4_shift_cutoff hχ z
    exact sa16y4_cont_abstract m m' hm' h1 h2 h3 G hbd hGw hτ₀ hε
  · intro τ hτ
    have hC1 : Kc ≤ max (max Kc cE) 1 := (le_max_left _ _).trans (le_max_left _ _)
    have hC2 : cE ≤ max (max Kc cE) 1 := (le_max_right _ _).trans (le_max_left _ _)
    have hexp : Real.exp (cE * τ) ≤ Real.exp (max (max Kc cE) 1 * τ) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hC2 hτ.1)
    have hbd2 : ‖G τ‖ ≤ max (max Kc cE) 1 * Real.exp (max (max Kc cE) 1 * τ) * w := by
      refine (hGb τ hτ).trans ?_
      calc Kc * w * Real.exp (cE * τ) ≤ max (max Kc cE) 1 * w * Real.exp (max (max Kc cE) 1 * τ) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hC1 hw0) hexp (Real.exp_pos _).le (by positivity)
        _ = _ := by ring
    calc wNormE m p (fun x => wrep d m p (G τ) x) ≤ ENNReal.ofReal ‖G τ‖ := sa16y3_wNormE_le (G τ)
      _ ≤ ENNReal.ofReal (max (max Kc cE) 1 * Real.exp (max (max Kc cE) 1 * τ) * w) := ENNReal.ofReal_le_ofReal hbd2
      _ = ENNReal.ofReal (max (max Kc cE) 1 * Real.exp (max (max Kc cE) 1 * τ)) * wNormE m p φ := by
          rw [ENNReal.ofReal_mul (by positivity), hw, ENNReal.ofReal_toReal hφ.ne]
end Ex1

end HRS.Whole.AppendixA.Phase2SA16R
