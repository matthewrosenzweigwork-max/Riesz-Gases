import HRS.MS.SA16Y8Jc1

/-!
# S.A.16 (SA16Y8) Cl1: the family of `C²` representatives of a weakly continuous path in `W^{m,p}` (classical clause, K4, part 4)

For `F` weakly continuous in `W^{m,p}` and bounded, `m > 2 + d/p`, there are `C²` functions `u τ =ᵐ F τ` (`τ ∈ [0,t]`) with uniform bounds
on `u, ∇u, D²u`, a uniform Hölder modulus of `D²u`, and `τ ↦ u τ x`, `τ ↦ ∇u τ x v`, `τ ↦ D²u τ x v w` continuous on `[0,t]`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16 HRS.Whole.AppendixA.Phase2SA16R
open Phase2SA16Transfer Phase2SA16Evolution

section Cl1

/-- a lift of norm below `B + 1` -/
lemma sa16y8_lift {d : ℕ} (m : ℕ) (p : ℝ) [Fact (2 ≤ p)] {u : Euc d → ℝ} {B : ℝ}
    (hu : wNormE m p u ≤ ENNReal.ofReal B) :
    ∃ G : WmpSpace d m p, wrep d m p G =ᵐ[volume] u ∧ ‖G‖ ≤ max B 0 + 1 := by
  have hlt : wNormE m p u < ENNReal.ofReal (max B 0 + 1) :=
    lt_of_le_of_lt hu ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by
      have := le_max_left B 0; linarith))
  unfold wNormE at hlt
  rw [iInf_lt_iff] at hlt
  obtain ⟨G, hG⟩ := hlt
  rw [iInf_lt_iff] at hG
  obtain ⟨h, hn⟩ := hG
  refine ⟨G, h, ?_⟩
  exact ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hn).le

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 3200000 in
theorem sa16y8_family (d m : ℕ) (hd : 1 ≤ d) (p : ℝ) [Fact (2 ≤ p)] (hmp : 2 + (d : ℝ) / p < m) (t : ℝ)
    (F : ℝ → Euc d → ℝ) (B : ℝ) (hB : ∀ τ ∈ Icc (0 : ℝ) t, wNormE m p (F τ) ≤ ENNReal.ofReal B)
    (hw : ∀ G : ℝ → WmpSpace d m p,
      (∀ τ ∈ Icc (0 : ℝ) t, ∀ᵐ x ∂(volume : Measure (Euc d)),
        ((G τ : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) = F τ x) →
      ∀ ℓ : StrongDual ℝ (WmpSpace d m p), ContinuousOn (fun τ => ℓ (G τ)) (Icc (0 : ℝ) t)) :
    ∃ (u : ℝ → Euc d → ℝ) (K α : ℝ), 0 < K ∧ 0 < α ∧ (∀ τ ∈ Icc (0 : ℝ) t, u τ =ᵐ[volume] F τ) ∧
      (∀ τ ∈ Icc (0 : ℝ) t, ContDiff ℝ 2 (u τ)) ∧
      (∀ τ ∈ Icc (0 : ℝ) t, ∀ x, ‖u τ x‖ ≤ K ∧ ‖fderiv ℝ (u τ) x‖ ≤ K ∧ ‖sa16y8_D2 (u τ) x‖ ≤ K) ∧
      (∀ τ ∈ Icc (0 : ℝ) t, ∀ x h : Euc d, ‖h‖ ≤ 1 →
        ‖sa16y8_D2 (u τ) (x + h) - sa16y8_D2 (u τ) x‖ ≤ K * ‖h‖ ^ α) ∧
      (∀ x₀, ContinuousOn (fun τ => u τ x₀) (Icc (0 : ℝ) t)) ∧
      (∀ x₀ v, ContinuousOn (fun τ => fderiv ℝ (u τ) x₀ v) (Icc (0 : ℝ) t)) ∧
      (∀ x₀ v w, ContinuousOn (fun τ => sa16y8_D2 (u τ) x₀ v w) (Icc (0 : ℝ) t)) := by
  obtain ⟨C, α, hC, hα, hrep⟩ := sa16y8_rep d m hd p hmp
  have hex : ∀ τ : ℝ, ∃ G : WmpSpace d m p, τ ∈ Icc (0 : ℝ) t →
      (wrep d m p G =ᵐ[volume] F τ ∧ ‖G‖ ≤ max B 0 + 1) := by
    intro τ
    by_cases hτ : τ ∈ Icc (0 : ℝ) t
    · obtain ⟨G, hG⟩ := sa16y8_lift m p (hB τ hτ)
      exact ⟨G, fun _ => hG⟩
    · exact ⟨0, fun h => absurd h hτ⟩
  choose Gt hGt using hex
  choose R hR1 hR2 hR3 hR4 hR5 hR6 using hrep
  have hM : 0 < max B 0 + 1 := by positivity
  have hnorm : ∀ τ ∈ Icc (0 : ℝ) t, ‖Gt τ‖ ≤ max B 0 + 1 := fun τ hτ => (hGt τ hτ).2
  refine ⟨fun τ => R (Gt τ), C * (max B 0 + 1), α, by positivity, hα, ?_, fun τ _ => hR1 _, ?_, ?_, ?_⟩
  · intro τ hτ
    exact (hR2 (Gt τ)).symm.trans (hGt τ hτ).1
  · intro τ hτ x
    have hn := hnorm τ hτ
    have hC0 : 0 ≤ C := hC.le
    exact ⟨(hR3 _ x).trans (mul_le_mul_of_nonneg_left hn hC0),
      (hR4 _ x).trans (mul_le_mul_of_nonneg_left hn hC0),
      (hR5 _ x).trans (mul_le_mul_of_nonneg_left hn hC0)⟩
  · intro τ hτ x h hh
    have hn := hnorm τ hτ
    calc ‖sa16y8_D2 (R (Gt τ)) (x + h) - sa16y8_D2 (R (Gt τ)) x‖ ≤ C * ‖h‖ ^ α * ‖Gt τ‖ := hR6 _ x h hh
      _ ≤ C * ‖h‖ ^ α * (max B 0 + 1) :=
          mul_le_mul_of_nonneg_left hn (by positivity)
      _ = C * (max B 0 + 1) * ‖h‖ ^ α := by ring
  · have hG : ∀ τ ∈ Icc (0 : ℝ) t, ∀ᵐ x ∂(volume : Measure (Euc d)),
        ((Gt τ : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) = F τ x :=
      fun τ hτ => (hGt τ hτ).1
    refine ⟨fun x₀ => ?_, fun x₀ v => ?_, fun x₀ v w => ?_⟩
    · obtain ⟨⟨ℓ, hℓ⟩, -, -⟩ := sa16y8_eval d m hd p hmp x₀ 0 0
      refine (hw Gt hG ℓ).congr (fun τ _ => ?_)
      exact (hℓ (Gt τ) (R (Gt τ)) (hR1 _) (hR2 _)).symm
    · obtain ⟨-, ⟨ℓ, hℓ⟩, -⟩ := sa16y8_eval d m hd p hmp x₀ v 0
      refine (hw Gt hG ℓ).congr (fun τ _ => ?_)
      exact (hℓ (Gt τ) (R (Gt τ)) (hR1 _) (hR2 _)).symm
    · obtain ⟨-, -, ⟨ℓ, hℓ⟩⟩ := sa16y8_eval d m hd p hmp x₀ v w
      refine (hw Gt hG ℓ).congr (fun τ _ => ?_)
      exact (hℓ (Gt τ) (R (Gt τ)) (hR1 _) (hR2 _)).symm

end Cl1

end HRS.Whole.AppendixA.Phase2SA16Q
