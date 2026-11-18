import HRS.MS.S82RN8
import HRS.Equilibrium.ReferenceMarginal

/-!
# S8.2 R02 (S82R), N9: pinned marginal versus the full unpinned marginal, at measure level
Chain: `n` free particles with `p` pins (strength `lam`) -> `n` free particles without pins (N6) ->
`n + k` free particles (k removal steps, N8), with a position weight.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ENNReal BigOperators

namespace HRS.MS.S82R
open HRS.External HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem s82r_cav_chain (hd : 2 ≤ d) {q : Euc d → ℝ} (hq : ShortRangePole d q) (M : ℝ)
    {Mψ M₁ P β γ : ℝ} (hβ : 0 < β) (hγ : 0 ≤ γ)
    (hα : β * γ * (Real.exp (Mψ + (M₁ + P)) + Real.exp (Mψ + (M₁ + P)) ^ 2) < 1) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ ρμ : Euc d → ℝ, HRS.Whole.IsProbDensity ρμ → (∀ x, ρμ x ≤ M) →
      ∀ (μ : Measure (Euc d)), μ = HRS.Whole.withDensityReal ρμ →
      ∀ (V : WeakPotential μ), (∀ x y, V.q x y = q (x - y)) →
      V.γ = γ → IsField μ V.φ Mψ M₁ →
      ∀ {N : ℕ} {lam : ℝ}, 0 ≤ lam → lam * (N : ℝ) * γ ≤ P → ((N : ℝ) - 1) * lam ≤ β →
      ∀ {K' : ℝ}, 0 ≤ K' →
      (∀ m : ℕ, m ≤ N → ∀ [NeZero m] (i : Fin m),
        (pinnedLaw V lam m (fun e : Empty => e.elim)).map (fun y => y i) ≤
          ENNReal.ofReal K' • μ) →
      ∀ {n : ℕ} [NeZero n] (k : ℕ), n + k ≤ N → ∀ {S : Set (Euc d)}, MeasurableSet S →
      |(RefMarg.cavMarg V lam (n + k)).real S - (RefMarg.cavMarg V lam n).real S| ≤
        k * (K' * (lam * (A * γ + B))) * μ.real S := by
  obtain ⟨A, B, hA, hB, hrem⟩ := s82r_removal_measure hd hq M hβ hγ hα
  refine ⟨A, B, hA, hB, fun ρμ hρ hM μ hμ V hVq hVγ hψ N lam hlam hP hnl K' hK' hmarg n _ k => ?_⟩
  induction k with
  | zero =>
    intro _ S hS
    simp
  | succ k ih =>
    intro hk S hS
    have ih' := ih (by omega) hS
    haveI : NeZero (n + k) := ⟨by have := NeZero.ne n; omega⟩
    have hnk : n + k ≤ N := by omega
    have hn1 : ((n + k : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast hk
    have hn0 : (0 : ℝ) ≤ ((n + k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hP' : lam * (((n + k : ℕ) : ℝ) + 1) * γ ≤ P := by
      refine le_trans ?_ hP
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn1 hlam) hγ
    have hnl' : (((n + k : ℕ) : ℝ) - 1) * lam ≤ β := by
      refine le_trans ?_ hnl
      exact mul_le_mul_of_nonneg_right (by linarith) hlam
    have hz : (Fin.last (n + k)).succAbove (0 : Fin (n + k)) = (0 : Fin (n + k + 1)) :=
      Fin.ext (by simp [Fin.succAbove_last])
    have hstep := hrem ρμ hρ hM μ hμ V hVq hVγ hψ (n := n + k) hlam hP' hnl' (Fin.last (n + k)) 0
      hK' (hmarg (n + k + 1) hk (Fin.last (n + k))) hS
    rw [hz] at hstep
    have e1 : (RefMarg.cavMarg V lam (n + k + 1)).real S =
        ((pinnedLaw V lam (n + k + 1) (fun e : Empty => e.elim)).map (fun y => y 0)).real S := rfl
    have e2 : (RefMarg.cavMarg V lam (n + k)).real S =
        ((pinnedLaw V lam (n + k) (fun e : Empty => e.elim)).map (fun y => y 0)).real S := rfl
    change |(RefMarg.cavMarg V lam (n + k + 1)).real S - (RefMarg.cavMarg V lam n).real S| ≤ _
    rw [e1] at *
    rw [← e2] at hstep
    have hμS : 0 ≤ μ.real S := measureReal_nonneg
    have hc0 : 0 ≤ K' * (lam * (A * γ + B)) :=
      mul_nonneg hK' (mul_nonneg hlam (add_nonneg (mul_nonneg hA hγ) hB))
    calc _ ≤ |((pinnedLaw V lam (n + k + 1) (fun e : Empty => e.elim)).map (fun y => y 0)).real S -
            (RefMarg.cavMarg V lam (n + k)).real S| +
          |(RefMarg.cavMarg V lam (n + k)).real S - (RefMarg.cavMarg V lam n).real S| := abs_sub_le _ _ _
      _ ≤ K' * (lam * (A * γ + B)) * μ.real S + k * (K' * (lam * (A * γ + B))) * μ.real S :=
          add_le_add hstep ih'
      _ = ((k + 1 : ℕ) : ℝ) * (K' * (lam * (A * γ + B))) * μ.real S := by push_cast; ring


/-- Pins (strength `lam` each) versus no pins, same number `n` of free particles. -/
theorem s82r_pins_to_cav (hd : 2 ≤ d) {q : Euc d → ℝ} (hq : ShortRangePole d q) (M : ℝ)
    {Mψ M₁ P β γ : ℝ} (hβ : 0 < β) (hγ : 0 ≤ γ)
    (hα : β * γ * (Real.exp (Mψ + (M₁ + P)) + Real.exp (Mψ + (M₁ + P)) ^ 2) < 1) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ ρμ : Euc d → ℝ, HRS.Whole.IsProbDensity ρμ → (∀ x, ρμ x ≤ M) →
      ∀ (μ : Measure (Euc d)), μ = HRS.Whole.withDensityReal ρμ →
      ∀ (V : WeakPotential μ), (∀ x y, V.q x y = q (x - y)) →
      V.γ = γ → IsField μ V.φ Mψ M₁ →
      ∀ {lam : ℝ}, 0 ≤ lam → ∀ {p n : ℕ} [NeZero n] (pins : Fin p → Euc d),
      lam * ((p : ℝ) + n) * γ ≤ P → ((n : ℝ) - 1) * lam ≤ β →
      ∀ (i0 : Fin n) {S : Set (Euc d)}, MeasurableSet S →
      |((pinnedLaw V lam n pins).map (fun y => y i0)).real S -
        (RefMarg.cavMarg V lam n).real S| ≤
        ∫ z in S, ∑ ℓ, lam * (A * q (z - pins ℓ) + B) ∂μ := by
  obtain ⟨A, B, hA, hB, hpin⟩ := s82r_pin_measure hd hq M hβ hγ hα
  refine ⟨A, B, hA, hB, fun ρμ hρ hM μ hμ V hVq hVγ hψ lam hlam p n _ pins hP hnl i0 S hS => ?_⟩
  subst hμ
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρμ) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have h := hpin ρμ hρ hM _ rfl V hVq hVγ hψ (m := p) (n := n) pins (fun _ => lam)
    (fun _ => hlam) hlam (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      nlinarith [hP]) hnl i0 hS
  have e0 : (RefMarg.cavMarg V lam n).real S = (fieldLaw V V.φ lam n).real
      ((fun y : Fin n → Euc d => y i0) ⁻¹' S) := by
    rw [← RefMarg.pinnedLaw_marginal_eq V n i0, RefMarg.pinnedLaw_empty V lam n (fun e : Empty => e.elim)]
    simp only [Measure.real, Measure.map_apply (f := fun y : Fin n → Euc d => y i0) (measurable_pi_apply i0) hS]
  have e1 : ((pinnedLaw V lam n pins).map (fun y => y i0)).real S =
      (fieldLaw V (s82r_Fld V pins (fun _ => lam) Finset.univ V.φ) lam n).real
        ((fun y : Fin n → Euc d => y i0) ⁻¹' S) := by
    have : pinnedLaw V lam n pins = fieldLaw V (s82r_Fld V pins (fun _ => lam) Finset.univ V.φ) lam n := by
      unfold pinnedLaw
      congr 1
      funext z
      simp only [pinField, s82r_Fld, Finset.mul_sum]
    rw [this]
    simp only [Measure.real, Measure.map_apply (f := fun y : Fin n → Euc d => y i0) (measurable_pi_apply i0) hS]
  rw [e0, e1, abs_sub_comm]
  exact h

end HRS.MS.S82R

end
