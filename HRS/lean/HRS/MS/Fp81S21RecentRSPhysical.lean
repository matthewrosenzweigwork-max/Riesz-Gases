import HRS.MS.Fp81S21RSValue5

/-! Transport of actual recent RS values through translation and a zero tail.
The physical prediction and increment identifications must hold simultaneously
on the indicated intervals; no equality of selected values is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS.MS.R2Interp

/-- RS sums only use ordered endpoints and tags between those endpoints. -/
theorem fp81s21_recentRS_congrOn {q r I : ℝ}
    {S T : ℝ → ℝ → ℝ → ℝ}
    (hST : ∀ τ u v, q ≤ u → u ≤ τ → τ ≤ v → v ≤ r →
      S τ u v = T τ u v)
    (hS : fp81s21_IsRSOn q r S I) : fp81s21_IsRSOn q r T I := by
  intro ε hε
  obtain ⟨δ, hδ, hsum⟩ := hS ε hε
  refine ⟨δ, hδ, ?_⟩
  intro n u τ hu hu0 hur htag hmesh
  have heq : (∑ i : Fin n, T (q + τ i) (q + u i.castSucc) (q + u i.succ)) =
      ∑ i : Fin n, S (q + τ i) (q + u i.castSucc) (q + u i.succ) := by
    apply Finset.sum_congr rfl
    intro i _
    apply (hST _ _ _ ?_ ?_ ?_ ?_).symm
    · have h := hu.monotone (Fin.zero_le i.castSucc)
      rw [hu0] at h
      linarith
    · linarith [(htag i).1]
    · linarith [(htag i).2]
    · have h := hu.monotone (Fin.le_last i.succ)
      rw [hur] at h
      linarith
  rw [heq]
  exact hsum n u τ hu hu0 hur htag hmesh

/-- A physical RS certificate on `[b,b+h]` and the recent kernel certificate
on `[0,H]` specify the same value when their summands agree after translation
and the recent summand vanishes on `[h,H]`. This includes `h=0` and `h=H`. -/
theorem fp81s21_recentRS_value_of_shift_tail {b h H I J : ℝ}
    (hh : 0 ≤ h) (hhH : h ≤ H) {S T : ℝ → ℝ → ℝ → ℝ}
    (hphysical : fp81s21_IsRSOn b (b + h) S I)
    (hrecent : fp81s21_IsRSOn 0 H T J)
    (hmatch : ∀ τ u v, 0 ≤ u → u ≤ τ → τ ≤ v → v ≤ h →
      S (b + τ) (b + u) (b + v) = T τ u v)
    (htail : ∀ τ u v, h ≤ u → u ≤ τ → τ ≤ v → v ≤ H → T τ u v = 0) :
    I = J := by
  have hleft : fp81s21_IsRSOn 0 h T I := by
    have hshift : fp81s21_IsRSOn 0 h
        (fun τ u v => S (b + τ) (b + u) (b + v)) I := by
      simpa only [fp81s21_IsRSOn, add_sub_cancel_left, sub_zero, zero_add] using hphysical
    exact fp81s21_recentRS_congrOn hmatch hshift
  have hzero : fp81s21_IsRSOn h H (fun _ _ _ => 0) 0 :=
    fp81s21_isRSOn_zero_summand hhH (fun _ _ _ => rfl)
  have hright : fp81s21_IsRSOn h H T 0 :=
    fp81s21_recentRS_congrOn
      (fun τ u v hu huτ hτv hv => (htail τ u v hu huτ hτv hv).symm) hzero
  have hsplit := fp81s21_isRSOn_split_general hh hhH hrecent hleft hright
  simpa only [add_zero] using hsplit.symm

/-- The value transport applies on a common probability-good event, retaining
both supplied values. No measurability of the event-indexed summands is needed. -/
theorem fp81s21_recentRS_values_ae_of_shift_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {b h H : ℝ}
    (hh : 0 ≤ h) (hhH : h ≤ H) (S T : Ω → ℝ → ℝ → ℝ → ℝ)
    (I J : Ω → ℝ)
    (hphysical : ∀ᵐ ω ∂μ, fp81s21_IsRSOn b (b + h) (S ω) (I ω))
    (hrecent : ∀ᵐ ω ∂μ, fp81s21_IsRSOn 0 H (T ω) (J ω))
    (hmatch : ∀ᵐ ω ∂μ, ∀ τ u v, 0 ≤ u → u ≤ τ → τ ≤ v → v ≤ h →
      S ω (b + τ) (b + u) (b + v) = T ω τ u v)
    (htail : ∀ᵐ ω ∂μ, ∀ τ u v, h ≤ u → u ≤ τ → τ ≤ v → v ≤ H →
      T ω τ u v = 0) : I =ᵐ[μ] J := by
  filter_upwards [hphysical, hrecent, hmatch, htail] with ω hp hr hm ht
  exact fp81s21_recentRS_value_of_shift_tail hh hhH hp hr hm ht

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_recentRS_congrOn
#print axioms HRS.Fp81.S21.fp81s21_recentRS_value_of_shift_tail
#print axioms HRS.Fp81.S21.fp81s21_recentRS_values_ae_of_shift_tail
end
