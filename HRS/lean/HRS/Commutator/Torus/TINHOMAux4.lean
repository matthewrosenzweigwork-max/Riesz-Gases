import HRS.Commutator.Torus.TINHOMAux3

/-!
# T-INHOM helpers, part 4: splitting `P^η_≤ v = v_lo + M`, `v_lo` of Fourier support `η|k| < 1/2`, `‖M‖_∞ ≲ ηL`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

theorem tinhom_vsplit (hd : 1 ≤ d) :
    ∃ CM : ℝ, 0 < CM ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (v : Torus d → Euc d) (L : ℝ), 0 ≤ L →
      IsLipschitzVF L v →
      ∃ vlo M : Torus d → Euc d, (∀ z, PleqT η v z = vlo z + M z) ∧ Continuous vlo ∧ Continuous M ∧
        (∀ z, ‖M z‖ ≤ CM * η * L) ∧
        ∃ (B : Finset (Lattice d)) (c : Fin d → Lattice d → ℂ),
          (∀ i z, ((vlo z i : ℝ) : ℂ) = ∑ k ∈ B, c i k * Torus.mode k z) ∧
          (∀ i k, c i k ≠ 0 → η * Lattice.enorm k < 1 / 2) := by
  obtain ⟨C₂, hC₂, hbd⟩ := tsamp_vhi_bounded_core hd
  refine ⟨5 * C₂ + 4 * d + C₂, by positivity, fun η hη hη1 v L hL hv => ?_⟩
  have hvc : Continuous v := tsamp_lip_continuous hv
  by_cases hsmall : η ≤ 1 / 4
  · -- `v_lo = P^{4η}_≤ v`
    have h4 : 0 < 4 * η := by positivity
    have h41 : 4 * η ≤ 1 := by linarith
    obtain ⟨hc1, hb1⟩ := hbd η hη hη1 v L hL hv
    obtain ⟨hc4, hb4⟩ := hbd (4 * η) h4 h41 v L hL hv
    refine ⟨PleqT (4 * η) v, fun z => PleqT η v z - PleqT (4 * η) v z,
      fun z => (add_sub_cancel (PleqT (4 * η) v z) (PleqT η v z)).symm, ?_, ?_, ?_, ?_⟩
    · have : (PleqT (4 * η) v) = fun z => v z - PgtT (4 * η) v z := by
        funext z; unfold PgtT; abel
      rw [this]
      exact hvc.sub hc4
    · have : (fun z => PleqT η v z - PleqT (4 * η) v z) = fun z => PgtT (4 * η) v z - PgtT η v z := by
        funext z; unfold PgtT; abel
      rw [this]
      exact hc4.sub hc1
    · intro z
      show ‖PleqT η v z - PleqT (4 * η) v z‖ ≤ _
      have : PleqT η v z - PleqT (4 * η) v z = PgtT (4 * η) v z - PgtT η v z := by
        unfold PgtT; abel
      rw [this]
      calc ‖PgtT (4 * η) v z - PgtT η v z‖ ≤ ‖PgtT (4 * η) v z‖ + ‖PgtT η v z‖ := norm_sub_le _ _
        _ ≤ C₂ * (4 * η) * L + C₂ * η * L := add_le_add (hb4 z) (hb1 z)
        _ ≤ (5 * C₂ + 4 * d + C₂) * η * L := by
            have : 0 ≤ (4 * (d : ℝ) + C₂) * η * L := by positivity
            nlinarith
    · refine ⟨HRS.PDE.Kern.boxF d ⌈2 / (4 * η)⌉₊,
        fun i k => ((tkrChi (4 * η) k : ℝ) : ℂ) * Torus.fcoef (fun x => v x i) k,
        fun i z => tlowv_Pleq_trig hd h4 h41 hL hv i z, ?_⟩
      intro i k hk
      by_contra hcon
      push Not at hcon
      apply hk
      have : tkrChi (4 * η) k = 0 := by
        apply tkrChi_eq_zero _ h4
        linarith
      simp [this]
  · -- `η > 1/4`: `v_lo` is the constant `v(0)`
    push Not at hsmall
    obtain ⟨hc1, hb1⟩ := hbd η hη hη1 v L hL hv
    refine ⟨fun _ => v 0, fun z => PleqT η v z - v 0,
      fun z => (add_sub_cancel (v 0) (PleqT η v z)).symm, continuous_const, ?_, ?_, ?_⟩
    · have : (fun z => PleqT η v z - v 0) = fun z => (v z - v 0) - PgtT η v z := by
        funext z; unfold PgtT; abel
      rw [this]
      exact (hvc.sub continuous_const).sub hc1
    · intro z
      show ‖PleqT η v z - v 0‖ ≤ _
      have : PleqT η v z - v 0 = (v z - v 0) - PgtT η v z := by unfold PgtT; abel
      rw [this]
      have h1 : ‖v z - v 0‖ ≤ L * d := by
        have := hv z 0
        calc ‖v z - v 0‖ ≤ L * KernelGrad.tdist z 0 := this
          _ ≤ L * d := mul_le_mul_of_nonneg_left (KernelGrad.tdist_le_card z) hL
      calc ‖(v z - v 0) - PgtT η v z‖ ≤ ‖v z - v 0‖ + ‖PgtT η v z‖ := norm_sub_le _ _
        _ ≤ L * d + C₂ * η * L := add_le_add h1 (hb1 z)
        _ ≤ (5 * C₂ + 4 * d + C₂) * η * L := by
            have h2 : L * (d : ℝ) ≤ 4 * (d : ℝ) * η * L := by
              have : (1 : ℝ) ≤ 4 * η := by linarith
              have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
              nlinarith [mul_nonneg hL hd0]
            have : 0 ≤ (5 * C₂ + C₂) * η * L := by positivity
            nlinarith
    · refine ⟨{0}, fun i k => if k = 0 then ((v 0 i : ℝ) : ℂ) else 0, fun i z => ?_, ?_⟩
      · simp [Torus.mode_zero]
      · intro i k hk
        by_cases h0 : k = 0
        · subst h0
          simp [text_enorm_zero]
        · simp [h0] at hk

end HRS.Commutator.TorusNote
