import HRS.MS.ProClosureS111PathMoments

/-! Quantitative dyadic envelope for fourth-moment increments. -/

set_option autoImplicit false
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.Fp81.S21
open HRS.MP.KC HRS.MS.ProClosureS111

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Fourth-order increment bounds yield one random dyadic envelope whose
fourth moment is bounded uniformly by the increment constant and horizon. -/
theorem fp81s21_fourth_dyadic_envelope
    (P : Measure Ω) (X : ℝ → Ω → E) {H r C : ℝ}
    (hH : 0 < H) (hr0 : 0 < r) (hC : 0 ≤ C) (hr : 1 < 2 * r ^ 4)
    (hX : ∀ t, Measurable (X t))
    (hmom : ∀ s ∈ Set.Icc (0 : ℝ) H, ∀ t ∈ Set.Icc (0 : ℝ) H,
      (∫⁻ ω, ENNReal.ofReal (‖X t ω - X s ω‖ ^ 4) ∂P) ≤
        ENNReal.ofReal (C * |t - s| ^ 2)) :
    ∃ L : Ω → ℝ, (∀ ω, 0 ≤ L ω) ∧ MemLp L 4 P ∧
      (∀ᵐ ω ∂P, ω ∈ mkc_G X H r (L ω)) ∧
      (∫ ω, L ω ^ 4 ∂P) ≤ C * H ^ 2 / (1 - 1 / (2 * r ^ 4)) := by
  let K : ℝ := C * H ^ 2 / (1 - 1 / (2 * r ^ 4))
  have hq : 1 / (2 * r ^ 4) < 1 := (div_lt_one (by positivity)).2 hr
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact div_nonneg (mul_nonneg hC (sq_nonneg H)) (sub_nonneg.mpr hq.le)
  let f : (Σ n : ℕ, Fin (2 ^ n)) → Ω → ℝ := fun j ω =>
    ‖X (mkc_pt H j.1 ((j.2 : ℕ) + 1)) ω - X (mkc_pt H j.1 (j.2 : ℕ)) ω‖ / r ^ j.1
  have hf : ∀ j, Measurable (f j) := fun j =>
    ((hX _).sub (hX _)).norm.div_const _
  have hf0 : ∀ j ω, 0 ≤ f j ω := fun _ _ =>
    div_nonneg (norm_nonneg _) (pow_nonneg hr0.le _)
  have henergy : (∑' j, ∫⁻ ω, ENNReal.ofReal (|f j ω| ^ 4) ∂P) ≤
      ENNReal.ofReal K := by
    simpa only [abs_of_nonneg (hf0 _ _)] using
      fourth_increment_energy_bound P X hH hr0 hC hr hmom
  obtain ⟨L, hL0, hL, hbound, heq⟩ :=
    exists_fourth_moment_envelope_with_integral P f hf
      (henergy.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨L, hL0, hL, ?_, ?_⟩
  · filter_upwards [hbound] with ω hω
    intro n k hk
    have hb := hω (⟨n, ⟨k, hk⟩⟩ : (Σ n : ℕ, Fin (2 ^ n)))
    rw [abs_of_nonneg (hf0 _ _)] at hb
    exact (div_le_iff₀ (pow_pos hr0 n)).1 hb
  · have hi : Integrable (fun ω => L ω ^ 4) P := by
      simpa only [Real.norm_of_nonneg (hL0 _)] using
        hL.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
    have he : ENNReal.ofReal (∫ ω, L ω ^ 4 ∂P) =
        ∫⁻ ω, ENNReal.ofReal (L ω ^ 4) ∂P :=
      ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun ω => by positivity)
    have hb : ENNReal.ofReal (∫ ω, L ω ^ 4 ∂P) ≤ ENNReal.ofReal K := by
      rw [he, heq]
      exact henergy
    exact (ENNReal.ofReal_le_ofReal_iff hK).1 hb

#print axioms fp81s21_fourth_dyadic_envelope

end HRS.Fp81.S21
