import HRS.MC.QRPWickLimAux2

/-!
# QRPWickLim: `qrs_wick_var_lim_proof` (passage to the `IsHalfWick` limit)

Relocated proof of `HRS.MC.QRSpec.qrs_wick_var_lim`.  Route: the finite-section bound `qrpw_sect`
(from `qrs_wick_var_fin_proof`) for `Q_S - Q_F`, `S ⊇ F`, and the `L²` convergence `Q_S → Q` of `IsHalfWick`
(an `ε`-splitting `(x+y)² ≤ (1+ε)y² + (1+1/ε)x²`, then `S ↑`, then `ε ↓ 0`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.QRSpec.Wick

open HRS.Sec7

variable {d : ℕ}

lemma qrpw_sq_integral_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → ℝ} (hf : MemLp f 2 P) : (∫ ω, f ω ∂P) ^ 2 ≤ ∫ ω, f ω ^ 2 ∂P := by
  have h := variance_nonneg f P
  rw [variance_eq_sub hf] at h
  simp only [Pi.pow_apply] at h
  linarith

lemma qrpw_enorm_sq (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

theorem qrs_wick_var_lim_proof {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r : ℝ) (η : Ω → NegSobolev d r) (hη : HasFiniteGaussianCoeffs P η) (K : ℝ)
    (hK : ModeCovBound P η K)
    (μ : Measure (Torus d)) (h : Torus d → Torus d → ℝ) (Q : Ω → ℝ) (hQ : IsHalfWick P η μ h Q)
    (hQm : AEStronglyMeasurable Q P)
    (hHS : Summable fun p : NonzeroLattice d × NonzeroLattice d => wickCoeff μ h p.1 p.2 ^ 2) :
    MemLp Q 2 P ∧ ∫ ω, Q ω ∂P = 0 ∧
    ∀ F : Finset (NonzeroLattice d),
      MemLp (fun ω => Q ω - wickSection P η μ h F ω) 2 P ∧
      ∫ ω, (Q ω - wickSection P η μ h F ω) ^ 2 ∂P ≤ (1 / 2) * K ^ 2 * tailHS (wickCoeff μ h) F := by
  have hQm' : ∀ S, AEStronglyMeasurable (fun ω => Q ω - wickSection P η μ h S ω) P :=
    fun S => hQm.sub (qrpw_wickSection_meas hη μ h S)
  have htend : Tendsto (fun S : Finset (NonzeroLattice d) =>
      ∫⁻ ω, ‖Q ω - wickSection P η μ h S ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) := hQ
  have hDreal : ∀ S : Finset (NonzeroLattice d), ∫ ω, (Q ω - wickSection P η μ h S ω) ^ 2 ∂P =
      (∫⁻ ω, ‖Q ω - wickSection P η μ h S ω‖ₑ ^ 2 ∂P).toReal := by
    intro S
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => sq_nonneg _)
      ((hQm' S).pow 2)]
    simp_rw [qrpw_enorm_sq]
  have hDlim : Tendsto (fun S : Finset (NonzeroLattice d) =>
      ∫ ω, (Q ω - wickSection P η μ h S ω) ^ 2 ∂P) atTop (𝓝 0) := by
    simp_rw [hDreal]
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htend
    simpa only [Function.comp_def, ENNReal.toReal_zero] using this
  have hDmem : ∀ᶠ S : Finset (NonzeroLattice d) in atTop,
      MemLp (fun ω => Q ω - wickSection P η μ h S ω) 2 P := by
    filter_upwards [htend.eventually (Iio_mem_nhds (ENNReal.zero_lt_top))] with S hS
    refine (memLp_two_iff_integrable_sq (hQm' S)).2 ⟨(hQm' S).pow 2, ?_⟩
    have : ∫⁻ ω, ‖(Q ω - wickSection P η μ h S ω) ^ 2‖ₑ ∂P =
        ∫⁻ ω, ‖Q ω - wickSection P η μ h S ω‖ₑ ^ 2 ∂P := by
      simp_rw [enorm_pow]
    unfold HasFiniteIntegral
    rw [this]
    exact hS
  have hsect := fun F S (hFS : F ⊆ S) => qrpw_sect hη hK μ h hHS F S hFS
  have key : ∀ F : Finset (NonzeroLattice d),
      MemLp (fun ω => Q ω - wickSection P η μ h F ω) 2 P ∧
      ∫ ω, (Q ω - wickSection P η μ h F ω) ^ 2 ∂P ≤ (1 / 2) * K ^ 2 * tailHS (wickCoeff μ h) F := by
    intro F
    have hev : ∀ᶠ S : Finset (NonzeroLattice d) in atTop,
        F ⊆ S ∧ MemLp (fun ω => Q ω - wickSection P η μ h S ω) 2 P :=
      (eventually_ge_atTop F).and hDmem
    have hsplit : ∀ S, ∀ ω, Q ω - wickSection P η μ h F ω =
        (Q ω - wickSection P η μ h S ω) + (wickSection P η μ h S ω - wickSection P η μ h F ω) :=
      fun S ω => by ring
    have hmem : MemLp (fun ω => Q ω - wickSection P η μ h F ω) 2 P := by
      obtain ⟨S, hS1, hS2⟩ := hev.exists
      have := hS2.add (hsect F S hS1).1
      refine this.ae_eq (Filter.Eventually.of_forall fun ω => ?_)
      simp only [Pi.add_apply]
      exact (hsplit S ω).symm
    refine ⟨hmem, ?_⟩
    set B : ℝ := (1 / 2) * K ^ 2 * tailHS (wickCoeff μ h) F with hB
    have hB0 : 0 ≤ B := le_trans (integral_nonneg fun ω => sq_nonneg _) (hsect F F le_rfl).2
    have hε : ∀ ε : ℝ, 0 < ε → ∫ ω, (Q ω - wickSection P η μ h F ω) ^ 2 ∂P ≤ (1 + ε) * B := by
      intro ε hε
      have hbound : ∀ᶠ S : Finset (NonzeroLattice d) in atTop,
          ∫ ω, (Q ω - wickSection P η μ h F ω) ^ 2 ∂P ≤ (1 + ε) * B +
            (1 + 1 / ε) * ∫ ω, (Q ω - wickSection P η μ h S ω) ^ 2 ∂P := by
        filter_upwards [hev] with S ⟨hS1, hS2⟩
        have hR := hsect F S hS1
        have i1 := hmem.integrable_sq
        have i2 := hS2.integrable_sq
        have i3 := hR.1.integrable_sq
        have hpt : ∀ ω, (Q ω - wickSection P η μ h F ω) ^ 2 ≤
            (1 + ε) * (wickSection P η μ h S ω - wickSection P η μ h F ω) ^ 2 +
              (1 + 1 / ε) * (Q ω - wickSection P η μ h S ω) ^ 2 := by
          intro ω
          rw [hsplit S ω]
          set x := Q ω - wickSection P η μ h S ω
          set y := wickSection P η μ h S ω - wickSection P η μ h F ω
          have h2 : 2 * x * y ≤ ε * y ^ 2 + x ^ 2 / ε := by
            have e : ε * y ^ 2 + x ^ 2 / ε = (ε * y - x) ^ 2 / ε + 2 * x * y := by
              field_simp; ring
            rw [e]
            have : 0 ≤ (ε * y - x) ^ 2 / ε := div_nonneg (sq_nonneg _) hε.le
            linarith
          have e1 : (1 + 1 / ε) * x ^ 2 = x ^ 2 + x ^ 2 / ε := by field_simp
          nlinarith
        calc ∫ ω, (Q ω - wickSection P η μ h F ω) ^ 2 ∂P
            ≤ ∫ ω, ((1 + ε) * (wickSection P η μ h S ω - wickSection P η μ h F ω) ^ 2 +
              (1 + 1 / ε) * (Q ω - wickSection P η μ h S ω) ^ 2) ∂P :=
              integral_mono i1 ((i3.const_mul _).add (i2.const_mul _)) hpt
          _ = (1 + ε) * ∫ ω, (wickSection P η μ h S ω - wickSection P η μ h F ω) ^ 2 ∂P +
              (1 + 1 / ε) * ∫ ω, (Q ω - wickSection P η μ h S ω) ^ 2 ∂P := by
              rw [integral_add (i3.const_mul _) (i2.const_mul _), integral_const_mul,
                integral_const_mul]
          _ ≤ _ := by
              have hR2 : ∫ ω, (wickSection P η μ h S ω - wickSection P η μ h F ω) ^ 2 ∂P ≤ B := hR.2
              have := mul_le_mul_of_nonneg_left hR2 (by linarith : (0 : ℝ) ≤ 1 + ε)
              linarith
      have hlim : Tendsto (fun S : Finset (NonzeroLattice d) => (1 + ε) * B +
          (1 + 1 / ε) * ∫ ω, (Q ω - wickSection P η μ h S ω) ^ 2 ∂P) atTop
          (𝓝 ((1 + ε) * B + (1 + 1 / ε) * 0)) :=
        tendsto_const_nhds.add (hDlim.const_mul _)
      have := ge_of_tendsto hlim hbound
      simpa using this
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have h1 := hε (δ / (B + 1)) (by positivity)
    have h2 : δ / (B + 1) * B ≤ δ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    nlinarith
  have hQ2 : MemLp Q 2 P := by
    have := (key ∅).1
    simpa [qrpw_wickSection_empty] using this
  refine ⟨hQ2, ?_, key⟩
  have hint : ∀ S : Finset (NonzeroLattice d), Integrable (wickSection P η μ h S) P := by
    intro S
    have := (hsect ∅ S (Finset.empty_subset S)).1
    simp only [qrpw_wickSection_empty, sub_zero] at this
    exact this.integrable (by norm_num)
  have hbd : ∀ᶠ S : Finset (NonzeroLattice d) in atTop,
      (∫ ω, Q ω ∂P) ^ 2 ≤ ∫ ω, (Q ω - wickSection P η μ h S ω) ^ 2 ∂P := by
    filter_upwards [hDmem] with S hS
    have h1 := qrpw_sq_integral_le hS
    rwa [integral_sub (hQ2.integrable (by norm_num)) (hint S), qrpw_wickSection_integral hη μ h S, sub_zero] at h1
  have := ge_of_tendsto hDlim hbd
  nlinarith [sq_nonneg (∫ ω, Q ω ∂P)]

end HRS.MC.QRSpec.Wick

end
