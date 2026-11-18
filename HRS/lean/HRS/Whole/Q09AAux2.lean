import HRS.Whole.AppendixA

/-!
# Packet Q09-A, part 2: auxiliary lemmas for Lemma S.A.19 (`test_cutoff_pathwise`, `test_cutoff_expectation`)

Generic measure-theoretic lemmas (optimization over the cutoff scale, `lintegral` bound of the pathwise
estimate), facts on probability densities and second moments, used in `HRS/Whole/AppendixALemmas.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Whole.Q09A

theorem inf_bound (f : {R : ℝ // 1 ≤ R} → ℝ) (hf : ∀ R, 0 ≤ f R) (A : ℝ≥0∞) (c : ℝ)
    (hc : 0 ≤ c) (h : ∀ R, A ≤ ENNReal.ofReal (c * f R)) :
    A ≤ ENNReal.ofReal (c * (⨅ R, f R)) := by
  have hbdd : BddBelow (Set.range f) := ⟨0, by rintro _ ⟨R, rfl⟩; exact hf R⟩
  have hne : Nonempty {R : ℝ // 1 ≤ R} := ⟨⟨1, le_refl _⟩⟩
  have hinf0 : 0 ≤ ⨅ R, f R := le_ciInf hf
  rcases hc.eq_or_lt with hc0 | hcpos
  · subst hc0
    simpa using h ⟨1, le_refl _⟩
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hε' : (0:ℝ) < ε := by exact_mod_cast hε
    obtain ⟨R, hR⟩ := exists_lt_of_ciInf_lt (show (⨅ R, f R) < (⨅ R, f R) + (ε : ℝ) / c by
      have : 0 < (ε : ℝ) / c := by positivity
      linarith)
    calc A ≤ ENNReal.ofReal (c * f R) := h R
      _ ≤ ENNReal.ofReal (c * (⨅ R, f R) + ε) := by
          apply ENNReal.ofReal_le_ofReal
          have := mul_lt_mul_of_pos_left hR hcpos
          rw [mul_add, mul_div_cancel₀ _ hcpos.ne'] at this
          linarith
      _ = ENNReal.ofReal (c * (⨅ R, f R)) + ε := by
          rw [ENNReal.ofReal_add (mul_nonneg hc hinf0) hε'.le, ENNReal.ofReal_coe_nnreal]

theorem lintegral_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (L E m : Ω → ℝ) (hm : Measurable m) (K Q lam R 𝔈 m₂ : ℝ)
    (hK : 0 ≤ K) (hQ : 0 ≤ Q) (hlam : 0 ≤ lam) (hR : 0 < R) (h𝔈 : 0 < 𝔈) (hm₂ : 0 ≤ m₂)
    (hE : ∀ᵐ ζ ∂P, 0 ≤ E ζ) (hm0 : ∀ ζ, 0 ≤ m ζ)
    (hEint : ∫⁻ ζ, ENNReal.ofReal (E ζ) ∂P ≤ ENNReal.ofReal 𝔈)
    (hmint : ∫⁻ ζ, ENNReal.ofReal (m ζ) ∂P ≤ ENNReal.ofReal m₂)
    (hL : ∀ᵐ ζ ∂P, |L ζ| ≤ K * (Q * (lam + Real.sqrt (E ζ)) + m ζ / R ^ 2)) :
    ∫⁻ ζ, ENNReal.ofReal |L ζ| ∂P ≤
      ENNReal.ofReal (K * (Q * (lam + Real.sqrt 𝔈) + m₂ / R ^ 2)) := by
  set ε := Real.sqrt 𝔈 with hε
  have hεpos : 0 < ε := Real.sqrt_pos.mpr h𝔈
  have hε2 : ε ^ 2 = 𝔈 := Real.sq_sqrt h𝔈.le
  set A0 := K * Q * (lam + ε / 2) with hA0
  set A1 := K * Q / (2 * ε) with hA1
  set A2 := K / R ^ 2 with hA2
  have hA0n : 0 ≤ A0 := by positivity
  have hA1n : 0 ≤ A1 := by positivity
  have hA2n : 0 ≤ A2 := by positivity
  have hpt : ∀ᵐ ζ ∂P, ENNReal.ofReal |L ζ| ≤
      ENNReal.ofReal A0 + (ENNReal.ofReal A1 * ENNReal.ofReal (E ζ) +
        ENNReal.ofReal A2 * ENNReal.ofReal (m ζ)) := by
    filter_upwards [hE, hL] with ζ hEζ hLζ
    have hsq : Real.sqrt (E ζ) ≤ (E ζ / ε + ε) / 2 := by
      have h1 : 0 ≤ (Real.sqrt (E ζ) - ε) ^ 2 := sq_nonneg _
      have h2 : Real.sqrt (E ζ) ^ 2 = E ζ := Real.sq_sqrt hEζ
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
      have : E ζ / ε + ε - Real.sqrt (E ζ) * 2 = (Real.sqrt (E ζ) - ε) ^ 2 / ε := by
        field_simp
        nlinarith
      have h3 : 0 ≤ (Real.sqrt (E ζ) - ε) ^ 2 / ε := by positivity
      linarith
    have hreal : |L ζ| ≤ A0 + (A1 * E ζ + A2 * m ζ) := by
      refine hLζ.trans ?_
      have hb : K * (Q * (lam + Real.sqrt (E ζ)) + m ζ / R ^ 2) ≤
          K * (Q * (lam + (E ζ / ε + ε) / 2) + m ζ / R ^ 2) := by
        gcongr
      refine hb.trans (le_of_eq ?_)
      simp only [hA0, hA1, hA2]
      field_simp
      ring
    calc ENNReal.ofReal |L ζ| ≤ ENNReal.ofReal (A0 + (A1 * E ζ + A2 * m ζ)) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = _ := by
          rw [ENNReal.ofReal_add hA0n (by have := hm0 ζ; positivity), ENNReal.ofReal_add
            (by positivity) (by have := hm0 ζ; positivity), ENNReal.ofReal_mul hA1n,
            ENNReal.ofReal_mul hA2n]
  calc ∫⁻ ζ, ENNReal.ofReal |L ζ| ∂P
      ≤ ∫⁻ ζ, (ENNReal.ofReal A0 + (ENNReal.ofReal A1 * ENNReal.ofReal (E ζ) +
        ENNReal.ofReal A2 * ENNReal.ofReal (m ζ))) ∂P := lintegral_mono_ae hpt
    _ = ENNReal.ofReal A0 + (ENNReal.ofReal A1 * ∫⁻ ζ, ENNReal.ofReal (E ζ) ∂P +
        ENNReal.ofReal A2 * ∫⁻ ζ, ENNReal.ofReal (m ζ) ∂P) := by
        rw [lintegral_add_left measurable_const, lintegral_add_right _
          (hm.ennreal_ofReal.const_mul _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul _ hm.ennreal_ofReal]
        simp
    _ ≤ ENNReal.ofReal A0 + (ENNReal.ofReal A1 * ENNReal.ofReal 𝔈 +
        ENNReal.ofReal A2 * ENNReal.ofReal m₂) := by gcongr
    _ = ENNReal.ofReal (A0 + (A1 * 𝔈 + A2 * m₂)) := by
        rw [ENNReal.ofReal_add hA0n (by positivity), ENNReal.ofReal_add (by positivity)
          (by positivity), ENNReal.ofReal_mul hA1n, ENNReal.ofReal_mul hA2n]
    _ = _ := by
        congr 1
        simp only [hA0, hA1, hA2]
        rw [← hε2]
        field_simp
        ring


/-! ### Densities and second moments -/

section Density

variable {d : ℕ}

theorem rho_le_of_cbNorm {r : ℕ} {Λ w : ℝ} {ρ : Euc d → ℝ} (hmem : HRS.MemCb r ρ) (hw : 0 ≤ w)
    (hΛ : HRS.cbNorm r ρ + w ≤ Λ) : ∀ x, ρ x ≤ Λ := by
  intro x
  have h0 : ‖ρ x‖ ≤ ⨆ z : Euc d, ‖iteratedFDeriv ℝ 0 ρ z‖ := by
    refine le_ciSup (f := fun z : Euc d => ‖iteratedFDeriv ℝ 0 ρ z‖) (hmem.2 0 (Nat.zero_le _)) x
      |> le_trans (by simp)
  have h1 : (⨆ z : Euc d, ‖iteratedFDeriv ℝ 0 ρ z‖) ≤ HRS.cbNorm r ρ := by
    unfold HRS.cbNorm
    refine Finset.single_le_sum (f := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j ρ z‖)
      (fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.succ_pos r))
  have h2 : ρ x ≤ ‖ρ x‖ := le_abs_self _
  linarith

theorem measure_isProb {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ) :
    IsProbabilityMeasure (withDensityReal ρ) := by
  have hint : Integrable ρ volume := by
    by_contra h
    have := hρ.integral_one
    rw [integral_undef h] at this
    exact zero_ne_one this
  constructor
  unfold withDensityReal
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hρ.nonneg), hρ.integral_one]
  simp

theorem pair_withDensityReal {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ) (f : Euc d → ℝ) :
    pair (withDensityReal ρ) f = ∫ x, ρ x * f x := by
  unfold pair withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul₀]
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [ENNReal.toReal_ofReal (hρ.nonneg x)]
  · exact (hρ.measurable.ennreal_ofReal).aemeasurable
  · exact Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

/-- A probability density with finite second moment has a finite logarithmic moment
`∫ log(2+|x|) dρ < ∞` (`log(2+r) ≤ 1 + r ≤ 3/2 + r²/2`). -/
theorem log_integrable_withDensityReal {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ)
    (hint : Integrable (fun x => ‖x‖ ^ 2 * ρ x)) :
    Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) (withDensityReal ρ) := by
  have hρi : Integrable ρ volume := by
    by_contra h
    have := hρ.integral_one
    rw [integral_undef h] at this
    exact zero_ne_one this
  unfold withDensityReal
  rw [integrable_withDensity_iff_integrable_smul' hρ.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have hcont : Continuous fun x : Euc d => Real.log (2 + ‖x‖) :=
    (continuous_const.add continuous_norm).log (fun x => by show (2 + ‖x‖) ≠ 0; positivity)
  have hdom : Integrable (fun x : Euc d => (3 / 2 : ℝ) * ρ x + (1 / 2 : ℝ) * (‖x‖ ^ 2 * ρ x)) :=
    (hρi.const_mul _).add (hint.const_mul _)
  refine hdom.mono' ((hρ.measurable.ennreal_ofReal.ennreal_toReal.smul hcont.measurable).aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  have hx := hρ.nonneg x
  have hr := norm_nonneg x
  have hlog0 : 0 ≤ Real.log (2 + ‖x‖) := Real.log_nonneg (by linarith)
  rw [ENNReal.toReal_ofReal hx, smul_eq_mul, Real.norm_of_nonneg (mul_nonneg hx hlog0)]
  have h1 := Real.log_le_sub_one_of_pos (show 0 < 2 + ‖x‖ by positivity)
  nlinarith [mul_le_mul_of_nonneg_left h1 hx, mul_nonneg hx (sq_nonneg (‖x‖ - 1))]

theorem secondMoment_withDensity_pos (hd : 1 ≤ d) {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ)
    (hint : Integrable (fun x => ‖x‖ ^ 2 * ρ x)) :
    0 < HRS.Whole.AppendixA.secondMomentOf (withDensityReal ρ) := by
  unfold HRS.Whole.AppendixA.secondMomentOf
  rw [pair_withDensityReal hρ]
  have hnn : 0 ≤ᵐ[volume] fun x : Euc d => ρ x * ‖x‖ ^ 2 :=
    Eventually.of_forall fun x => mul_nonneg (hρ.nonneg x) (sq_nonneg _)
  have hint' : Integrable (fun x : Euc d => ρ x * ‖x‖ ^ 2) := by
    simpa [mul_comm] using hint
  refine lt_of_le_of_ne (integral_nonneg_of_ae hnn) fun h0 => ?_
  have h1 := (integral_eq_zero_iff_of_nonneg_ae hnn hint').mp h0.symm
  have : Nontrivial (Euc d) := by
    have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  have h2 : ∀ᵐ x : Euc d ∂volume, x ≠ 0 := by
    simp [ae_iff]
  have h3 : ∀ᵐ x : Euc d ∂volume, ρ x = 0 := by
    filter_upwards [h1, h2] with x hx hx0
    have hn : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx0)
    simpa [hn] using hx
  have := hρ.integral_one
  rw [integral_congr_ae h3] at this
  simp at this

theorem secondMomentOf_nonneg (μ : Measure (Euc d)) :
    0 ≤ HRS.Whole.AppendixA.secondMomentOf μ :=
  integral_nonneg fun _ => sq_nonneg _

theorem measurable_secondMoment_empirical {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (hN : 0 < N)
    {X : Ω → EucConfig d N} (hX : Measurable X) :
    Measurable fun ζ => HRS.Whole.AppendixA.secondMomentOf (empirical (X ζ)) := by
  unfold HRS.Whole.AppendixA.secondMomentOf
  simp_rw [pair_empirical hN]
  refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => ?_) _
  exact ((measurable_pi_apply i).comp hX).norm.pow_const 2

theorem selectedFlow_measurable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} {P : Measure Ω}
    {D : WholeDyn d} {T : ℝ} {X₀ : Ω → EucConfig d N} {W : NNReal → Ω → (Fin N → Euc d)}
    {X : NNReal → Ω → EucConfig d N}
    (h : HRS.Whole.AppendixA.SelectedFlowRd P D T X₀ W X) (t : NNReal) : Measurable (X t) := by
  rcases h.flow with ⟨h1, -⟩ | ⟨-, -, -, -, h1⟩ | ⟨-, -, -, -, h1⟩
  · exact h1.adapted t
  · exact h1.toContact.adapted t
  · exact h1.adapted t

end Density

end HRS.Whole.Q09A
