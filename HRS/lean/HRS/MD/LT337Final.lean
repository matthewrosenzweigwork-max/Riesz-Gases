import HRS.MD.LT337P4
import HRS.MD.LT337P5D
import HRS.MD.LT337P6
import HRS.MD.LT337P8

/-!
# Proposition 3.37 (`HRS.lowtemp_coulomb_bound`, `HRS.lowtemp_coulomb_threshold`): final assembly (sorry-free)

Assembly of the proved sub-lemmas `lt1`-`lt8` of the packet files `HRS/MD/LT337P*.lean` (`lt0` is the proved
`HRS.Commutator.commutator_estimate_super`, used in `LT337P6`), following the assembly theorems of `HRS/MD/LT337Spec.lean`
(M L3126-3153), with the sorry-free vocabulary `HRS.MD.LT337Vocab`.  The two frozen statements of
`HRS/Energy/Coercivity.lean` are reproved as `lowtemp_coulomb_bound_proof` and `lowtemp_coulomb_threshold_proof`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.MD.LT337Vocab HRS.MD.LT337P4 HRS.MD.LT337P5 HRS.MD.LT337P6 HRS.MD.LT337P8

namespace HRS.MD.LT337Final

variable {d N : ℕ}

theorem lowTempHyp_det {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {D : DynData d} {T Λ ΛV Mb : ℝ}
    {ρ : ℝ → Torus d → ℝ} {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} (h : LowTempHyp P D N T Λ ΛV Mb ρ X₀ W X) :
    LTDet D T Λ ΛV Mb ρ :=
  ⟨h.coulomb, h.sym_nonpos, h.M_bound, h.V_reg, h.mf, h.mf_reg, h.Λ_ge⟩

/-- `o_N(Λ) ≥ 0` for `s = d - 2 ≥ 0`, `Λ ≥ 1`, `N ≥ 1`, `C₀ ≥ 0`. -/
theorem lt9_oN_nonneg (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ) {N : ℕ} (hN : 1 ≤ N) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    0 ≤ oNΛ d ((d : ℝ) - 2) C₀ Λ N := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hΛpos : 0 < Λ := by linarith
  have hNΛ1 : (1 : ℝ) ≤ (N : ℝ) * Λ := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  unfold oNΛ
  have h1 : 0 ≤ (if ((d : ℝ) - 2) = 0 then Real.log (N * Λ) / (2 * d * N) else 0) := by
    split_ifs
    · exact div_nonneg (Real.log_nonneg hNΛ1) (by positivity)
    · exact le_rfl
  have h2 : 0 ≤ C₀ * Λ ^ (((d : ℝ) - 2) / d) * (N : ℝ) ^ (((d : ℝ) - 2) / d - 1) := by
    have := Real.rpow_nonneg hΛpos.le (((d : ℝ) - 2) / d)
    have := Real.rpow_nonneg hNpos.le (((d : ℝ) - 2) / d - 1)
    positivity
  linarith

/-- Threshold arithmetic (M L3152-3153): for `s = d - 2`, `Λ ≥ 1`, `C₀ > 0`:
`(δ (NΛ)^{2/d})⁻¹ ≤ (δ C₀)⁻¹ o_N(Λ)`.  PROVED here (it is elementary). -/
theorem lt9_inv_le_oN (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ) {N : ℕ} (hN : 1 ≤ N) {δ C₀ : ℝ} (hδ : 0 < δ)
    (hC₀ : 0 < C₀) :
    (δ * ((N : ℝ) * Λ) ^ (2 / (d : ℝ)))⁻¹ ≤ (δ * C₀)⁻¹ * oNΛ d ((d : ℝ) - 2) C₀ Λ N := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hΛpos : 0 < Λ := by linarith
  have hNΛ1 : (1 : ℝ) ≤ (N : ℝ) * Λ := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  set x : ℝ := 2 / (d : ℝ) with hx
  have hx0 : 0 ≤ x := by positivity
  have hsd : ((d : ℝ) - 2) / d = 1 - x := by rw [hx]; field_simp
  have hlog : 0 ≤ (if ((d : ℝ) - 2) = 0 then Real.log (N * Λ) / (2 * d * N) else 0) := by
    split_ifs
    · exact div_nonneg (Real.log_nonneg hNΛ1) (by positivity)
    · exact le_rfl
  unfold oNΛ
  rw [hsd]
  have h1 : (1 - x) - 1 = -x := by ring
  rw [h1]
  have hL : (δ * ((N : ℝ) * Λ) ^ x)⁻¹ = δ⁻¹ * ((N : ℝ) ^ (-x) * Λ ^ (-x)) := by
    rw [mul_inv, Real.mul_rpow hNpos.le hΛpos.le, mul_inv, Real.rpow_neg hNpos.le, Real.rpow_neg hΛpos.le]
  have hR : C₀ * Λ ^ (1 - x) * (N : ℝ) ^ (-x) ≥ C₀ * Λ ^ (-x) * (N : ℝ) ^ (-x) := by
    have : Λ ^ (-x) ≤ Λ ^ (1 - x) := Real.rpow_le_rpow_of_exponent_le hΛ (by linarith)
    have hN' : 0 ≤ (N : ℝ) ^ (-x) := Real.rpow_nonneg hNpos.le _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this hC₀.le) hN'
  have hK : 0 ≤ (δ * C₀)⁻¹ := by positivity
  rw [hL]
  calc δ⁻¹ * ((N : ℝ) ^ (-x) * Λ ^ (-x))
      = (δ * C₀)⁻¹ * (C₀ * Λ ^ (-x) * (N : ℝ) ^ (-x)) := by
        field_simp
    _ ≤ (δ * C₀)⁻¹ * (C₀ * Λ ^ (1 - x) * (N : ℝ) ^ (-x)) := mul_le_mul_of_nonneg_left hR hK
    _ ≤ (δ * C₀)⁻¹ * ((if ((d : ℝ) - 2) = 0 then Real.log (N * Λ) / (2 * d * N) else 0) +
          C₀ * Λ ^ (1 - x) * (N : ℝ) ^ (-x)) := mul_le_mul_of_nonneg_left (by linarith) hK

/-- The bound with `C₀` allowed to be any number `≥ C₀min` (needed for the threshold, where `C₀ > 0` is forced);
also records `E[(F_N + o_N)(X_0, μ_0)] ≥ 0`.  PROVED from LT4, LT5, LT6, LT8 (this is the assembly of the TeX proof
M L3126-3153). -/
theorem lowtemp_coulomb_bound_mono (hd : 2 ≤ d) (T Λ ΛV Mb : ℝ) (hT : 0 ≤ T) :
    ∃ C₀min C : ℝ, 0 ≤ C₀min ∧ 0 < C ∧ ∀ C₀ : ℝ, C₀min ≤ C₀ →
      ∀ (D : DynData d) (N : ℕ), 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ρ : ℝ → Torus d → ℝ) (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
        (X : ℝ≥0 → Ω → Config d N),
        LowTempHyp P D N T Λ ΛV Mb ρ X₀ W X →
        Integrable (fun ω => correctedEnergy D C₀ Λ ρ (X 0 ω) 0) P →
        0 ≤ ∫ ω, correctedEnergy D C₀ Λ ρ (X 0 ω) 0 ∂P ∧
        ∀ t ∈ Set.Icc 0 T,
          ∫⁻ ω, ENNReal.ofReal (correctedEnergy D C₀ Λ ρ (X (Real.toNNReal t) ω) t) ∂P ≤
            ENNReal.ofReal (C * (∫ ω, correctedEnergy D C₀ Λ ρ (X 0 ω) 0 ∂P + D.invβ)) := by
  obtain ⟨C₀min, κ, κ', hC₀min, hκ, hκ', h6⟩ := lt6_drift_bound_proof hd T Λ ΛV Mb
  obtain ⟨C, hC, h8⟩ := lt8_gronwall_fatou_proof (d := d) T κ κ' hT hκ hκ'
  refine ⟨C₀min, C, hC₀min, hC, fun C₀ hC₀ D N hN Ω _ P _ ρ X₀ W X h hint => ?_⟩
  have hcol : ∀ᵐ ω ∂P, ∀ s ∈ Set.Icc (0 : ℝ) T, X (Real.toNNReal s) ω ∉ collisionSet d N := by
    filter_upwards [h.sol.no_collision] with ω hω s hs
    exact hω _ (by rw [Real.coe_toNNReal _ hs.1]; exact hs.2)
  have hpath : ∀ᵐ ω ∂P, ∀ s ∈ Set.Icc (0 : ℝ) T,
      0 ≤ correctedEnergy D C₀ Λ ρ (X (Real.toNNReal s) ω) s ∧
      ltDrift D ρ s (X (Real.toNNReal s) ω) ≤
        κ * correctedEnergy D C₀ Λ ρ (X (Real.toNNReal s) ω) s + κ' * D.invβ := by
    filter_upwards [hcol] with ω hω s hs
    exact h6 C₀ hC₀ D N hN ρ (lowTempHyp_det h) s hs _ (hω s hs)
  have hnn : 0 ≤ ∫ ω, correctedEnergy D C₀ Λ ρ (X 0 ω) 0 ∂P := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hpath] with ω hω
    have := (hω 0 ⟨le_rfl, hT⟩).1
    simpa using this
  refine ⟨hnn, fun t ht => ?_⟩
  obtain ⟨ℱ, W', hF⟩ := h.filtered
  obtain ⟨τ, hτ⟩ := lt4_stopping_proof hd h hF
  have hid := lt5_stopped_identity_proof hd hN hT h hF hτ C₀ hint
  exact h8 P D N Λ C₀ ρ X ℱ τ hτ hid hpath hint t ht

/-- ASSEMBLY of the frozen statement `HRS.lowtemp_coulomb_bound` (Proposition 3.37, `B:eq:lowtemp-bound`). -/
theorem lowtemp_coulomb_bound_proof_aux (hd : 2 ≤ d) (T Λ ΛV Mb : ℝ) (hT : 0 ≤ T) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (D : DynData d) (N : ℕ), 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ρ : ℝ → Torus d → ℝ) (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
        (X : ℝ≥0 → Ω → Config d N),
        LowTempHyp P D N T Λ ΛV Mb ρ X₀ W X →
        Integrable (fun ω => correctedEnergy D C₀ Λ ρ (X 0 ω) 0) P →
        ∀ t ∈ Set.Icc 0 T,
          ∫⁻ ω, ENNReal.ofReal (correctedEnergy D C₀ Λ ρ (X (Real.toNNReal t) ω) t) ∂P ≤
            ENNReal.ofReal (C * (∫ ω, correctedEnergy D C₀ Λ ρ (X 0 ω) 0 ∂P + D.invβ)) := by
  obtain ⟨C₀min, C, h0, hC, hm⟩ := lowtemp_coulomb_bound_mono hd T Λ ΛV Mb hT
  exact ⟨C₀min, C, h0, hC, fun D N hN Ω _ P _ ρ X₀ W X h hint t ht =>
    (hm C₀min le_rfl D N hN P ρ X₀ W X h hint).2 t ht⟩

/-- ASSEMBLY of the frozen statement `HRS.lowtemp_coulomb_threshold` (Proposition 3.37 consequence = 3.36 (C3)). -/
theorem lowtemp_coulomb_threshold_proof_aux (hd : 2 ≤ d) (T Λ ΛV Mb δ : ℝ) (hT : 0 ≤ T) (hδ : 0 < δ) :
    ∃ C₀ Cδ : ℝ, 0 ≤ C₀ ∧ 0 < Cδ ∧
      ∀ (D : DynData d) (N : ℕ), 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ρ : ℝ → Torus d → ℝ) (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
        (X : ℝ≥0 → Ω → Config d N),
        LowTempHyp P D N T Λ ΛV Mb ρ X₀ W X →
        Integrable (fun ω => correctedEnergy D C₀ Λ ρ (X 0 ω) 0) P →
        D.invβ ≤ (δ * (N * Λ) ^ (2 / (d : ℝ)))⁻¹ →
        ∀ t ∈ Set.Icc 0 T,
          ∫⁻ ω, ENNReal.ofReal (correctedEnergy D C₀ Λ ρ (X (Real.toNNReal t) ω) t) ∂P ≤
            ENNReal.ofReal (Cδ * (∫ ω, correctedEnergy D C₀ Λ ρ (X 0 ω) 0 ∂P +
              oNΛ d D.s C₀ Λ N)) := by
  obtain ⟨C₀min, C, h0, hC, hm⟩ := lowtemp_coulomb_bound_mono hd T Λ ΛV Mb hT
  set C₀ : ℝ := max C₀min 1 with hC₀def
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hC₀min : C₀min ≤ C₀ := le_max_left _ _
  set K : ℝ := (δ * C₀)⁻¹ with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨C₀, C * max 1 K, hC₀pos.le, by positivity, fun D N hN Ω _ P _ ρ X₀ W X h hint hβ t ht => ?_⟩
  obtain ⟨hnn, hb⟩ := hm C₀ hC₀min D N hN P ρ X₀ W X h hint
  refine (hb t ht).trans (ENNReal.ofReal_le_ofReal ?_)
  have hΛ : 1 ≤ Λ := h.Λ_ge
  have hs : D.s = (d : ℝ) - 2 := h.coulomb
  have hβK : D.invβ ≤ K * oNΛ d D.s C₀ Λ N := by
    have := lt9_inv_le_oN hd hΛ (by omega : 1 ≤ N) hδ hC₀pos
    rw [hs]
    exact hβ.trans this
  have ho : 0 ≤ oNΛ d D.s C₀ Λ N := by
    rw [hs]; exact lt9_oN_nonneg hd hΛ (by omega : 1 ≤ N) hC₀pos.le
  have hm1 : (1 : ℝ) ≤ max 1 K := le_max_left _ _
  have hmK : K ≤ max 1 K := le_max_right _ _
  have hCo : 0 < C := hC
  have h1 : ∫ ω, correctedEnergy D C₀ Λ ρ (X 0 ω) 0 ∂P + D.invβ ≤
      max 1 K * (∫ ω, correctedEnergy D C₀ Λ ρ (X 0 ω) 0 ∂P + oNΛ d D.s C₀ Λ N) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hm1) hnn, mul_nonneg (sub_nonneg.2 hmK) ho]
  calc C * (∫ ω, correctedEnergy D C₀ Λ ρ (X 0 ω) 0 ∂P + D.invβ)
      ≤ C * (max 1 K * (∫ ω, correctedEnergy D C₀ Λ ρ (X 0 ω) 0 ∂P + oNΛ d D.s C₀ Λ N)) :=
        mul_le_mul_of_nonneg_left h1 hCo.le
    _ = C * max 1 K * (∫ ω, correctedEnergy D C₀ Λ ρ (X 0 ω) 0 ∂P + oNΛ d D.s C₀ Λ N) := by ring


theorem lowtemp_coulomb_bound_proof : type_of% @HRS.lowtemp_coulomb_bound :=
  @lowtemp_coulomb_bound_proof_aux

theorem lowtemp_coulomb_threshold_proof : type_of% @HRS.lowtemp_coulomb_threshold :=
  @lowtemp_coulomb_threshold_proof_aux

example := (@lowtemp_coulomb_bound_proof : type_of% @HRS.lowtemp_coulomb_bound)
example := (@lowtemp_coulomb_threshold_proof : type_of% @HRS.lowtemp_coulomb_threshold)

end HRS.MD.LT337Final
end
