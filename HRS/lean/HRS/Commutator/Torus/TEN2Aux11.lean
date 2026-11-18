import HRS.Commutator.Torus.TEN2Aux10

/-!
# Torus energy layer (packet T-EN2), helper part 11: the energy identity for every `η > 0` and
`energy_control_T`

Prefix `ten2_`.  `ten2_energy_identity` is `energy_identity_T`, `ten2_energy_control` is `energy_control_T`
(both are used verbatim in `Layer.lean`; the identity is needed here, so it lives in this file).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.TorusNote

open HRS

variable {d N : ℕ} {s η : ℝ}

/-- The energy identity `(2.energyidentity)` on the torus (exact, any `η > 0`). -/
theorem ten2_energy_identity (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (η : ℝ) (hη : 0 < η)
    (ρ : Torus d → ℝ) (hρ : BddDensityT ρ) {N : ℕ} (hN : 1 ≤ N) (X : Config d N)
    (hX : X ∉ collisionSet d N) :
    kerEnergyT (gTorus s η) (chargeT X ρ) +
        (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, fTorus s η (X i - X j) +
        ∫ x, ∫ y, fTorus s η (x - y) * ρ x * ρ y =
      2 * modEnergyT s X ρ + gTorus0 d s η / (N : ℝ) +
        (2 / (N : ℝ)) * ∑ i, ∫ y, fTorus s η (X i - y) * ρ y := by
  obtain ⟨-, hcoef, hsumm, hlift⟩ := tpos_coef_formula hd hs0 hsd η hη
  have hG : Continuous (gTorus s η) := HRS.Torus.continuous_of_continuous_lift hlift
  have hR : Integrable (periodicRiesz d s) :=
    HRS.KernelAux.integrable_periodicRiesz (by omega) hs0 (by linarith)
  have hf : Integrable (fTorus s η) := ten_fTorus_integrable hR hG (by omega)
  have key := ten_identity_abstract (d := d) (by omega) (G := gTorus s η)
    (R := periodicRiesz d s) (f := fTorus s η) (g0 := gTorus0 d s η) hG
    (fun z => ten_gTorus_neg s η z) hR hf
    (fun x hx => by simp [gTorus, hx]) (by simp [gTorus]) hN X hX ρ hρ
  unfold modEnergyT
  exact key

/-- Pure arithmetic of `(a)` and `(b)` of `energy_control_T`. -/
theorem ten2_arith (F Lg A Bq M K Cx Cg Cp g0N nu SN I cr : ℝ)
    (hid : nu + SN + I = 2 * F + g0N + cr) (hnu : 0 ≤ nu) (hI : 0 ≤ I) (hS : -M ≤ SN)
    (hcr : cr ≤ 2 * (Cx * Bq)) (hg0 : g0N + Lg ≤ Cg * A) (hMB : M ≤ K * Bq) (hA : 0 ≤ A)
    (hB : 0 ≤ Bq) (hK : 0 ≤ K) (hCx : 0 ≤ Cx) (hCg : 0 ≤ Cg) (hCp : K + Cg + 2 * Cx + 1 ≤ Cp) :
    A + Bq ≤ F - Lg / 2 + Cp * (A + Bq) ∧
      nu + SN + I ≤ 2 * (F - Lg / 2 + Cp * (A + Bq)) := by
  have t1 : 0 ≤ (Cp - Cg - 1) * A := mul_nonneg (by linarith) hA
  have t2 : 0 ≤ (Cp - K - Cx - 1) * Bq := mul_nonneg (by linarith) hB
  have t3 : 0 ≤ Cg * A := mul_nonneg hCg hA
  have t4 : 0 ≤ Cx * Bq := mul_nonneg hCx hB
  have t5 : 0 ≤ K * Bq := mul_nonneg hK hB
  constructor
  · nlinarith [t1, t2, t3, t4, t5]
  · nlinarith [t1, t2, t3, t4, t5]

/-- Lower bound of the particle sum: `N⁻² ∑_{i≠j} f_η(X_i - X_j) ≥ -K η^{d-s}`. -/
theorem ten2_S_lower (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η)
    {N : ℕ} (hN : 1 ≤ N) (X : Config d N) :
    -(ten2K d s * η ^ ((d : ℝ) - s)) ≤
      (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, fTorus s η (X i - X j) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hM0 : 0 ≤ ten2K d s * η ^ ((d : ℝ) - s) :=
    mul_nonneg (ten2K_nonneg hd hs0 hsd) (Real.rpow_nonneg hη.le _)
  set M := ten2K d s * η ^ ((d : ℝ) - s) with hM
  set S : ℝ := ∑ i, ∑ j ∈ Finset.univ.erase i, fTorus s η (X i - X j) with hSdef
  have hSlow : -(M * ((N : ℝ) * (N - 1))) ≤ S := by
    have h1 : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, (-M) ≤
        ∑ j ∈ Finset.univ.erase i, fTorus s η (X i - X j) :=
      fun i => Finset.sum_le_sum fun j _ => ten2_fTorus_lower hd hs0 hsd hη _
    have h2 : ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, (-M) ≤ S :=
      Finset.sum_le_sum fun i _ => h1 i
    have h3 : ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, (-M) = -(M * ((N : ℝ) * (N - 1))) := by
      simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      have : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub hN]; simp
      rw [this]
      simp
      ring
    linarith
  have hN1 : (N : ℝ) * (N - 1) ≤ (N : ℝ) ^ 2 := by nlinarith
  have h4 : -(M * (N : ℝ) ^ 2) ≤ S := by
    have := mul_le_mul_of_nonneg_left hN1 hM0
    linarith
  have h5 : (1 / (N : ℝ) ^ 2) * (-(M * (N : ℝ) ^ 2)) ≤ (1 / (N : ℝ) ^ 2) * S :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  have h6 : (1 / (N : ℝ) ^ 2) * (-(M * (N : ℝ) ^ 2)) = -M := by field_simp
  linarith

/-- The diagonal value: `g_η^𝕋(0)/N + 1_{s=0} log η/N ≤ C_g η^{-s}/N`. -/
theorem ten2_g0_bound (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ Cg : ℝ, 0 < Cg ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ N : ℕ, 1 ≤ N →
      gTorus0 d s η / (N : ℝ) + (if s = 0 then Real.log η / (N : ℝ) else 0) ≤
        Cg * (η ^ (-s) / (N : ℝ)) := by
  obtain ⟨Cg, hCg0, hCg⟩ := tpos_g_zero hd hs0 hsd
  refine ⟨Cg, hCg0, fun η hη hη1 N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  obtain ⟨hg1, hg2⟩ := hCg η hη hη1
  by_cases hs : s = 0
  · have h := hg2 hs
    have h' : gTorus0 d s η + Real.log η ≤ Cg := (le_abs_self _).trans h
    have hη0 : η ^ (-s) = 1 := by rw [hs]; simp
    rw [if_pos hs, ← add_div, hη0, ← mul_div_assoc, mul_one]
    exact div_le_div_of_nonneg_right h' hN0.le
  · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    have h := hg1 hspos
    have h' : gTorus0 d s η ≤ Cg * η ^ (-s) := (le_abs_self _).trans h
    rw [if_neg hs, add_zero, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right h' hN0.le

/-- `(d)` occupancy, from the energy inequality. -/
theorem ten2_occ_core (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {cf η₁ : ℝ} (hcf0 : 0 < cf)
    (hcf : ∀ η : ℝ, 0 < η → η ≤ η₁ → ∀ x : Torus d, x ≠ 0 →
      KernelGrad.tdist x 0 ≤ 2 * η * Real.sqrt d → cf * η ^ (-s) ≤ fTorus s η x)
    (hη : 0 < η) (hη1 : η ≤ 1) (hηη₁ : η ≤ η₁) {N : ℕ} (hN : 1 ≤ N) (X : Config d N)
    (hX : X ∉ collisionSet d N) {Q : ℝ}
    (hAQ : η ^ (-s) / (N : ℝ) ≤ Q)
    (hSQ : (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, fTorus s η (X i - X j) ≤ 2 * Q)
    (hMQ : ten2K d s * η ^ ((d : ℝ) - s) ≤ ten2K d s * Q) :
    ∑ j : Fin d → Fin (nCells η), occT η X j ^ 2 ≤ (1 + (2 + ten2K d s) / cf) * η ^ s * Q := by
  have hK := ten2K_nonneg hd hs0 hsd
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hocc := ten2_occ_count (d := d) hη hη1 hN X
  have hsη : 0 < η ^ s := Real.rpow_pos_of_pos hη _
  have hηsη : η ^ s * η ^ (-s) = 1 := by
    rw [← Real.rpow_add hη]; simp
  have hM0 : 0 ≤ ten2K d s * η ^ ((d : ℝ) - s) :=
    mul_nonneg hK (Real.rpow_nonneg hη.le _)
  set M := ten2K d s * η ^ ((d : ℝ) - s) with hM
  set S : ℝ := ∑ i, ∑ j ∈ Finset.univ.erase i, fTorus s η (X i - X j) with hSdef
  have hW : ∀ i : Fin N, ∀ i' ∈ Finset.univ.erase i,
      (if KernelGrad.tdist (X i - X i') 0 ≤ 2 * η * Real.sqrt d then (1 : ℝ) else 0) ≤
        (η ^ s / cf) * (fTorus s η (X i - X i') + M) := by
    intro i i' hi'
    have hne : i' ≠ i := Finset.ne_of_mem_erase hi'
    have hXne : X i - X i' ≠ 0 := sub_ne_zero.2 (fun h => hX ⟨i, i', Ne.symm hne, h⟩)
    have hlow := ten2_fTorus_lower hd hs0 hsd hη (X i - X i')
    have hpos : 0 ≤ η ^ s / cf := by positivity
    by_cases hnear : KernelGrad.tdist (X i - X i') 0 ≤ 2 * η * Real.sqrt d
    · rw [if_pos hnear]
      have h1 := hcf η hη hηη₁ (X i - X i') hXne hnear
      have h2 : (η ^ s / cf) * (cf * η ^ (-s)) = 1 := by
        have : (η ^ s / cf) * (cf * η ^ (-s)) = η ^ s * η ^ (-s) := by field_simp
        rw [this, hηsη]
      calc (1 : ℝ) = (η ^ s / cf) * (cf * η ^ (-s)) := h2.symm
        _ ≤ (η ^ s / cf) * (fTorus s η (X i - X i')) := mul_le_mul_of_nonneg_left h1 hpos
        _ ≤ (η ^ s / cf) * (fTorus s η (X i - X i') + M) :=
            mul_le_mul_of_nonneg_left (by linarith) hpos
    · rw [if_neg hnear]
      exact mul_nonneg hpos (by linarith)
  have hsumW : ∑ i, ∑ i' ∈ Finset.univ.erase i,
      (if KernelGrad.tdist (X i - X i') 0 ≤ 2 * η * Real.sqrt d then (1 : ℝ) else 0) ≤
      (η ^ s / cf) * (S + M * (N : ℝ) ^ 2) := by
    have h1 : ∀ i : Fin N, ∑ i' ∈ Finset.univ.erase i,
        (if KernelGrad.tdist (X i - X i') 0 ≤ 2 * η * Real.sqrt d then (1 : ℝ) else 0) ≤
        ∑ i' ∈ Finset.univ.erase i, (η ^ s / cf) * (fTorus s η (X i - X i') + M) :=
      fun i => Finset.sum_le_sum fun i' hi' => hW i i' hi'
    refine (Finset.sum_le_sum fun i _ => h1 i).trans ?_
    have e1 : ∀ i : Fin N, ∑ i' ∈ Finset.univ.erase i, (η ^ s / cf) * (fTorus s η (X i - X i') + M) =
        (η ^ s / cf) * (∑ i' ∈ Finset.univ.erase i, fTorus s η (X i - X i') + ((N : ℝ) - 1) * M) := by
      intro i
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_sub hN, Nat.cast_one]
    have h2 : ∑ i : Fin N, ∑ i' ∈ Finset.univ.erase i, (η ^ s / cf) * (fTorus s η (X i - X i') + M) =
        (η ^ s / cf) * (S + M * ((N : ℝ) * (N - 1))) := by
      calc ∑ i : Fin N, ∑ i' ∈ Finset.univ.erase i, (η ^ s / cf) * (fTorus s η (X i - X i') + M)
          = ∑ i : Fin N, (η ^ s / cf) * (∑ i' ∈ Finset.univ.erase i, fTorus s η (X i - X i') +
              ((N : ℝ) - 1) * M) := Finset.sum_congr rfl fun i _ => e1 i
        _ = (η ^ s / cf) * ∑ i : Fin N, (∑ i' ∈ Finset.univ.erase i, fTorus s η (X i - X i') +
              ((N : ℝ) - 1) * M) := by rw [Finset.mul_sum]
        _ = (η ^ s / cf) * (S + M * ((N : ℝ) * (N - 1))) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul]
            ring
    rw [h2]
    have hN1 : (N : ℝ) * (N - 1) ≤ (N : ℝ) ^ 2 := by nlinarith
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := mul_le_mul_of_nonneg_left hN1 hM0
    linarith
  have hinvN : 1 / (N : ℝ) = η ^ s * (η ^ (-s) / (N : ℝ)) := by
    rw [← mul_div_assoc, hηsη]
  have h1 : (1 / (N : ℝ) ^ 2) * ∑ i, ∑ i' ∈ Finset.univ.erase i,
      (if KernelGrad.tdist (X i - X i') 0 ≤ 2 * η * Real.sqrt d then (1 : ℝ) else 0) ≤
      (η ^ s / cf) * ((1 / (N : ℝ) ^ 2) * S + M) := by
    calc _ ≤ (1 / (N : ℝ) ^ 2) * ((η ^ s / cf) * (S + M * (N : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hsumW (by positivity)
      _ = (η ^ s / cf) * ((1 / (N : ℝ) ^ 2) * S + M) := by field_simp
  have h2 : (η ^ s / cf) * ((1 / (N : ℝ) ^ 2) * S + M) ≤ (η ^ s / cf) * ((2 + ten2K d s) * Q) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith
  have h3 : 1 / (N : ℝ) ≤ η ^ s * Q := by
    rw [hinvN]
    exact mul_le_mul_of_nonneg_left hAQ hsη.le
  calc ∑ j : Fin d → Fin (nCells η), occT η X j ^ 2
      ≤ 1 / (N : ℝ) + (1 / (N : ℝ) ^ 2) * ∑ i, ∑ i' ∈ Finset.univ.erase i,
        (if KernelGrad.tdist (X i - X i') 0 ≤ 2 * η * Real.sqrt d then (1 : ℝ) else 0) := hocc
    _ ≤ η ^ s * Q + (η ^ s / cf) * ((2 + ten2K d s) * Q) := add_le_add h3 (h1.trans h2)
    _ = (1 + (2 + ten2K d s) / cf) * η ^ s * Q := by field_simp

theorem ten2_energy_control (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ Cb η₀ : ℝ, 0 < Cb ∧ 0 < η₀ ∧ η₀ ≤ 1 ∧ ∀ p : ℝ≥0∞,
      ENNReal.ofReal ((d : ℝ) / (d - s)) < p →
      ∃ Cp0 : ℝ, 0 < Cp0 ∧ ∀ Cp : ℝ, Cp0 ≤ Cp → ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ ρ : Torus d → ℝ, BddDensityT ρ →
      ∀ (N : ℕ) (X : Config d N), 1 ≤ N → X ∉ collisionSet d N →
        η ^ (-s) / (N : ℝ) + normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) ≤
            scaleQT s Cp p η X ρ ∧
        kerEnergyT (gTorus s η) (chargeT X ρ) +
            (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, fTorus s η (X i - X j) +
            ∫ x, ∫ y, fTorus s η (x - y) * ρ x * ρ y ≤ 2 * scaleQT s Cp p η X ρ ∧
        ENNReal.ofReal (η ^ (-s)) * sobSqT η (-Whole.alphaE d s) (fun k => Torus.fcoef ρ k) ≤
          ENNReal.ofReal (Cb * scaleQT s Cp p η X ρ) ∧
        ∑ j : Fin d → Fin (nCells η), occT η X j ^ 2 ≤ Cb * η ^ s * scaleQT s Cp p η X ρ := by
  obtain ⟨η₁, cf, hη₁0, hη₁1, hcf0, hcf⟩ := tpos_f_lower_near hd hs0 hsd
  obtain ⟨cb, hcb0, hcb⟩ := tpos_coef_bounds hd hs0 hsd
  obtain ⟨Cg, hCg0, hCg⟩ := ten2_g0_bound hd hs0 hsd
  have hK := ten2K_nonneg hd hs0 hsd
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hds : 0 < (d : ℝ) - s := by linarith
  refine ⟨1 + cb⁻¹ * (2 + ten2K d s) + (2 + ten2K d s) / cf, η₁, by positivity, hη₁0, hη₁1,
    fun p hp => ?_⟩
  -- the conjugate exponent
  have hρ1 : 1 ≤ (d : ℝ) / (d - s) := by rw [le_div_iff₀ hds]; linarith
  have hp1 : 1 < p := lt_of_le_of_lt (by simpa using ENNReal.ofReal_le_ofReal hρ1) hp
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp1).ne'
  have hpinv_le : p⁻¹ ≤ 1 := (ENNReal.inv_lt_one.2 hp1).le
  obtain ⟨q, hpq⟩ : ∃ q : ℝ≥0∞, p⁻¹ + q⁻¹ = 1 :=
    ⟨(1 - p⁻¹)⁻¹, by rw [inv_inv, add_tsub_cancel_of_le hpinv_le]⟩
  obtain ⟨hq0, hqt, hq1, hQ1⟩ := ten2_conj_facts hd hs0 hsd hp hpq
  obtain ⟨Cx, hCx0, hCx⟩ := ten2_cross_bound hd hs0 hsd hp hpq
  have hpinvT : (p⁻¹).toReal + (q.toReal)⁻¹ = 1 := by
    have := congrArg ENNReal.toReal hpq
    rwa [ENNReal.toReal_add (ENNReal.inv_ne_top.2 hp0) (ENNReal.inv_ne_top.2 hq0), ENNReal.toReal_one,
      ENNReal.toReal_inv q] at this
  have hexp : (d : ℝ) / q.toReal = (d : ℝ) * (1 - (p⁻¹).toReal) := by
    rw [div_eq_mul_inv]; congr 1; linarith
  have hpinv0 : 0 ≤ (p⁻¹).toReal := ENNReal.toReal_nonneg
  refine ⟨ten2K d s + Cg + 2 * Cx + 1, by positivity, fun Cp hCp η hη hηη₁ ρ hρ N X hN hX => ?_⟩
  have hη1 : η ≤ 1 := hηη₁.trans hη₁1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hnp1 : 1 ≤ normT p ρ := ten2_normT_ge_one hp1.le hρ
  have hηe : 0 < η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) := Real.rpow_pos_of_pos hη _
  have hηs : 0 < η ^ (-s) := Real.rpow_pos_of_pos hη _
  have hA0 : 0 ≤ η ^ (-s) / (N : ℝ) := by positivity
  have hB0 : 0 ≤ normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) := by positivity
  have hM0 : 0 ≤ ten2K d s * η ^ ((d : ℝ) - s) := mul_nonneg hK (Real.rpow_nonneg hη.le _)
  have hdB : η ^ ((d : ℝ) - s) ≤ normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) := by
    have h1 : η ^ ((d : ℝ) - s) ≤ η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) :=
      Real.rpow_le_rpow_of_exponent_ge hη hη1 (by nlinarith)
    calc η ^ ((d : ℝ) - s) ≤ η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) := h1
      _ = 1 * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hnp1 hηe.le
  have hMB : ten2K d s * η ^ ((d : ℝ) - s) ≤
      ten2K d s * (normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s)) :=
    mul_le_mul_of_nonneg_left hdB hK
  -- the energy identity and the signs of its terms
  have hid := ten2_energy_identity hd hs0 hsd η hη ρ hρ hN X hX
  have hν := ten2_kerEnergy_nonneg hd hs0 hsd hη hN X hρ
  have hcb' : ∀ k : Lattice d, k ≠ 0 → cb * η ^ ((d : ℝ) - s) *
      (1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (-(Whole.alphaE d s)) ≤
        tScale s * fHatEta d s η (Lattice.toEuc k) := fun k hk => (hcb η hη hη1 k hk).2.2
  have hI := ten2_quad_nonneg hd hs0 hsd hcb' hcb0 hη hρ
  have hS' := ten2_S_lower hd hs0 hsd hη hN X
  have hcrossi : ∀ i : Fin N, ∫ y, fTorus s η (X i - y) * ρ y ≤
      Cx * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) * normT p ρ := by
    intro i
    have := hCx η hη hη1 ρ hρ (X i)
    rw [hexp] at this
    exact this
  have hcross : (2 / (N : ℝ)) * ∑ i, ∫ y, fTorus s η (X i - y) * ρ y ≤
      2 * (Cx * (normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s))) := by
    have h1 : ∑ i, ∫ y, fTorus s η (X i - y) * ρ y ≤
        (N : ℝ) * (Cx * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) * normT p ρ) := by
      calc ∑ i, ∫ y, fTorus s η (X i - y) * ρ y ≤
            ∑ _i : Fin N, (Cx * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) * normT p ρ) :=
            Finset.sum_le_sum fun i _ => hcrossi i
        _ = (N : ℝ) * (Cx * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) * normT p ρ) := by simp
    have h2 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 2 / (N : ℝ) by positivity)
    have h3 : (2 / (N : ℝ)) * ((N : ℝ) * (Cx * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) * normT p ρ)) =
        2 * (Cx * (normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s))) := by
      field_simp
    linarith
  have hg0 := hCg η hη hη1 N hN
  -- the scale function
  have hQdef : scaleQT s Cp p η X ρ = modEnergyT s X ρ -
      (if s = 0 then Real.log η / (N : ℝ) else 0) / 2 +
      Cp * (η ^ (-s) / (N : ℝ) + normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s)) := by
    unfold scaleQT
    have : (if s = 0 then Real.log η / (2 * (N : ℝ)) else 0) =
        (if s = 0 then Real.log η / (N : ℝ) else 0) / 2 := by
      by_cases hs : s = 0
      · simp only [hs, if_true]; field_simp
      · simp [hs]
    rw [this]
  have hcl := ten2_arith (modEnergyT s X ρ) (if s = 0 then Real.log η / (N : ℝ) else 0)
    (η ^ (-s) / (N : ℝ)) (normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s))
    (ten2K d s * η ^ ((d : ℝ) - s)) (ten2K d s) Cx Cg Cp (gTorus0 d s η / (N : ℝ))
    (kerEnergyT (gTorus s η) (chargeT X ρ))
    ((1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, fTorus s η (X i - X j))
    (∫ x, ∫ y, fTorus s η (x - y) * ρ x * ρ y)
    ((2 / (N : ℝ)) * ∑ i, ∫ y, fTorus s η (X i - y) * ρ y)
    (by linarith [hid]) hν hI hS' hcross hg0 hMB hA0 hB0 hK hCx0 hCg0.le (by linarith)
  obtain ⟨hQ1, hQ2⟩ := hcl
  rw [← hQdef] at hQ1 hQ2
  have hQnn : 0 ≤ scaleQT s Cp p η X ρ := by linarith
  have hBQ : normT p ρ * η ^ ((d : ℝ) * (1 - (p⁻¹).toReal) - s) ≤ scaleQT s Cp p η X ρ := by linarith
  have hIle : (∫ x, ∫ y, fTorus s η (x - y) * ρ x * ρ y) ≤
      2 * scaleQT s Cp p η X ρ + ten2K d s * η ^ ((d : ℝ) - s) := by linarith
  have hSQ : (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, fTorus s η (X i - X j) ≤
      2 * scaleQT s Cp p η X ρ := by linarith
  have hMQ : ten2K d s * η ^ ((d : ℝ) - s) ≤ ten2K d s * scaleQT s Cp p η X ρ :=
    hMB.trans (mul_le_mul_of_nonneg_left hBQ hK)
  have hAQ : η ^ (-s) / (N : ℝ) ≤ scaleQT s Cp p η X ρ := by linarith
  refine ⟨hQ1, hQ2, ?_, ?_⟩
  · -- (c)
    refine (ten2_sobSq_le hd hs0 hsd hcb' hcb0 hη hρ).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : cb⁻¹ * (∫ x, ∫ y, fTorus s η (x - y) * ρ x * ρ y) ≤
        cb⁻¹ * (2 * scaleQT s Cp p η X ρ + ten2K d s * η ^ ((d : ℝ) - s)) :=
      mul_le_mul_of_nonneg_left hIle (by positivity)
    have h3 : η ^ ((d : ℝ) - s) ≤ scaleQT s Cp p η X ρ := hdB.trans hBQ
    have h4 : cb⁻¹ * (2 * scaleQT s Cp p η X ρ + ten2K d s * η ^ ((d : ℝ) - s)) ≤
        cb⁻¹ * ((2 + ten2K d s) * scaleQT s Cp p η X ρ) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h5 : 0 ≤ (2 + ten2K d s) / cf * scaleQT s Cp p η X ρ := by positivity
    have h6 : cb⁻¹ * ((2 + ten2K d s) * scaleQT s Cp p η X ρ) =
        cb⁻¹ * (2 + ten2K d s) * scaleQT s Cp p η X ρ := by ring
    have h7 : (1 + cb⁻¹ * (2 + ten2K d s) + (2 + ten2K d s) / cf) * scaleQT s Cp p η X ρ =
        scaleQT s Cp p η X ρ + cb⁻¹ * (2 + ten2K d s) * scaleQT s Cp p η X ρ +
          (2 + ten2K d s) / cf * scaleQT s Cp p η X ρ := by ring
    linarith
  · -- (d)
    have h := ten2_occ_core hd hs0 hsd hcf0 hcf hη hη1 hηη₁ hN X hX hAQ hSQ hMQ
    have h4 : 0 ≤ cb⁻¹ * (2 + ten2K d s) * (η ^ s * scaleQT s Cp p η X ρ) := by
      have : 0 < η ^ s := Real.rpow_pos_of_pos hη _
      positivity
    calc _ ≤ (1 + (2 + ten2K d s) / cf) * η ^ s * scaleQT s Cp p η X ρ := h
      _ ≤ (1 + cb⁻¹ * (2 + ten2K d s) + (2 + ten2K d s) / cf) * η ^ s * scaleQT s Cp p η X ρ := by
          nlinarith [h4]

end HRS.Commutator.TorusNote
