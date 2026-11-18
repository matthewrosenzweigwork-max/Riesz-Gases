import HRS.Energy.Commutator.RenormStj0Raw

/-!
# Route S, packet STJ: final assembly for `d = 1`, `s = 0`
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS.Commutator.Renorm

namespace HRS.Commutator.Stj

theorem braw0_alg {CQ Ksg KE KM KT1 KT2 Cm Kb c L R S0 T a Sη Sη0 Q Q0 B4 lg2 lg4 : ℝ}
    (hCQ : 0 ≤ CQ) (hKsg : 0 ≤ Ksg) (hKE : 0 ≤ KE) (hKM : 0 ≤ KM) (hKT1 : 0 ≤ KT1) (hKT2 : 0 ≤ KT2)
    (hCm : 0 ≤ Cm) (hKb : 0 ≤ Kb) (hc : 0 < c) (hL : 0 ≤ L)
    (hSη : Sη ≤ S0 + lg2 * T) (hSη0 : Sη0 ≤ S0 + lg4 * T) (hQ : Q ≤ T + 2 * a) (hQ0 : Q0 ≤ T + 2 * a)
    (hB4 : B4 ≤ 2 * L * KM * a) :
    CQ * L * ((2 / c) * R + c⁻¹ * Sη + KE * Q) + 4 * L * Ksg * Cm * T + B4 +
        (2 * L * KT1 * T + 2 * L * KT2 * (2 * ((2 / c) * R + c⁻¹ * Sη0 + KE * Q0) + Kb * T)) ≤
      L * (((2 * CQ + 8 * KT2) / c) * R + (((2 * CQ + 8 * KT2) / c) / 2) * S0 +
        (CQ * c⁻¹ * lg2 + CQ * KE + 4 * Ksg * Cm + 2 * KT1 + 4 * KT2 * c⁻¹ * lg4 + 4 * KT2 * KE +
          2 * KT2 * Kb) * T + (2 * CQ * KE + 2 * KM + 8 * KT2 * KE) * a) := by
  have hci : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have h1 : CQ * L * c⁻¹ * Sη ≤ CQ * L * c⁻¹ * (S0 + lg2 * T) := mul_le_mul_of_nonneg_left hSη (by positivity)
  have h2 : CQ * L * KE * Q ≤ CQ * L * KE * (T + 2 * a) := mul_le_mul_of_nonneg_left hQ (by positivity)
  have h3 : L * KT2 * c⁻¹ * Sη0 ≤ L * KT2 * c⁻¹ * (S0 + lg4 * T) :=
    mul_le_mul_of_nonneg_left hSη0 (by positivity)
  have h4 : L * KT2 * KE * Q0 ≤ L * KT2 * KE * (T + 2 * a) := mul_le_mul_of_nonneg_left hQ0 (by positivity)
  have key : L * (((2 * CQ + 8 * KT2) / c) * R + (((2 * CQ + 8 * KT2) / c) / 2) * S0 +
        (CQ * c⁻¹ * lg2 + CQ * KE + 4 * Ksg * Cm + 2 * KT1 + 4 * KT2 * c⁻¹ * lg4 + 4 * KT2 * KE +
          2 * KT2 * Kb) * T + (2 * CQ * KE + 2 * KM + 8 * KT2 * KE) * a) -
      (CQ * L * ((2 / c) * R + c⁻¹ * Sη + KE * Q) + 4 * L * Ksg * Cm * T + B4 +
        (2 * L * KT1 * T + 2 * L * KT2 * (2 * ((2 / c) * R + c⁻¹ * Sη0 + KE * Q0) + Kb * T))) =
      (CQ * L * c⁻¹ * (S0 + lg2 * T) - CQ * L * c⁻¹ * Sη) + (CQ * L * KE * (T + 2 * a) - CQ * L * KE * Q) +
        4 * (L * KT2 * c⁻¹ * (S0 + lg4 * T) - L * KT2 * c⁻¹ * Sη0) +
        4 * (L * KT2 * KE * (T + 2 * a) - L * KT2 * KE * Q0) + (2 * L * KM * a - B4) := by
    have hc0 : c ≠ 0 := hc.ne'
    field_simp
    ring
  have hnn : 0 ≤ (CQ * L * c⁻¹ * (S0 + lg2 * T) - CQ * L * c⁻¹ * Sη) +
      (CQ * L * KE * (T + 2 * a) - CQ * L * KE * Q) +
      4 * (L * KT2 * c⁻¹ * (S0 + lg4 * T) - L * KT2 * c⁻¹ * Sη0) +
      4 * (L * KT2 * KE * (T + 2 * a) - L * KT2 * KE * Q0) + (2 * L * KM * a - B4) := by
    have := sub_nonneg.mpr h1
    have := sub_nonneg.mpr h2
    have := sub_nonneg.mpr h3
    have := sub_nonneg.mpr h4
    have := sub_nonneg.mpr hB4
    positivity
  linarith [key, hnn]

theorem con_alg0 {cc AR AT AA C0 R S lp a T L : ℝ} (hcc : 0 < cc) (hAR : 0 ≤ AR) (hAT : 0 ≤ AT)
    (hAA : 0 ≤ AA) (hC0 : 0 ≤ C0) (hL : 0 ≤ L) (hS : 0 ≤ S) (ha : 0 ≤ a) (hT : T ≤ a)
    (hR : 0 ≤ R + lp + C0 * a) :
    cc * (L * (AR * R + (AR / 2) * (S + 2 * lp) + AT * T + AA * a)) ≤
        (cc * AR + 1) * L * (R + lp + S + (C0 + cc * (AT + AA)) * a) ∧
      0 ≤ (cc * AR + 1) * L * (R + lp + S + (C0 + cc * (AT + AA)) * a) := by
  have hb : 0 ≤ R + lp + S + (C0 + cc * (AT + AA)) * a := by
    have : 0 ≤ cc * (AT + AA) * a := by positivity
    nlinarith
  refine ⟨?_, by positivity⟩
  have key : (cc * AR + 1) * L * (R + lp + S + (C0 + cc * (AT + AA)) * a) -
      cc * (L * (AR * R + (AR / 2) * (S + 2 * lp) + AT * T + AA * a)) =
      L * ((R + lp + C0 * a) + (1 + cc * AR / 2) * S + cc * AR * (C0 + cc * (AT + AA)) * a +
        cc * AT * (a - T)) := by ring
  have hnn : 0 ≤ L * ((R + lp + C0 * a) + (1 + cc * AR / 2) * S + cc * AR * (C0 + cc * (AT + AA)) * a +
        cc * AT * (a - T)) := by
    have h1 : 0 ≤ a - T := sub_nonneg.mpr hT
    positivity
  linarith [key, hnn]

theorem smearScale_one (N : ℕ) (Λ : ℝ) : smearScale 1 N Λ = ((N : ℝ) * Λ)⁻¹ := by
  unfold smearScale
  simp [Real.rpow_neg_one]

theorem sum_neg_log_eq {N : ℕ} (hN : 0 < N) {Λ : ℝ} (hΛ : 0 < Λ) {r : Fin N → ℝ} (hr : ∀ i, 0 < r i) :
    (1 / (N : ℝ)) ^ 2 * ∑ i, -Real.log (r i) =
      (1 / (N : ℝ) ^ 2) * ∑ i, selfExcess 1 0 Λ N (r i) + 2 * logPart 1 0 Λ N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNΛ : 0 < (N : ℝ) * Λ := by positivity
  have hse : ∀ i, selfExcess 1 0 Λ N (r i) = -Real.log ((N : ℝ) * Λ) - Real.log (r i) := fun i => by
    unfold selfExcess
    rw [if_pos rfl, smearScale_one, Real.log_div (inv_ne_zero hNΛ.ne') (hr i).ne', Real.log_inv]
  have hlp : logPart 1 0 Λ N = Real.log ((N : ℝ) * Λ) / (2 * 1 * N) := by
    unfold logPart; simp
  simp only [hse, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, hlp, Finset.sum_neg_distrib]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem super_core_stj_zero :
    ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 2 ≤ N →
      ∀ ρ : Torus 1 → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config 1 N, X ∉ collisionSet 1 N →
      ∀ (L : ℝ) (v : Torus 1 → Euc 1), 0 ≤ L → IsLipschitzVF L v →
        |commQuantity 1 0 v X (withDensityReal ρ)| ≤
          C * L * (rieszEnergy 1 0 X (withDensityReal ρ) + logPart 1 0 Λ N +
            (1 / (N : ℝ) ^ 2) * ∑ i, selfExcess 1 0 Λ N (smearRadius Λ X i) + K * aNΛ 1 0 Λ N) := by
  obtain ⟨c, hc, hker⟩ := stieltjes_kernel (d := 1) le_rfl (s := 0) le_rfl (by norm_num) (by norm_num)
  obtain ⟨cc, hcc, hcomm⟩ := commQuantity_stieltjes (d := 1) le_rfl (s := 0) le_rfl (by norm_num) (by norm_num)
  obtain ⟨CQ, Ksg, KE, KM, KT1, KT2, Cm, Kb, hCQ, hKsg, hKE, hKM, hKT1, hKT2, hCm, hKb, hraw⟩ :=
    stj_raw0 hc hker
  obtain ⟨C0, hC00, hcoer⟩ := coercivity_lower (d := 1) le_rfl (s := 0) le_rfl (by norm_num)
  set AR : ℝ := (2 * CQ + 8 * KT2) / c with hAR
  set AT : ℝ := CQ * c⁻¹ * Real.log 2 + CQ * KE + 4 * Ksg * Cm + 2 * KT1 + 4 * KT2 * c⁻¹ * Real.log 4 +
    4 * KT2 * KE + 2 * KT2 * Kb with hAT
  set AA : ℝ := 2 * CQ * KE + 2 * KM + 8 * KT2 * KE with hAA
  have hlg2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlg4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hci : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have hAR0 : 0 ≤ AR := by positivity
  have hAT0 : 0 ≤ AT := by positivity
  have hAA0 : 0 ≤ AA := by positivity
  refine ⟨cc * AR + 1, C0 + cc * (AT + AA), by positivity, by positivity, ?_⟩
  intro Λ hΛ N hN ρ hρ hρΛ X hX L v hL hv
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hΛpos : 0 < Λ := by linarith
  have hX' : ∀ i j, i ≠ j → X i ≠ X j := fun i j hij h => hX ⟨i, j, hij, h⟩
  obtain ⟨hr0, hrl, hr8, hsep⟩ := radii_facts (d := 1) le_rfl hN hΛ X hX'
  obtain ⟨η, hηmem, hint⟩ := hraw hN hΛ hρ hρΛ hX hL hv
  set μ := withDensityReal ρ with hμdef
  set r : Fin N → ℝ := fun i => smearRadius Λ X i with hr
  set R : ℝ := rieszEnergy 1 0 X μ with hR
  set a : ℝ := aNΛ 1 0 Λ N with ha
  set S : ℝ := (1 / (N : ℝ) ^ 2) * ∑ i, selfExcess 1 0 Λ N (r i) with hS
  set lp : ℝ := logPart 1 0 Λ N with hlp
  have ha0 : 0 ≤ a := by rw [ha]; unfold aNΛ; positivity
  have hlam : 0 < smearScale 1 N Λ := CoercAux.smearScale_pos hNpos hΛpos
  have hS0 : 0 ≤ S := by
    rw [hS]
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => ?_)
    unfold selfExcess
    rw [if_pos rfl]
    apply Real.log_nonneg
    rw [le_div_iff₀ (hr0 i)]
    have := hrl i
    linarith [hr0 i]
  -- the sums
  have hSigma : (1 / (N : ℝ)) ^ 2 * ∑ i, -Real.log (r i) = S + 2 * lp := sum_neg_log_eq hNpos hΛpos hr0
  have hT1 : 1 / (N : ℝ) ≤ a := inv_le_aN_s (d := 1) le_rfl (s := 0) le_rfl hΛ hNpos
  have hT2 : Λ * (1 / (N : ℝ)) * ∑ i, r i ≤ a := by
    have h := rpow_sum_le_aN (d := 1) le_rfl (s := 0) (by norm_num) hΛpos hNpos (ξ := r)
      (fun i => (hr0 i).le) (fun i => by linarith [hrl i])
    simpa using h
  have hηpos : ∀ i, 0 < η i := fun i => by linarith [(hηmem i).1, hr0 i]
  have hSη : Sig0 η ≤ (1 / (N : ℝ)) ^ 2 * ∑ i, -Real.log (r i) + Real.log 2 * (1 / (N : ℝ)) := by
    unfold Sig0
    have h1 : ∀ i, -Real.log (η i) ≤ -Real.log (r i) + Real.log 2 := fun i => by
      have : Real.log (r i / 2) ≤ Real.log (η i) :=
        Real.log_le_log (by have := hr0 i; positivity) (by linarith [(hηmem i).1])
      rw [Real.log_div (hr0 i).ne' (by norm_num)] at this
      linarith
    have h2 : ∑ i, -Real.log (η i) ≤ ∑ i, (-Real.log (r i) + Real.log 2) := Finset.sum_le_sum fun i _ => h1 i
    rw [Finset.sum_add_distrib] at h2
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (1 / (N : ℝ)) ^ 2)
    have e : (1 / (N : ℝ)) ^ 2 * ((N : ℝ) * Real.log 2) = Real.log 2 * (1 / (N : ℝ)) := by field_simp
    nlinarith [h3, e]
  have hSη0 : Sig0 (fun i => r i / 4) ≤ (1 / (N : ℝ)) ^ 2 * ∑ i, -Real.log (r i) + Real.log 4 * (1 / (N : ℝ)) := by
    unfold Sig0
    have h1 : ∀ i, -Real.log (r i / 4) = -Real.log (r i) + Real.log 4 := fun i => by
      rw [Real.log_div (hr0 i).ne' (by norm_num)]; ring
    simp only [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have e : (1 / (N : ℝ)) ^ 2 * ((N : ℝ) * Real.log 4) = Real.log 4 * (1 / (N : ℝ)) := by field_simp
    nlinarith [e]
  have hsumη : ∑ i, η i ≤ ∑ i, r i := Finset.sum_le_sum fun i _ => (hηmem i).2.le
  have hsumη0 : ∑ i, r i / 4 ≤ ∑ i, r i := Finset.sum_le_sum fun i _ => by linarith [hr0 i]
  have hQ1 : Q1 Λ η ≤ 1 / (N : ℝ) + 2 * a := by
    unfold Q1
    have h : (1 + Λ) * (1 / (N : ℝ)) * ∑ i, η i ≤ 2 * (Λ * (1 / (N : ℝ)) * ∑ i, r i) := by
      have hu : 0 ≤ 1 / (N : ℝ) := by positivity
      have hs0 : 0 ≤ ∑ i, η i := Finset.sum_nonneg fun i _ => (hηpos i).le
      calc (1 + Λ) * (1 / (N : ℝ)) * ∑ i, η i ≤ (2 * Λ) * (1 / (N : ℝ)) * ∑ i, η i :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hu) hs0
        _ ≤ (2 * Λ) * (1 / (N : ℝ)) * ∑ i, r i := mul_le_mul_of_nonneg_left hsumη (by positivity)
        _ = _ := by ring
    linarith
  have hQ10 : Q1 Λ (fun i => r i / 4) ≤ 1 / (N : ℝ) + 2 * a := by
    unfold Q1
    have h : (1 + Λ) * (1 / (N : ℝ)) * ∑ i, r i / 4 ≤ 2 * (Λ * (1 / (N : ℝ)) * ∑ i, r i) := by
      have hu : 0 ≤ 1 / (N : ℝ) := by positivity
      have hs0 : 0 ≤ ∑ i, r i / 4 := Finset.sum_nonneg fun i _ => by have := hr0 i; positivity
      calc (1 + Λ) * (1 / (N : ℝ)) * ∑ i, r i / 4 ≤ (2 * Λ) * (1 / (N : ℝ)) * ∑ i, r i / 4 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hu) hs0
        _ ≤ (2 * Λ) * (1 / (N : ℝ)) * ∑ i, r i := mul_le_mul_of_nonneg_left hsumη0 (by positivity)
        _ = _ := by ring
    linarith
  have hB4 : (2 / (N : ℝ)) * ∑ i, Λ * L * (KM * η i) ≤ 2 * L * KM * a := by
    have e1 : ∑ i, Λ * L * (KM * η i) = Λ * L * KM * ∑ i, η i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1]
    have : (2 / (N : ℝ)) * (Λ * L * KM * ∑ i, η i) = 2 * L * KM * (Λ * (1 / (N : ℝ)) * ∑ i, η i) := by
      field_simp
    rw [this]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc Λ * (1 / (N : ℝ)) * ∑ i, η i ≤ Λ * (1 / (N : ℝ)) * ∑ i, r i :=
          mul_le_mul_of_nonneg_left hsumη (by positivity)
      _ ≤ a := hT2
  have e5 : (2 / (N : ℝ)) * ∑ _i : Fin N, L * (KT1 / N) = 2 * L * KT1 * (1 / (N : ℝ)) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have e6 : ∀ Z : ℝ, (2 / (N : ℝ)) * (L * KT2 * N) * Z = 2 * L * KT2 * Z := fun Z => by field_simp
  rw [e5, e6] at hint
  have hBraw := braw0_alg (CQ := CQ) (Ksg := Ksg) (KE := KE) (KM := KM) (KT1 := KT1) (KT2 := KT2) (Cm := Cm)
    (Kb := Kb) (c := c) (L := L) (R := R) (S0 := (1 / (N : ℝ)) ^ 2 * ∑ i, -Real.log (r i)) (T := 1 / (N : ℝ))
    (a := a) (Sη := Sig0 η) (Sη0 := Sig0 (fun i => r i / 4)) (Q := Q1 Λ η) (Q0 := Q1 Λ (fun i => r i / 4))
    (B4 := (2 / (N : ℝ)) * ∑ i, Λ * L * (KM * η i)) (lg2 := Real.log 2) (lg4 := Real.log 4)
    hCQ hKsg hKE hKM hKT1 hKT2 hCm hKb hc hL hSη hSη0 hQ1 hQ10 hB4
  rw [hSigma] at hBraw
  have hG := hint.trans (ENNReal.ofReal_le_ofReal hBraw)
  have hcon := con_alg0 (cc := cc) (AR := AR) (AT := AT) (AA := AA) (C0 := C0) (R := R) (S := S) (lp := lp)
    (a := a) (T := 1 / (N : ℝ)) (L := L) hcc hAR0 hAT0 hAA0 hC00 hL hS0 ha0 hT1 (by
      have h := hcoer Λ hΛ N hN ρ hρ hρΛ X hX
      rw [oNΛ_eq] at h
      linarith)
  rw [hcomm N X ρ hρ Λ hρΛ hX L v hL hv]
  have hnorm := norm_integral_le_lintegral_norm (μ := volume.restrict (Ioi (0 : ℝ)))
    (fun l : ℝ => l ^ (-bexp 1 0) * offDiagPairing (commKernel (sliceGrad 1 l) v) X μ)
  have hE : ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal ‖l ^ (-bexp 1 0) *
        offDiagPairing (commKernel (sliceGrad 1 l) v) X μ‖ =
      ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp 1 0)) *
        ENNReal.ofReal |offDiagPairing (commKernel (SliceAux.sgv l) v) X μ| := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun l hl => ?_
    have hl' : (0 : ℝ) < l := hl
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hl'.le _),
      ENNReal.ofReal_mul (Real.rpow_nonneg hl'.le _), RoughLimit.commKernel_sliceGrad hl'.le v]
  rw [hE] at hnorm
  have hMle := ENNReal.toReal_mono ENNReal.ofReal_ne_top hG
  rw [ENNReal.toReal_ofReal'] at hMle
  rw [Real.norm_eq_abs] at hnorm
  have hfin : cc * max (L * (AR * R + (AR / 2) * (S + 2 * lp) + AT * (1 / (N : ℝ)) + AA * a)) 0 ≤
      (cc * AR + 1) * L * (R + lp + S + (C0 + cc * (AT + AA)) * a) := by
    rcases le_total (L * (AR * R + (AR / 2) * (S + 2 * lp) + AT * (1 / (N : ℝ)) + AA * a)) 0 with h | h
    · rw [max_eq_right h]; simpa using hcon.2
    · rw [max_eq_left h]; exact hcon.1
  rw [abs_mul, abs_of_pos hcc]
  calc cc * |∫ l in Ioi (0 : ℝ), l ^ (-bexp 1 0) * offDiagPairing (commKernel (sliceGrad 1 l) v) X μ|
      ≤ cc * (max (L * (AR * R + (AR / 2) * (S + 2 * lp) + AT * (1 / (N : ℝ)) + AA * a)) 0) :=
        mul_le_mul_of_nonneg_left (hnorm.trans hMle) hcc.le
    _ ≤ _ := hfin

end HRS.Commutator.Stj
