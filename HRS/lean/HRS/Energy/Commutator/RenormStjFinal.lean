import HRS.Energy.Commutator.RenormStjRaw
import HRS.Energy.Commutator.RenormFinal

/-!
# Route S, packet STJ: final assembly for `s > 0`
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS.Commutator.Renorm

namespace HRS.Commutator.Stj

variable {d : ℕ}

theorem inv_le_aN_s (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) {Λ : ℝ} (hΛ : 1 ≤ Λ) {N : ℕ} (hN : 0 < N) :
    1 / (N : ℝ) ≤ aNΛ d s Λ N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hs : (0 : ℝ) ≤ s / d := div_nonneg hs0 hd0.le
  unfold aNΛ
  have h1 : (1 : ℝ) ≤ Λ ^ (s / d) := Real.one_le_rpow hΛ hs
  have h2 : 1 / (N : ℝ) ≤ (N : ℝ) ^ (s / d - 1) := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
  calc 1 / (N : ℝ) ≤ (N : ℝ) ^ (s / d - 1) := h2
    _ = 1 * (N : ℝ) ^ (s / d - 1) := (one_mul _).symm
    _ ≤ Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)

theorem rpow_sum_le_aN (hd : 1 ≤ d) {s : ℝ} (hsd : s < d) {Λ : ℝ} (hΛ : 0 < Λ) {N : ℕ} (hN : 0 < N)
    {ξ : Fin N → ℝ} (hξ0 : ∀ i, 0 ≤ ξ i) (hξ : ∀ i, ξ i ≤ smearScale d N Λ) :
    Λ * (1 / (N : ℝ)) * ∑ i, ξ i ^ ((d : ℝ) - s) ≤ aNΛ d s Λ N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hds : 0 ≤ (d : ℝ) - s := by linarith
  have h1 : ∑ i, ξ i ^ ((d : ℝ) - s) ≤ ∑ _i : Fin N, (smearScale d N Λ) ^ ((d : ℝ) - s) :=
    Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (hξ0 i) (hξ i) hds
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  have e1 : (smearScale d N Λ) ^ ((d : ℝ) - s) = (N : ℝ) ^ (s / d - 1) * Λ ^ (s / d - 1) := by
    unfold smearScale
    have hd0' : (d : ℝ) ≠ 0 := hd0.ne'
    rw [← Real.rpow_mul (by positivity), Real.mul_rpow hNr.le hΛ.le]
    have : -1 / (d : ℝ) * ((d : ℝ) - s) = s / d - 1 := by field_simp; ring
    rw [this]
  have e2 : Λ * Λ ^ (s / (d : ℝ) - 1) = Λ ^ (s / (d : ℝ)) := by
    have : Λ ^ (s / (d : ℝ)) = Λ ^ ((1 : ℝ) + (s / (d : ℝ) - 1)) := by congr 1; ring
    rw [this, Real.rpow_add hΛ, Real.rpow_one]
  calc Λ * (1 / (N : ℝ)) * ∑ i, ξ i ^ ((d : ℝ) - s)
      ≤ Λ * (1 / (N : ℝ)) * (N * (smearScale d N Λ) ^ ((d : ℝ) - s)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = aNΛ d s Λ N := by
        rw [e1]; unfold aNΛ
        have := e2
        calc Λ * (1 / (N : ℝ)) * (N * ((N : ℝ) ^ (s / d - 1) * Λ ^ (s / d - 1)))
            = (Λ * Λ ^ (s / (d : ℝ) - 1)) * (N : ℝ) ^ (s / d - 1) := by field_simp
          _ = _ := by rw [this]

theorem Sig1_le (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {Λ : ℝ} (hΛ : 1 ≤ Λ) {N : ℕ} (hN : 0 < N)
    {r η : Fin N → ℝ} {θ : ℝ} (hθ : 0 < θ) (hr0 : ∀ i, 0 < r i) (hη : ∀ i, θ * r i ≤ η i ∧ η i ≤ r i) :
    Sig1 d s Λ η ≤ θ ^ (-s) * ((1 / (N : ℝ)) ^ 2 * ∑ i, r i ^ (-s)) + 1 / (N : ℝ) +
      2 * (Λ * (1 / (N : ℝ)) * ∑ i, r i ^ ((d : ℝ) - s)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hds : 0 ≤ (d : ℝ) - s := by linarith
  have hηpos : ∀ i, 0 < η i := fun i => lt_of_lt_of_le (mul_pos hθ (hr0 i)) (hη i).1
  have h1 : ∀ i, η i ^ (-s) ≤ θ ^ (-s) * r i ^ (-s) := fun i => by
    rw [← Real.mul_rpow hθ.le (hr0 i).le]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos hθ (hr0 i)) (hη i).1 (by linarith)
  have h2 : ∀ i, η i ^ ((d : ℝ) - s) ≤ r i ^ ((d : ℝ) - s) := fun i =>
    Real.rpow_le_rpow (hηpos i).le (hη i).2 hds
  have hs1 : ∑ i, (η i ^ (-s) + 1) ≤ θ ^ (-s) * ∑ i, r i ^ (-s) + N := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact add_le_add (Finset.sum_le_sum fun i _ => h1 i) le_rfl
  have hs2 : ∑ i, η i ^ ((d : ℝ) - s) ≤ ∑ i, r i ^ ((d : ℝ) - s) := Finset.sum_le_sum fun i _ => h2 i
  unfold Sig1
  have hN2 : (0 : ℝ) ≤ (1 / (N : ℝ)) ^ 2 := by positivity
  have h3 := mul_le_mul_of_nonneg_left hs1 hN2
  have h4 : (1 + Λ) * (1 / (N : ℝ)) * ∑ i, η i ^ ((d : ℝ) - s) ≤
      2 * (Λ * (1 / (N : ℝ)) * ∑ i, r i ^ ((d : ℝ) - s)) := by
    have hsum0 : 0 ≤ ∑ i, η i ^ ((d : ℝ) - s) := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hηpos i).le _
    have hu : 0 ≤ 1 / (N : ℝ) := by positivity
    calc (1 + Λ) * (1 / (N : ℝ)) * ∑ i, η i ^ ((d : ℝ) - s)
        ≤ (2 * Λ) * (1 / (N : ℝ)) * ∑ i, η i ^ ((d : ℝ) - s) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hu) hsum0
      _ ≤ (2 * Λ) * (1 / (N : ℝ)) * ∑ i, r i ^ ((d : ℝ) - s) :=
          mul_le_mul_of_nonneg_left hs2 (by positivity)
      _ = _ := by ring
  have e : (1 / (N : ℝ)) ^ 2 * (N : ℝ) = 1 / N := by field_simp
  nlinarith [h3, h4, e]

theorem braw_alg {CQ Cs KE KU KJ KM KT1 KT2 c L R S T1 T2 Sη Sη0 θ1 θ2 B4 : ℝ}
    (hCQ : 0 ≤ CQ) (hCs : 0 ≤ Cs) (hKE : 0 ≤ KE) (hKU : 0 ≤ KU) (hKJ : 0 ≤ KJ) (hKM : 0 ≤ KM)
    (hKT1 : 0 ≤ KT1) (hKT2 : 0 ≤ KT2) (hc : 0 < c) (hL : 0 ≤ L)
    (hSη : Sη ≤ θ1 * S + T1 + 2 * T2) (hSη0 : Sη0 ≤ θ2 * S + T1 + 2 * T2) (hB4 : B4 ≤ 2 * L * KM * T2) :
    CQ * L * ((2 / c) * R + KE * Sη) + Cs * L * (KU * Sη) + 2 * L * T1 * KJ + B4 +
        (2 * L * KT1 * S + 2 * L * KT2 * (2 * ((2 / c) * R + KE * Sη0) + 2 * (KU * Sη0))) ≤
      L * ((CQ * (2 / c) + KT2 * (8 / c)) * R +
        ((CQ * KE + Cs * KU) * θ1 + 2 * KT1 + 4 * KT2 * (KE + KU) * θ2) * S +
        (2 * KJ + (CQ * KE + Cs * KU) + 4 * KT2 * (KE + KU)) * T1 +
        (2 * KM + 2 * (CQ * KE + Cs * KU) + 8 * KT2 * (KE + KU)) * T2) := by
  have h1 : CQ * L * KE * Sη ≤ CQ * L * KE * (θ1 * S + T1 + 2 * T2) :=
    mul_le_mul_of_nonneg_left hSη (by positivity)
  have h2 : Cs * L * KU * Sη ≤ Cs * L * KU * (θ1 * S + T1 + 2 * T2) :=
    mul_le_mul_of_nonneg_left hSη (by positivity)
  have h3 : L * KT2 * KE * Sη0 ≤ L * KT2 * KE * (θ2 * S + T1 + 2 * T2) :=
    mul_le_mul_of_nonneg_left hSη0 (by positivity)
  have h4 : L * KT2 * KU * Sη0 ≤ L * KT2 * KU * (θ2 * S + T1 + 2 * T2) :=
    mul_le_mul_of_nonneg_left hSη0 (by positivity)
  have key : L * ((CQ * (2 / c) + KT2 * (8 / c)) * R +
        ((CQ * KE + Cs * KU) * θ1 + 2 * KT1 + 4 * KT2 * (KE + KU) * θ2) * S +
        (2 * KJ + (CQ * KE + Cs * KU) + 4 * KT2 * (KE + KU)) * T1 +
        (2 * KM + 2 * (CQ * KE + Cs * KU) + 8 * KT2 * (KE + KU)) * T2) -
    (CQ * L * ((2 / c) * R + KE * Sη) + Cs * L * (KU * Sη) + 2 * L * T1 * KJ + B4 +
        (2 * L * KT1 * S + 2 * L * KT2 * (2 * ((2 / c) * R + KE * Sη0) + 2 * (KU * Sη0)))) =
    (CQ * L * KE * (θ1 * S + T1 + 2 * T2) - CQ * L * KE * Sη) +
      (Cs * L * KU * (θ1 * S + T1 + 2 * T2) - Cs * L * KU * Sη)
    + 4 * (L * KT2 * KE * (θ2 * S + T1 + 2 * T2) - L * KT2 * KE * Sη0)
    + 4 * (L * KT2 * KU * (θ2 * S + T1 + 2 * T2) - L * KT2 * KU * Sη0) + (2 * L * KM * T2 - B4) := by ring
  have hnn : 0 ≤ (CQ * L * KE * (θ1 * S + T1 + 2 * T2) - CQ * L * KE * Sη) +
      (Cs * L * KU * (θ1 * S + T1 + 2 * T2) - Cs * L * KU * Sη)
    + 4 * (L * KT2 * KE * (θ2 * S + T1 + 2 * T2) - L * KT2 * KE * Sη0)
    + 4 * (L * KT2 * KU * (θ2 * S + T1 + 2 * T2) - L * KT2 * KU * Sη0) + (2 * L * KM * T2 - B4) := by
    have := sub_nonneg.mpr h1
    have := sub_nonneg.mpr h2
    have := sub_nonneg.mpr h3
    have := sub_nonneg.mpr h4
    have := sub_nonneg.mpr hB4
    positivity
  linarith [key, hnn]

theorem con_alg {cc AR AS AT1 AT2 C0 R S a T1 T2 L : ℝ} (hcc : 0 < cc) (hAR : 0 ≤ AR) (hAS : 0 ≤ AS)
    (hAT1 : 0 ≤ AT1) (hAT2 : 0 ≤ AT2) (hC0 : 0 ≤ C0) (hL : 0 ≤ L) (hS : 0 ≤ S) (ha : 0 ≤ a)
    (hT1 : T1 ≤ a) (hT2 : T2 ≤ a) (hR : 0 ≤ R + C0 * a) :
    cc * (L * (AR * R + AS * S + AT1 * T1 + AT2 * T2)) ≤
        (cc * (AR + AS) + 1) * L * (R + S + (C0 + cc * (AT1 + AT2)) * a) ∧
      0 ≤ (cc * (AR + AS) + 1) * L * (R + S + (C0 + cc * (AT1 + AT2)) * a) := by
  have hC1 : 0 ≤ cc * (AR + AS) := by positivity
  have hb : 0 ≤ R + S + (C0 + cc * (AT1 + AT2)) * a := by
    have : 0 ≤ cc * (AT1 + AT2) * a := by positivity
    nlinarith
  refine ⟨?_, by positivity⟩
  have key : (cc * (AR + AS) + 1) * L * (R + S + (C0 + cc * (AT1 + AT2)) * a) -
      cc * (L * (AR * R + AS * S + AT1 * T1 + AT2 * T2)) =
      L * ((cc * AS + 1) * (R + C0 * a) + (cc * AR + 1) * S + cc * AR * C0 * a +
        (cc * (AR + AS)) * cc * (AT1 + AT2) * a + cc * AT1 * (a - T1) + cc * AT2 * (a - T2)) := by ring
  have hnn : 0 ≤ L * ((cc * AS + 1) * (R + C0 * a) + (cc * AR + 1) * S + cc * AR * C0 * a +
        (cc * (AR + AS)) * cc * (AT1 + AT2) * a + cc * AT1 * (a - T1) + cc * AT2 * (a - T2)) := by
    have h1 : 0 ≤ a - T1 := sub_nonneg.mpr hT1
    have h2 : 0 ≤ a - T2 := sub_nonneg.mpr hT2
    positivity
  linarith [key, hnn]

set_option maxHeartbeats 4000000 in
theorem super_core_stj_pos (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hs : (d : ℝ) - 2 < s) (hsd : s < d) :
    ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 2 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
      ∀ (L : ℝ) (v : Torus d → Euc d), 0 ≤ L → IsLipschitzVF L v →
        |commQuantity d s v X (withDensityReal ρ)| ≤
          C * L * (rieszEnergy d s X (withDensityReal ρ) + logPart d s Λ N +
            (1 / (N : ℝ) ^ 2) * ∑ i, selfExcess d s Λ N (smearRadius Λ X i) + K * aNΛ d s Λ N) := by
  obtain ⟨c, hc, hker⟩ := stieltjes_kernel hd hs0.le hs hsd
  obtain ⟨cc, hcc, hcomm⟩ := commQuantity_stieltjes hd hs0.le hs hsd
  obtain ⟨CQ, Cs, KE, KU, KJ, KM, KT1, KT2, hCQ, hCs, hKE, hKU, hKJ, hKM, hKT1, hKT2, hraw⟩ :=
    stj_raw hd hs0 hs hsd hc hker
  obtain ⟨C0, hC00, hcoer⟩ := coercivity_lower hd hs0.le hsd
  have hθ1 : 0 ≤ ((1 : ℝ) / 2) ^ (-s) := Real.rpow_nonneg (by norm_num) _
  have hθ2 : 0 ≤ ((1 : ℝ) / 4) ^ (-s) := Real.rpow_nonneg (by norm_num) _
  set AR : ℝ := CQ * (2 / c) + KT2 * (8 / c) with hAR
  set AS : ℝ := (CQ * KE + Cs * KU) * ((1 : ℝ) / 2) ^ (-s) + 2 * KT1 +
    4 * KT2 * (KE + KU) * ((1 : ℝ) / 4) ^ (-s) with hAS
  set AT1 : ℝ := 2 * KJ + (CQ * KE + Cs * KU) + 4 * KT2 * (KE + KU) with hAT1
  set AT2 : ℝ := 2 * KM + 2 * (CQ * KE + Cs * KU) + 8 * KT2 * (KE + KU) with hAT2
  have hAR0 : 0 ≤ AR := by positivity
  have hAS0 : 0 ≤ AS := by positivity
  have hAT10 : 0 ≤ AT1 := by positivity
  have hAT20 : 0 ≤ AT2 := by positivity
  refine ⟨cc * (AR + AS) + 1, C0 + cc * (AT1 + AT2), by positivity, by positivity, ?_⟩
  intro Λ hΛ N hN ρ hρ hρΛ X hX L v hL hv
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hΛpos : 0 < Λ := by linarith
  have hX' : ∀ i j, i ≠ j → X i ≠ X j := fun i j hij h => hX ⟨i, j, hij, h⟩
  obtain ⟨hr0, hrl, hr8, hsep⟩ := radii_facts hd hN hΛ X hX'
  obtain ⟨η, hηmem, hint⟩ := hraw hN hΛ hρ hρΛ hX hL hv
  set μ := withDensityReal ρ with hμdef
  set r : Fin N → ℝ := fun i => smearRadius Λ X i with hr
  set R : ℝ := rieszEnergy d s X μ with hR
  set a : ℝ := aNΛ d s Λ N with ha
  set S : ℝ := (1 / (N : ℝ) ^ 2) * ∑ i, r i ^ (-s) with hS
  have ha0 : 0 ≤ a := by rw [ha]; unfold aNΛ; positivity
  have hS0 : 0 ≤ S := by
    rw [hS]; exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hr0 i).le _)
  have hlam : 0 < smearScale d N Λ := CoercAux.smearScale_pos hNpos hΛpos
  -- the sums
  have hSS : (1 / (N : ℝ)) ^ 2 * ∑ i, r i ^ (-s) = S := by rw [hS, one_div_pow]
  have hSig1 := Sig1_le hd hs0.le hsd hΛ hNpos (r := r) (η := η) (θ := 1 / 2) (by norm_num) hr0
    (fun i => ⟨by linarith [(hηmem i).1], (hηmem i).2.le⟩)
  have hSig0 := Sig1_le hd hs0.le hsd hΛ hNpos (r := r) (η := fun i => r i / 4) (θ := 1 / 4) (by norm_num) hr0
    (fun i => ⟨by linarith, by linarith [hr0 i]⟩)
  rw [hSS] at hSig1 hSig0
  have hT1 : 1 / (N : ℝ) ≤ a := inv_le_aN_s hd hs0.le hΛ hNpos
  have hT2 : Λ * (1 / (N : ℝ)) * ∑ i, r i ^ ((d : ℝ) - s) ≤ a :=
    rpow_sum_le_aN hd hsd hΛpos hNpos (fun i => (hr0 i).le) (fun i => by linarith [hrl i])
  have hB4 : (2 / (N : ℝ)) * ∑ i, Λ * L * (KM * η i ^ ((d : ℝ) - s)) ≤
      2 * L * KM * (Λ * (1 / (N : ℝ)) * ∑ i, r i ^ ((d : ℝ) - s)) := by
    have hηpos : ∀ i, 0 < η i := fun i => by linarith [(hηmem i).1, hr0 i]
    have h1 : ∑ i, η i ^ ((d : ℝ) - s) ≤ ∑ i, r i ^ ((d : ℝ) - s) :=
      Finset.sum_le_sum fun i _ => Real.rpow_le_rpow (hηpos i).le (hηmem i).2.le (by linarith)
    have e1 : ∑ i, Λ * L * (KM * η i ^ ((d : ℝ) - s)) = Λ * L * KM * ∑ i, η i ^ ((d : ℝ) - s) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1]
    have : (2 / (N : ℝ)) * (Λ * L * KM * ∑ i, η i ^ ((d : ℝ) - s)) =
        2 * L * KM * (Λ * (1 / (N : ℝ)) * ∑ i, η i ^ ((d : ℝ) - s)) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by positivity)) (by positivity)
  have e5 : (2 / (N : ℝ)) * ∑ i, L * (KT1 * r i ^ (-s) / N) = 2 * L * KT1 * S := by
    have : ∑ i, L * (KT1 * r i ^ (-s) / N) = (L * KT1 / N) * ∑ i, r i ^ (-s) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hS]; field_simp
  have e6 : ∀ Z : ℝ, (2 / (N : ℝ)) * (L * KT2 * N) * Z = 2 * L * KT2 * Z := fun Z => by field_simp
  rw [e5, e6] at hint
  have hBraw := braw_alg (CQ := CQ) (Cs := Cs) (KE := KE) (KU := KU) (KJ := KJ) (KM := KM) (KT1 := KT1)
    (KT2 := KT2) (c := c) (L := L) (R := R) (S := S) (T1 := 1 / (N : ℝ))
    (T2 := Λ * (1 / (N : ℝ)) * ∑ i, r i ^ ((d : ℝ) - s)) (θ1 := ((1 : ℝ) / 2) ^ (-s))
    (θ2 := ((1 : ℝ) / 4) ^ (-s)) hCQ hCs hKE hKU hKJ hKM hKT1 hKT2 hc hL hSig1 hSig0 hB4
  have hG := hint.trans (ENNReal.ofReal_le_ofReal hBraw)
  have hcon := con_alg (cc := cc) (AR := AR) (AS := AS) (AT1 := AT1) (AT2 := AT2) (C0 := C0) (R := R)
    (S := S) (a := a) (T1 := 1 / (N : ℝ)) (T2 := Λ * (1 / (N : ℝ)) * ∑ i, r i ^ ((d : ℝ) - s)) (L := L)
    hcc hAR0 hAS0 hAT10 hAT20 hC00 hL hS0 ha0 hT1 hT2 (by
      have h := hcoer Λ hΛ N hN ρ hρ hρΛ X hX
      rw [oNΛ_eq] at h
      have hlp : logPart d s Λ N = 0 := by unfold logPart; rw [if_neg hs0.ne']
      rw [hlp] at h
      linarith)
  have hlp : logPart d s Λ N = 0 := by unfold logPart; rw [if_neg hs0.ne']
  have hse : (∑ i, selfExcess d s Λ N (r i)) = ∑ i, r i ^ (-s) :=
    Finset.sum_congr rfl fun i _ => by unfold selfExcess; rw [if_neg hs0.ne']
  rw [hcomm N X ρ hρ Λ hρΛ hX L v hL hv]
  -- the norm of the integral
  have hnorm := norm_integral_le_lintegral_norm (μ := volume.restrict (Ioi (0 : ℝ)))
    (fun l : ℝ => l ^ (-bexp d s) * offDiagPairing (commKernel (sliceGrad d l) v) X μ)
  have hE : ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal ‖l ^ (-bexp d s) *
        offDiagPairing (commKernel (sliceGrad d l) v) X μ‖ =
      ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) *
        ENNReal.ofReal |offDiagPairing (commKernel (SliceAux.sgv l) v) X μ| := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun l hl => ?_
    have hl' : (0 : ℝ) < l := hl
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hl'.le _),
      ENNReal.ofReal_mul (Real.rpow_nonneg hl'.le _), RoughLimit.commKernel_sliceGrad hl'.le v]
  rw [hE] at hnorm
  have hGtop : (∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp d s)) *
        ENNReal.ofReal |offDiagPairing (commKernel (SliceAux.sgv l) v) X μ|) ≠ ⊤ :=
    (lt_of_le_of_lt hG ENNReal.ofReal_lt_top).ne
  have hMle := ENNReal.toReal_mono ENNReal.ofReal_ne_top hG
  rw [ENNReal.toReal_ofReal'] at hMle
  rw [Real.norm_eq_abs] at hnorm
  have hfin : cc * max (L * (AR * R + AS * S + AT1 * (1 / (N : ℝ)) +
      AT2 * (Λ * (1 / (N : ℝ)) * ∑ i, r i ^ ((d : ℝ) - s)))) 0 ≤
      (cc * (AR + AS) + 1) * L * (R + S + (C0 + cc * (AT1 + AT2)) * a) := by
    rcases le_total (L * (AR * R + AS * S + AT1 * (1 / (N : ℝ)) +
      AT2 * (Λ * (1 / (N : ℝ)) * ∑ i, r i ^ ((d : ℝ) - s)))) 0 with h | h
    · rw [max_eq_right h]; simpa using hcon.2
    · rw [max_eq_left h]; exact hcon.1
  rw [abs_mul, abs_of_pos hcc, hlp, hse]
  calc cc * |∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * offDiagPairing (commKernel (sliceGrad d l) v) X μ|
      ≤ cc * (max (L * (AR * R + AS * S + AT1 * (1 / (N : ℝ)) +
      AT2 * (Λ * (1 / (N : ℝ)) * ∑ i, r i ^ ((d : ℝ) - s)))) 0) :=
        mul_le_mul_of_nonneg_left (hnorm.trans hMle) hcc.le
    _ ≤ _ := hfin.trans (le_of_eq (by rw [hS]; ring))

end HRS.Commutator.Stj
