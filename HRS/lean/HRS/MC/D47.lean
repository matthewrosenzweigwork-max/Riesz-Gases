import HRS.MC.D47Aux7

/-!
# Packet D47: Lemmas D.4 (`fdl_compare`), D.5 (`fdl_ito`) and Remark D.7 (`fdl_scope`) of `HRS/Appendix/FDL.lean`.

The three theorems `fdl_compare_proof`, `fdl_ito_proof`, `fdl_scope_proof` are tied to the frozen statements by
`type_of%`; they are derived from the master lemma `d47_master` (all `η ∈ [λ, Rλ]`).
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.MC.D47

open HRS HRS.MC.FDLE HRS.MC.Per HRS.MC.D3T1 HRS.MC.D3T3 HRS.StaticLimitAux

variable {d : ℕ}

lemma d47_pairW_nonneg {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {s b η : ℝ} (hb0 : 0 ≤ b) {N : ℕ}
    (X : Config d N) : 0 ≤ fdlPairW ψ s b η X := by
  unfold fdlPairW
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_)
  exact d47_fdlWT_nonneg hψ hb0 _

lemma d47_arith {C₁ K₁ B F Fη Fl Pη Pl Eη El L a Tη W : ℝ}
    (hC₁ : 0 ≤ C₁) (hK₁ : 0 ≤ K₁) (hB : 0 ≤ B) (ha0 : 0 ≤ a) (hL0 : 0 ≤ L)
    (hlowη : -(L + C₁ * a) ≤ Fη) (hlowl : -(L + C₁ * a) ≤ Fl)
    (hPη0 : 0 ≤ Pη) (hPl0 : 0 ≤ Pl)
    (hEη1 : -2 * Tη ≤ Eη) (hEη2 : Eη ≤ Tη) (hFη : F = Fη + 1 / 2 * (Pη + Eη))
    (hEl1 : -2 * (K₁ * a) ≤ El) (hFl : F = Fl + 1 / 2 * (Pl + El))
    (hTη : Tη ≤ B * a) (hTη0 : 0 ≤ Tη) (hTW : Tη = K₁ * W) (hW : 0 ≤ W) :
    0 ≤ Fη + (L + (C₁ + K₁ + 1) * a) ∧
    (0 ≤ Pη ∧ Pη ≤ (3 + 2 * B + K₁) * (F + (L + (C₁ + K₁ + 1) * a))) ∧
    (|F - Fη - 1 / 2 * Pη| ≤ (3 + 2 * B + K₁) * W ∧
      Fη + (L + (C₁ + K₁ + 1) * a) ≤ (3 + 2 * B + K₁) * (F + (L + (C₁ + K₁ + 1) * a)) ∧
      Fη - (3 + 2 * B + K₁) * (L + (C₁ + K₁ + 1) * a) ≤ F) ∧
    0 ≤ F + (L + (C₁ + K₁ + 1) * a) ∧ 0 ≤ L + (C₁ + K₁ + 1) * a := by
  have hFo : a ≤ F + (L + (C₁ + K₁ + 1) * a) := by nlinarith
  have hFo0 : 0 ≤ F + (L + (C₁ + K₁ + 1) * a) := le_trans ha0 hFo
  have hKW : 0 ≤ K₁ * W := mul_nonneg hK₁ hW
  refine ⟨?_, ⟨hPη0, ?_⟩, ⟨?_, ?_, ?_⟩, hFo0, add_nonneg hL0 (mul_nonneg (by linarith) ha0)⟩
  · nlinarith [mul_nonneg (by linarith : 0 ≤ K₁ + 1) ha0]
  · have h1 : Pη ≤ 2 * (F + (L + (C₁ + K₁ + 1) * a)) + 2 * (B * a) := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ K₁ + 1) ha0]
    have h2 : 2 * B * a ≤ 2 * B * (F + (L + (C₁ + K₁ + 1) * a)) :=
      mul_le_mul_of_nonneg_left hFo (by linarith)
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + K₁) hFo0]
  · rw [abs_le]
    constructor <;> nlinarith [mul_nonneg (by linarith : 0 ≤ 2 + 2 * B) hW,
      mul_nonneg (by linarith : 0 ≤ 3 + 2 * B) hKW]
  · have h2 : B * a ≤ B * (F + (L + (C₁ + K₁ + 1) * a)) :=
      mul_le_mul_of_nonneg_left hFo hB
    nlinarith [mul_nonneg (by linarith : 0 ≤ 2 + B + K₁) hFo0]
  · have h2 : B * a ≤ (3 + 2 * B + K₁) * ((C₁ + K₁ + 1) * a) := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ 3 + B + K₁) ha0,
        mul_nonneg (mul_nonneg hB hC₁) ha0, mul_nonneg (mul_nonneg hB hK₁) ha0,
        mul_nonneg (mul_nonneg hK₁ hK₁) ha0, mul_nonneg (mul_nonneg hK₁ hC₁) ha0,
        mul_nonneg (mul_nonneg hB hB) ha0]
    have h3 : 0 ≤ (3 + 2 * B + K₁) * L := mul_nonneg (by linarith) hL0
    nlinarith

theorem d47_master (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {R : ℝ} (hR : 1 ≤ R) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 1 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
      ∀ η : ℝ, smearScale d N Λ ≤ η → η ≤ R * smearScale d N Λ →
        0 ≤ fdlEnergy ψ s b η X (withDensityReal ρ) + oNΛ d s C₀ Λ N ∧
        (0 ≤ fdlPairW ψ s b η X ∧
          fdlPairW ψ s b η X ≤ C * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N)) ∧
        (|rieszEnergy d s X (withDensityReal ρ) - fdlEnergy ψ s b η X (withDensityReal ρ)
            - (1 / 2) * fdlPairW ψ s b η X| ≤ C * Λ * η ^ ((d : ℝ) - s) ∧
          fdlEnergy ψ s b η X (withDensityReal ρ) + oNΛ d s C₀ Λ N
            ≤ C * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N) ∧
          fdlEnergy ψ s b η X (withDensityReal ρ) - C * oNΛ d s C₀ Λ N
            ≤ rieszEnergy d s X (withDensityReal ρ)) ∧
        0 ≤ rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N ∧ 0 ≤ oNΛ d s C₀ Λ N := by
  obtain ⟨C₁, hC₁, hlow⟩ := d47_lowerB hd hs0 hsd hψ hb
  have hds : 0 < (d : ℝ) - s := by linarith
  have hb0 : 0 < b := hb.1
  set K₁ : ℝ := b * (∫ y, fdlPhi ψ y) / ((d : ℝ) - s) with hK₁
  have hK₁0 : 0 ≤ K₁ := by
    have : 0 ≤ ∫ y, fdlPhi ψ y := integral_nonneg (fdle_phi_nonneg hψ)
    positivity
  have hR0 : 0 ≤ R := by linarith
  set B : ℝ := K₁ * R ^ ((d : ℝ) - s) with hB
  have hB0 : 0 ≤ B := mul_nonneg hK₁0 (Real.rpow_nonneg hR0 _)
  refine ⟨C₁ + K₁ + 1, 3 + 2 * B + K₁, by positivity, by positivity, ?_⟩
  intro Λ hΛ N hN ρ hρ hρΛ X hX η hη1 hη2
  have hlam0 : 0 < smearScale d N Λ := d47_lam_pos hN hΛ
  have hη0 : 0 < η := lt_of_lt_of_le hlam0 hη1
  have hΛ0 : 0 ≤ Λ := by linarith
  set a : ℝ := Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1) with ha
  have ha0 : 0 ≤ a := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    positivity
  set L : ℝ := (if s = 0 then Real.log ((N : ℝ) * Λ) / (2 * d * N) else 0) with hL
  have hL0 : 0 ≤ L := by
    rw [hL]; split_ifs
    · have := d47_log_nonneg hN hΛ
      positivity
    · exact le_rfl
  have hoN : oNΛ d s (C₁ + K₁ + 1) Λ N = L + (C₁ + K₁ + 1) * a := by
    unfold oNΛ; rw [hL, ha]; ring
  set F := rieszEnergy d s X (withDensityReal ρ) with hF
  set Fη := fdlEnergy ψ s b η X (withDensityReal ρ) with hFη
  set Fl := fdlEnergy ψ s b (smearScale d N Λ) X (withDensityReal ρ) with hFl
  have hlowη : -(L + C₁ * a) ≤ Fη := hlow Λ hΛ N hN ρ hρ X η hη1
  have hlowl : -(L + C₁ * a) ≤ Fl := hlow Λ hΛ N hN ρ hρ X _ le_rfl
  obtain ⟨Eη, hEη1, hEη2, hFη⟩ := d47_decomp hd hs0 hsd hψ hb hη0 hΛ hN hρ hρΛ hX
  obtain ⟨El, hEl1, hEl2, hFl'⟩ := d47_decomp hd hs0 hsd hψ hb hlam0 hΛ hN hρ hρΛ hX
  have hPη0 := d47_pairW_nonneg (ψ := ψ) (s := s) hψ hb0.le (η := η) X
  have hPl0 := d47_pairW_nonneg (ψ := ψ) (s := s) hψ hb0.le (η := smearScale d N Λ) X
  -- the sizes of `Λ κ`
  have hκη : Λ * d47_kappa ψ s b η = K₁ * (Λ * η ^ ((d : ℝ) - s)) := by
    rw [d47_kappa_eq]; ring
  have hκl : Λ * d47_kappa ψ s b (smearScale d N Λ) = K₁ * a := by
    rw [d47_kappa_eq, ha, ← d47_Lam_lam hd hN hΛ]; ring
  have hηle : η ^ ((d : ℝ) - s) ≤ (R * smearScale d N Λ) ^ ((d : ℝ) - s) :=
    Real.rpow_le_rpow hη0.le hη2 hds.le
  have hTη : Λ * d47_kappa ψ s b η ≤ B * a := by
    rw [hκη]
    calc K₁ * (Λ * η ^ ((d : ℝ) - s)) ≤ K₁ * (Λ * (R * smearScale d N Λ) ^ ((d : ℝ) - s)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hηle hΛ0) hK₁0
      _ = B * a := by
          rw [Real.mul_rpow hR0 hlam0.le, ha, ← d47_Lam_lam hd hN hΛ, hB]; ring
  have hTη0 : 0 ≤ Λ * d47_kappa ψ s b η := mul_nonneg hΛ0 (d47_kappa_nonneg hsd hψ hb0.le hη0)
  have hTW : Λ * d47_kappa ψ s b η = K₁ * (Λ * η ^ ((d : ℝ) - s)) := hκη
  have hW : 0 ≤ Λ * η ^ ((d : ℝ) - s) := mul_nonneg hΛ0 (Real.rpow_nonneg hη0.le _)
  have hEl1' : -2 * (K₁ * a) ≤ El := by
    have := hEl1; rw [hκl] at this; linarith
  have key := d47_arith hC₁ hK₁0 hB0 ha0 hL0 hlowη hlowl hPη0 hPl0 hEη1 hEη2 hFη hEl1' hFl' hTη
    hTη0 hTW hW
  rw [hoN]
  obtain ⟨k1, k2, ⟨k3, k4, k5⟩, k6, k7⟩ := key
  refine ⟨k1, k2, ⟨?_, k4, k5⟩, k6, k7⟩
  calc |F - Fη - 1 / 2 * fdlPairW ψ s b η X| ≤ (3 + 2 * B + K₁) * (Λ * η ^ ((d : ℝ) - s)) := k3
    _ = (3 + 2 * B + K₁) * Λ * η ^ ((d : ℝ) - s) := by ring

lemma d47_two_fdlK : 1 ≤ 2 * fdlK := by unfold fdlK; norm_num

lemma d47_one_le_mul {x R : ℝ} (hx : 0 < x) (hR : 1 ≤ R) : x ≤ R * x := by nlinarith

/-- Lemma D.4 (`fdl_compare`), proved. -/
theorem fdl_compare_proof (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 1 ≤ N → smearScale d N Λ < 1 / 2 →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
        (∀ η : ℝ, smearScale d N Λ ≤ η → η ≤ 2 * fdlK * smearScale d N Λ →
          0 ≤ fdlEnergy ψ s b η X (withDensityReal ρ) + oNΛ d s C₀ Λ N) ∧
        (∀ η : ℝ, smearScale d N Λ ≤ η → η ≤ 2 * fdlK * smearScale d N Λ →
          0 ≤ fdlPairW ψ s b η X ∧
          fdlPairW ψ s b η X ≤ C * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N)) ∧
        (|rieszEnergy d s X (withDensityReal ρ) - fdlEnergy ψ s b (smearScale d N Λ) X (withDensityReal ρ)
            - (1 / 2) * fdlPairW ψ s b (smearScale d N Λ) X|
          ≤ C * Λ * smearScale d N Λ ^ ((d : ℝ) - s) ∧
        fdlEnergy ψ s b (smearScale d N Λ) X (withDensityReal ρ) + oNΛ d s C₀ Λ N
          ≤ C * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N) ∧
        fdlEnergy ψ s b (smearScale d N Λ) X (withDensityReal ρ) - C * oNΛ d s C₀ Λ N
          ≤ rieszEnergy d s X (withDensityReal ρ)) := by
  obtain ⟨C₀, C, hC₀, hC, h⟩ := d47_master hd hs0 hsd hψ hb d47_two_fdlK
  refine ⟨C₀, C, hC₀, hC, fun Λ hΛ N hN _ ρ hρ hρΛ X hX => ?_⟩
  have H := fun η h1 h2 => h Λ hΛ N hN ρ hρ hρΛ X hX η h1 h2
  refine ⟨fun η h1 h2 => (H η h1 h2).1, fun η h1 h2 => (H η h1 h2).2.1, ?_⟩
  exact (H _ le_rfl (d47_one_le_mul (d47_lam_pos hN hΛ) d47_two_fdlK)).2.2.1

example := (@fdl_compare_proof : type_of% @HRS.fdl_compare)

/-- Lemma D.5 (`fdl_ito`), proved. -/
theorem fdl_ito_proof (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 1 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
        offDiagPairing (fun x y => Torus.laplacian (fdlTruncT ψ s b (smearScale d N Λ)) (x - y))
            X (withDensityReal ρ)
          ≤ |Torus.laplacian (fdlTruncT ψ s b (smearScale d N Λ)) 0| / N ∧
        |Torus.laplacian (fdlTruncT ψ s b (smearScale d N Λ)) 0| / N
          ≤ C * Λ ^ ((s + 2) / d) * (N : ℝ) ^ ((s + 2) / d - 1) := by
  obtain ⟨C, hC, h⟩ := d47_ito hd hs0 hsd hψ hb
  exact ⟨C, hC, fun Λ hΛ N hN ρ hρ _ X _ => h Λ hΛ N hN ρ hρ X _ le_rfl⟩

example := (@fdl_ito_proof : type_of% @HRS.fdl_ito)

/-- Remark D.7 (`fdl_scope`), proved. -/
theorem fdl_scope_proof (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {R : ℝ} (hR : 1 ≤ R) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 1 ≤ N → smearScale d N Λ < 1 / 2 →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
      ∀ η : ℝ, smearScale d N Λ ≤ η → η ≤ R * smearScale d N Λ → η < 1 →
        0 ≤ fdlEnergy ψ s b η X (withDensityReal ρ) + oNΛ d s C₀ Λ N ∧
        (0 ≤ fdlPairW ψ s b η X ∧
          fdlPairW ψ s b η X ≤ C * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N)) ∧
        (|rieszEnergy d s X (withDensityReal ρ) - fdlEnergy ψ s b η X (withDensityReal ρ)
            - (1 / 2) * fdlPairW ψ s b η X| ≤ C * Λ * η ^ ((d : ℝ) - s) ∧
          fdlEnergy ψ s b η X (withDensityReal ρ) + oNΛ d s C₀ Λ N
            ≤ C * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N) ∧
          fdlEnergy ψ s b η X (withDensityReal ρ) - C * oNΛ d s C₀ Λ N
            ≤ rieszEnergy d s X (withDensityReal ρ)) ∧
        (offDiagPairing (fun x y => Torus.laplacian (fdlTruncT ψ s b η) (x - y)) X (withDensityReal ρ)
            ≤ |Torus.laplacian (fdlTruncT ψ s b η) 0| / N ∧
          |Torus.laplacian (fdlTruncT ψ s b η) 0| / N
            ≤ C * Λ ^ ((s + 2) / d) * (N : ℝ) ^ ((s + 2) / d - 1)) := by
  obtain ⟨C₀, C, hC₀, hC, h⟩ := d47_master hd hs0 hsd hψ hb hR
  obtain ⟨C₂, hC₂, hito⟩ := d47_ito hd hs0 hsd hψ hb
  refine ⟨C₀, max C C₂, hC₀, lt_max_of_lt_left hC, fun Λ hΛ N hN _ ρ hρ hρΛ X hX η h1 h2 _ => ?_⟩
  obtain ⟨k1, ⟨k2, k3⟩, ⟨k4, k5, k6⟩, hFo, ho⟩ := h Λ hΛ N hN ρ hρ hρΛ X hX η h1 h2
  have hm : C ≤ max C C₂ := le_max_left _ _
  have hlam := d47_lam_pos (d := d) hN hΛ
  have hη0 : 0 < η := lt_of_lt_of_le hlam h1
  have hΛ0 : 0 ≤ Λ := by linarith
  have hW : 0 ≤ Λ * η ^ ((d : ℝ) - s) := mul_nonneg hΛ0 (Real.rpow_nonneg hη0.le _)
  refine ⟨k1, ⟨k2, k3.trans (mul_le_mul_of_nonneg_right hm hFo)⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · refine k4.trans ?_
    have := mul_le_mul_of_nonneg_right hm hW
    nlinarith
  · exact k5.trans (mul_le_mul_of_nonneg_right hm hFo)
  · have := mul_le_mul_of_nonneg_right hm ho
    linarith
  · obtain ⟨i1, i2⟩ := hito Λ hΛ N hN ρ hρ X η h1
    refine ⟨i1, i2.trans ?_⟩
    have hpos : 0 ≤ Λ ^ ((s + 2) / d) * (N : ℝ) ^ ((s + 2) / d - 1) := by
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      positivity
    have := mul_le_mul_of_nonneg_right (le_max_right C C₂) hpos
    nlinarith

example := (@fdl_scope_proof : type_of% @HRS.fdl_scope)

end HRS.MC.D47
