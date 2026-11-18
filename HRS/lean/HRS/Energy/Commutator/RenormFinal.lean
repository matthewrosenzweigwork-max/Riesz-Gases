import HRS.Energy.Commutator.RenormCoulMain
import HRS.Energy.Commutator.Coerc0

/-!
# Route S, packet S4: the Coulomb case, final assembly
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.Renorm

variable {d : ℕ}

theorem aN_eq (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ) {N : ℕ} (hN : 0 < N) :
    aNΛ d ((d : ℝ) - 2) Λ N = Λ * (smearScale d N Λ) ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  unfold aNΛ smearScale
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.mul_rpow hNr.le hΛ.le]
  have e1 : ((d : ℝ) - 2) / d = 1 - 2 / d := by field_simp
  have e3 : -1 / (d : ℝ) * ((2 : ℕ) : ℝ) = -(2 / d) := by push_cast; ring
  rw [e1, e3]
  have e2 : 1 - 2 / (d : ℝ) - 1 = -(2 / d) := by ring
  rw [e2]
  have : Λ ^ (1 - 2 / (d : ℝ)) = Λ * Λ ^ (-(2 / (d : ℝ))) := by
    rw [sub_eq_add_neg, Real.rpow_add hΛ, Real.rpow_one]
  rw [this]
  ring

theorem inv_le_aN (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ) {N : ℕ} (hN : 0 < N) :
    1 / (N : ℝ) ≤ aNΛ d ((d : ℝ) - 2) Λ N := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hs : (0 : ℝ) ≤ ((d : ℝ) - 2) / d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    apply div_nonneg <;> linarith
  unfold aNΛ
  have h1 : (1 : ℝ) ≤ Λ ^ (((d : ℝ) - 2) / d) := Real.one_le_rpow hΛ hs
  have h2 : 1 / (N : ℝ) ≤ (N : ℝ) ^ (((d : ℝ) - 2) / d - 1) := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
  calc 1 / (N : ℝ) ≤ (N : ℝ) ^ (((d : ℝ) - 2) / d - 1) := h2
    _ = 1 * (N : ℝ) ^ (((d : ℝ) - 2) / d - 1) := (one_mul _).symm
    _ ≤ Λ ^ (((d : ℝ) - 2) / d) * (N : ℝ) ^ (((d : ℝ) - 2) / d - 1) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)

theorem eta_sq_sum (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ) {N : ℕ} (hN : 0 < N) {ξ : Fin N → ℝ}
    (hξ0 : ∀ i, 0 ≤ ξ i) (hξ : ∀ i, ξ i ≤ smearScale d N Λ) :
    (1 / (N : ℝ)) * Λ * ∑ i, ξ i ^ 2 ≤ aNΛ d ((d : ℝ) - 2) Λ N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [aN_eq hd hΛ hN]
  have h1 : ∑ i, ξ i ^ 2 ≤ ∑ _i : Fin N, (smearScale d N Λ) ^ 2 :=
    Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (hξ0 i) (hξ i) 2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  calc (1 / (N : ℝ)) * Λ * ∑ i, ξ i ^ 2 ≤ (1 / (N : ℝ)) * Λ * (N * smearScale d N Λ ^ 2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = Λ * smearScale d N Λ ^ 2 := by field_simp

theorem selfExcess_nonneg (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ) {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 0 < r)
    (hrl : r ≤ smearScale d N Λ / 8) : 0 ≤ selfExcess d ((d : ℝ) - 2) Λ N r := by
  unfold selfExcess
  split_ifs
  · have hlam : 0 < smearScale d N Λ := CoercAux.smearScale_pos hN hΛ
    apply Real.log_nonneg
    rw [le_div_iff₀ hr]
    linarith
  · exact Real.rpow_nonneg hr.le _

theorem selfScale_conv_ge3 (hd : 3 ≤ d) {Λ : ℝ} {N : ℕ} {r η θ : ℝ} (hr : 0 < r) (hθ : 0 < θ)
    (hη : r / θ ≤ η) : selfScale d ((d : ℝ) - 2) η ≤ θ ^ ((d : ℝ) - 2) * selfExcess d ((d : ℝ) - 2) Λ N r := by
  have hs : (d : ℝ) - 2 ≠ 0 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hs0 : 0 < (d : ℝ) - 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hη
  unfold selfScale selfExcess
  rw [if_neg hs, if_neg hs]
  have h1 : η ^ (-((d : ℝ) - 2)) = (η⁻¹) ^ ((d : ℝ) - 2) := by
    rw [Real.rpow_neg hη0.le, Real.inv_rpow hη0.le]
  have h2 : r ^ (-((d : ℝ) - 2)) = (r⁻¹) ^ ((d : ℝ) - 2) := by
    rw [Real.rpow_neg hr.le, Real.inv_rpow hr.le]
  rw [h1, h2, ← Real.mul_rpow (by positivity) (by positivity)]
  refine Real.rpow_le_rpow (by positivity) ?_ hs0.le
  have : η⁻¹ ≤ (r / θ)⁻¹ := inv_anti₀ (by positivity) hη
  calc η⁻¹ ≤ (r / θ)⁻¹ := this
    _ = θ * r⁻¹ := by rw [inv_div, div_eq_mul_inv]

theorem selfScale_conv_two (hd : d = 2) {Λ : ℝ} (hΛ : 0 < Λ) {N : ℕ} (hN : 0 < N) {r η θ : ℝ} (hr : 0 < r)
    (hθ : 0 < θ) (hη : r / θ ≤ η) :
    selfScale d ((d : ℝ) - 2) η ≤ selfExcess d ((d : ℝ) - 2) Λ N r + Real.log θ + 1 / d * Real.log (N * Λ) := by
  have hs : (d : ℝ) - 2 = 0 := by rw [hd]; norm_num
  have hη0 : 0 < η := lt_of_lt_of_le (by positivity) hη
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hlam : 0 < smearScale d N Λ := CoercAux.smearScale_pos hN hΛ
  unfold selfScale selfExcess
  rw [if_pos hs, if_pos hs]
  have h1 : Real.log (r / θ) ≤ Real.log η := Real.log_le_log (by positivity) hη
  have h2 : Real.log (r / θ) = Real.log r - Real.log θ := Real.log_div hr.ne' hθ.ne'
  have h3 : Real.log (smearScale d N Λ / r) = Real.log (smearScale d N Λ) - Real.log r :=
    Real.log_div hlam.ne' hr.ne'
  have h4 : Real.log (smearScale d N Λ) = -(1 / d) * Real.log (N * Λ) := by
    unfold smearScale
    rw [Real.log_rpow (by positivity)]
    ring
  rw [h3, h4]
  linarith

theorem alg_d2 {c CQ Cb Ca Cw C₂ K2 M₁ F0 SS SS0 KK KK0 Hh Tt u a lp S ZZ ZZ0 R : ℝ}
    (hc : 0 < c) (hCQ : 0 ≤ CQ) (hCb : 0 ≤ Cb) (hCa : 0 ≤ Ca) (hCw : 0 ≤ Cw) (hK2 : 0 ≤ K2) (hM : 0 ≤ M₁)
    (hR : R = c * F0) (hTt : Tt = u) (hu : u ≤ a) (hKK : KK ≤ a) (hKK0 : KK0 ≤ a) (hH : Hh ≤ 2 * M₁ * a)
    (hSS : c * SS ≤ ZZ + c * C₂ * u) (hSS0 : c * SS0 ≤ ZZ0 + c * C₂ * u)
    (hZZ : ZZ ≤ S + u * Real.log 2 + 2 * lp) (hZZ0 : ZZ0 ≤ S + u * Real.log 4 + 2 * lp)
    (hl2 : 0 ≤ Real.log 2) (hl4 : 0 ≤ Real.log 4) (hu0 : 0 ≤ u) (hC₂ : 0 ≤ C₂) :
    c * (CQ * (2 * F0 + SS + KK) + Cb * (2 * (2 * F0 + SS0 + KK0) + 2 * Cw * Tt) + Ca * Tt + (K2 * u + Hh)) ≤
      (2 * CQ + 4 * Cb) * (R + lp) + (CQ + 2 * Cb) * S +
        (CQ * Real.log 2 + 2 * Cb * Real.log 4 + (CQ + 2 * Cb) * c * C₂ +
          c * (CQ + 2 * Cb + 2 * Cb * Cw + Ca + K2 + 2 * M₁)) * a := by
  rw [hTt]
  have e1 : c * (CQ * (2 * F0 + SS + KK) + Cb * (2 * (2 * F0 + SS0 + KK0) + 2 * Cw * u) + Ca * u + (K2 * u + Hh)) =
      (2 * CQ + 4 * Cb) * (c * F0) + CQ * (c * SS) + 2 * Cb * (c * SS0) +
        c * (CQ * KK + 2 * Cb * KK0 + (2 * Cb * Cw + Ca + K2) * u + Hh) := by ring
  rw [e1, ← hR]
  have h1 := mul_le_mul_of_nonneg_left hSS hCQ
  have h2 := mul_le_mul_of_nonneg_left hSS0 (by positivity : 0 ≤ 2 * Cb)
  have h3 := mul_le_mul_of_nonneg_left hZZ hCQ
  have h4 := mul_le_mul_of_nonneg_left hZZ0 (by positivity : 0 ≤ 2 * Cb)
  have h5 : c * (CQ * KK + 2 * Cb * KK0 + (2 * Cb * Cw + Ca + K2) * u + Hh) ≤
      c * (CQ * a + 2 * Cb * a + (2 * Cb * Cw + Ca + K2) * a + 2 * M₁ * a) := by
    apply mul_le_mul_of_nonneg_left _ hc.le
    have := mul_le_mul_of_nonneg_left hKK hCQ
    have := mul_le_mul_of_nonneg_left hKK0 (by positivity : 0 ≤ 2 * Cb)
    have := mul_le_mul_of_nonneg_right hu (by positivity : 0 ≤ 2 * Cb * Cw + Ca + K2)
    linarith
  have h6 : u * (CQ * Real.log 2) ≤ a * (CQ * Real.log 2) :=
    mul_le_mul_of_nonneg_right hu (by positivity)
  have h7 : u * (2 * Cb * Real.log 4) ≤ a * (2 * Cb * Real.log 4) :=
    mul_le_mul_of_nonneg_right hu (by positivity)
  have h8 : u * ((CQ + 2 * Cb) * c * C₂) ≤ a * ((CQ + 2 * Cb) * c * C₂) :=
    mul_le_mul_of_nonneg_right hu (by positivity)
  nlinarith [h1, h2, h3, h4, h5, h6, h7, h8]

theorem alg_ge3 {c CQ Cb Ca Cw C₂ Cs J0 M₁ F0 SS SS0 KK KK0 Hh Tt u a S ZZ ZZ0 R P2 P4 : ℝ}
    (hc : 0 < c) (hCQ : 0 ≤ CQ) (hCb : 0 ≤ Cb) (hCa : 0 ≤ Ca) (hCw : 0 ≤ Cw) (hCs : 0 ≤ Cs) (hM : 0 ≤ M₁)
    (hJ0 : 0 ≤ J0) (hC₂ : 0 ≤ C₂)
    (hR : R = c * F0) (hTt : Tt = S) (hu : u ≤ a) (hKK : KK ≤ a) (hKK0 : KK0 ≤ a) (hH : Hh ≤ 2 * M₁ * a)
    (hSS : c * SS ≤ ZZ + c * C₂ * u) (hSS0 : c * SS0 ≤ ZZ0 + c * C₂ * u)
    (hZZ : ZZ ≤ P2 * S) (hZZ0 : ZZ0 ≤ P4 * S) (hu0 : 0 ≤ u) :
    c * (CQ * (2 * F0 + SS + KK) + Cb * (2 * (2 * F0 + SS0 + KK0) + 2 * Cw * Tt) + Ca * Tt +
        (Cs * SS + 2 * J0 * u + Hh)) ≤
      (2 * CQ + 4 * Cb) * R + (CQ * P2 + 2 * Cb * P4 + c * (2 * Cb * Cw + Ca) + Cs * P2) * S +
        ((CQ + 2 * Cb + Cs) * c * C₂ + 2 * c * J0 + c * (CQ + 2 * Cb + 2 * M₁)) * a := by
  rw [hTt]
  have e1 : c * (CQ * (2 * F0 + SS + KK) + Cb * (2 * (2 * F0 + SS0 + KK0) + 2 * Cw * S) + Ca * S +
        (Cs * SS + 2 * J0 * u + Hh)) =
      (2 * CQ + 4 * Cb) * (c * F0) + CQ * (c * SS) + 2 * Cb * (c * SS0) + Cs * (c * SS) +
        c * (CQ * KK + 2 * Cb * KK0 + (2 * Cb * Cw + Ca) * S + 2 * J0 * u + Hh) := by ring
  rw [e1, ← hR]
  have h1 := mul_le_mul_of_nonneg_left hSS hCQ
  have h2 := mul_le_mul_of_nonneg_left hSS0 (by positivity : 0 ≤ 2 * Cb)
  have h2' := mul_le_mul_of_nonneg_left hSS hCs
  have h3 := mul_le_mul_of_nonneg_left hZZ hCQ
  have h4 := mul_le_mul_of_nonneg_left hZZ0 (by positivity : 0 ≤ 2 * Cb)
  have h4' := mul_le_mul_of_nonneg_left hZZ hCs
  have h5 : c * (CQ * KK + 2 * Cb * KK0 + (2 * Cb * Cw + Ca) * S + 2 * J0 * u + Hh) ≤
      c * (CQ * a + 2 * Cb * a + (2 * Cb * Cw + Ca) * S + 2 * J0 * a + 2 * M₁ * a) := by
    apply mul_le_mul_of_nonneg_left _ hc.le
    have := mul_le_mul_of_nonneg_left hKK hCQ
    have := mul_le_mul_of_nonneg_left hKK0 (by positivity : 0 ≤ 2 * Cb)
    have := mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 2 * J0)
    linarith
  have h8 : u * ((CQ + 2 * Cb + Cs) * c * C₂) ≤ a * ((CQ + 2 * Cb + Cs) * c * C₂) :=
    mul_le_mul_of_nonneg_right hu (by positivity)
  nlinarith [h1, h2, h2', h3, h4, h4', h5, h8]

theorem rho2_ge3 (hd : 3 ≤ d) {Λ : ℝ} {N : ℕ} {r : ℝ} (hr : 0 < r) :
    rho2 d r = selfExcess d ((d : ℝ) - 2) Λ N r := by
  have hs : (d : ℝ) - 2 ≠ 0 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  unfold selfExcess rho2
  rw [if_neg hs]
  have h1 : r ^ (-((d : ℝ) - 2)) = (r ^ (d - 2))⁻¹ := by
    rw [Real.rpow_neg hr.le, ← Real.rpow_natCast]
    congr 2
    rw [Nat.cast_sub (by omega)]; norm_num
  rw [h1]
  have h2 : r ^ (d - 1) = r * r ^ (d - 2) := by
    rw [← pow_succ']; congr 1; omega
  rw [h2]
  have : r ^ (d - 2) ≠ 0 := (pow_pos hr _).ne'
  field_simp

theorem rho2_two (hd : d = 2) {r : ℝ} (hr : 0 < r) : rho2 d r = 1 := by
  subst hd
  unfold rho2
  simp [hr.ne']

theorem Jl_nonneg (l : ℝ) : 0 ≤ Jl d l :=
  integral_nonneg fun z => mul_nonneg (KernelGrad.tdist_nonneg z 0) (norm_nonneg _)

theorem logPart_ge3 (hd : 3 ≤ d) (Λ : ℝ) (N : ℕ) : logPart d ((d : ℝ) - 2) Λ N = 0 := by
  have hs : (d : ℝ) - 2 ≠ 0 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  unfold logPart
  rw [if_neg hs]

theorem SS_le {N : ℕ} (hN : 0 < N) {c C₂ : ℝ} (hc : 0 < c) {sc : ℝ → ℝ} {ξ : Fin N → ℝ}
    (hξ : ∀ i, S0 d (ξ i) ≤ c⁻¹ * sc (ξ i) + C₂) :
    c * ((1 / (N : ℝ)) ^ 2 * ∑ i, S0 d (ξ i)) ≤ (1 / (N : ℝ)) ^ 2 * ∑ i, sc (ξ i) + c * C₂ * (1 / (N : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ∑ i, S0 d (ξ i) ≤ ∑ i, (c⁻¹ * sc (ξ i) + C₂) := Finset.sum_le_sum fun i _ => hξ i
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ c * (1 / (N : ℝ)) ^ 2)
  calc c * ((1 / (N : ℝ)) ^ 2 * ∑ i, S0 d (ξ i)) = c * (1 / (N : ℝ)) ^ 2 * ∑ i, S0 d (ξ i) := by ring
    _ ≤ c * (1 / (N : ℝ)) ^ 2 * (c⁻¹ * ∑ i, sc (ξ i) + N * C₂) := h2
    _ = (1 / (N : ℝ)) ^ 2 * ∑ i, sc (ξ i) + c * C₂ * (1 / (N : ℝ)) := by
        field_simp

theorem ZZ_two (hd : d = 2) {Λ : ℝ} (hΛ : 0 < Λ) {N : ℕ} (hN : 0 < N) {r ξ : Fin N → ℝ}
    (hr : ∀ i, 0 < r i) {θ : ℝ} (hθ : 0 < θ) (hξ : ∀ i, r i / θ ≤ ξ i) :
    (1 / (N : ℝ)) ^ 2 * ∑ i, selfScale d ((d : ℝ) - 2) (ξ i) ≤
      (1 / (N : ℝ) ^ 2) * ∑ i, selfExcess d ((d : ℝ) - 2) Λ N (r i) + (1 / (N : ℝ)) * Real.log θ +
        2 * logPart d ((d : ℝ) - 2) Λ N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ∀ i, selfScale d ((d : ℝ) - 2) (ξ i) ≤
      selfExcess d ((d : ℝ) - 2) Λ N (r i) + Real.log θ + 1 / d * Real.log (N * Λ) := fun i =>
    selfScale_conv_two hd hΛ hN (hr i) hθ (hξ i)
  have h2 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h1 i
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (1 / (N : ℝ)) ^ 2)
  have hs : (d : ℝ) - 2 = 0 := by rw [hd]; norm_num
  have hlp : logPart d ((d : ℝ) - 2) Λ N = Real.log (N * Λ) / (2 * d * N) := by
    unfold logPart; rw [if_pos hs]
  rw [hlp]
  have hd0 : (d : ℝ) ≠ 0 := by rw [hd]; norm_num
  refine h3.trans (le_of_eq ?_)
  field_simp

theorem ZZ_ge3 (hd : 3 ≤ d) {Λ : ℝ} {N : ℕ} (hN : 0 < N) {r ξ : Fin N → ℝ}
    (hr : ∀ i, 0 < r i) {θ : ℝ} (hθ : 0 < θ) (hξ : ∀ i, r i / θ ≤ ξ i) :
    (1 / (N : ℝ)) ^ 2 * ∑ i, selfScale d ((d : ℝ) - 2) (ξ i) ≤
      θ ^ ((d : ℝ) - 2) * ((1 / (N : ℝ) ^ 2) * ∑ i, selfExcess d ((d : ℝ) - 2) Λ N (r i)) := by
  have h1 : ∀ i, selfScale d ((d : ℝ) - 2) (ξ i) ≤ θ ^ ((d : ℝ) - 2) * selfExcess d ((d : ℝ) - 2) Λ N (r i) :=
    fun i => selfScale_conv_ge3 hd (hr i) hθ (hξ i)
  have h2 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h1 i
  rw [← Finset.mul_sum] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (1 / (N : ℝ)) ^ 2)
  refine h3.trans (le_of_eq ?_)
  rw [one_div_pow]; ring

set_option maxHeartbeats 4000000 in
theorem coulomb_final_ineq (hd : 2 ≤ d) :
    ∃ A2 γS γa : ℝ, 0 ≤ A2 ∧ 0 ≤ γS ∧ 0 ≤ γa ∧
    ∀ {N : ℕ} (hN : 2 ≤ N) {Λ : ℝ} (hΛ : 1 ≤ Λ) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (hρΛ : ∀ x, ρ x ≤ Λ)
      {X : Config d N} (hX : X ∉ collisionSet d N) {L : ℝ} (hL : 0 ≤ L) {v : Torus d → Euc d}
      (hv : IsLipschitzVF L v),
      |commQuantity d ((d : ℝ) - 2) v X (withDensityReal ρ)| ≤ L * (
        A2 * (rieszEnergy d ((d : ℝ) - 2) X (withDensityReal ρ) + logPart d ((d : ℝ) - 2) Λ N) +
        γS * ((1 / (N : ℝ) ^ 2) * ∑ i, selfExcess d ((d : ℝ) - 2) Λ N (smearRadius Λ X i)) +
        γa * aNΛ d ((d : ℝ) - 2) Λ N) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨CQ, Cs, K2, M₁, Cw, ω, hCQ, hCs, hK2, hM₁, hCw, hω, hmaster⟩ := coulomb_master hd
  obtain ⟨C₂, hC₂, hS0⟩ := S0_bound hd
  have hc : 0 < cC d := cC_pos hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hCb0 : 0 ≤ (2 : ℝ) ^ d / (d * ω) := by positivity
  have hCa0 : 0 ≤ (2 : ℝ) ^ d / d := by positivity
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h2s : 0 ≤ (2 : ℝ) ^ ((d : ℝ) - 2) := Real.rpow_nonneg (by norm_num) _
  have h4s : 0 ≤ (4 : ℝ) ^ ((d : ℝ) - 2) := Real.rpow_nonneg (by norm_num) _
  have hJ0 : 0 ≤ Jl d 0 := Jl_nonneg 0
  refine ⟨2 * CQ + 4 * ((2 : ℝ) ^ d / (d * ω)),
    (CQ + 2 * ((2 : ℝ) ^ d / (d * ω))) + (CQ * 2 ^ ((d : ℝ) - 2) + 2 * ((2 : ℝ) ^ d / (d * ω)) * 4 ^ ((d : ℝ) - 2) +
      cC d * (2 * ((2 : ℝ) ^ d / (d * ω)) * Cw + (2 : ℝ) ^ d / d) + Cs * 2 ^ ((d : ℝ) - 2)),
    (CQ * Real.log 2 + 2 * ((2 : ℝ) ^ d / (d * ω)) * Real.log 4 + (CQ + 2 * ((2 : ℝ) ^ d / (d * ω))) * cC d * C₂ +
      cC d * (CQ + 2 * ((2 : ℝ) ^ d / (d * ω)) + 2 * ((2 : ℝ) ^ d / (d * ω)) * Cw + (2 : ℝ) ^ d / d + K2 + 2 * M₁)) +
    ((CQ + 2 * ((2 : ℝ) ^ d / (d * ω)) + Cs) * cC d * C₂ + 2 * cC d * Jl d 0 +
      cC d * (CQ + 2 * ((2 : ℝ) ^ d / (d * ω)) + 2 * M₁)),
    by positivity, by positivity, by positivity, ?_⟩
  intro N hN Λ hΛ ρ hρ hρΛ X hX L hL v hv
  obtain ⟨η, hη, hbound⟩ := hmaster hN hΛ hρ hρΛ hX hL hv
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hΛ0 : 0 < Λ := by linarith
  set μ := withDensityReal ρ with hμdef
  haveI : IsProbabilityMeasure μ := isProb_withDensityReal hρ
  have hc' : ENNReal.ofReal Λ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hμ : μ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d)) := withDensityReal_le_smul' hρΛ
  have hX' : ∀ i j, i ≠ j → X i ≠ X j := fun i j hij h => hX ⟨i, j, hij, h⟩
  obtain ⟨hr0, hrl, hr8, hsep⟩ := radii_facts hd1 hN hΛ X hX'
  have hμ0 : ∀ x, μ {x} = 0 := atomless_of_le_vol hd1 hc' hμ
  have hcomm := commQuantity_coulomb hd X μ v
  have hR := rieszEnergy_coulomb hd X hX' μ hμ0
  set c := cC d with hcdef
  set Cb : ℝ := (2 : ℝ) ^ d / (d * ω) with hCb
  set Ca : ℝ := (2 : ℝ) ^ d / d with hCa
  set P0 := offDiagPairing (commKernel (SliceAux.sgv 0) v) X μ with hP0
  set F0 := modulatedEnergyKernel (sliceG d 0) X μ with hF0
  set s : ℝ := (d : ℝ) - 2 with hs
  set u : ℝ := 1 / (N : ℝ) with hu
  set a := aNΛ d s Λ N with ha
  have ha0 : 0 ≤ a := aNΛ_nonneg d s Λ N hΛ0.le
  have hua : u ≤ a := inv_le_aN hd hΛ hN0
  have hu0 : 0 ≤ u := by positivity
  set S : ℝ := (1 / (N : ℝ) ^ 2) * ∑ i, selfExcess d s Λ N (smearRadius Λ X i) with hS
  have hS0' : 0 ≤ S := by
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => ?_)
    exact selfExcess_nonneg hd hΛ0 hN0 (hr0 i) (hrl i)
  set lp := logPart d s Λ N with hlp
  -- the bounds for the radii
  have hlam0 : 0 < smearScale d N Λ := CoercAux.smearScale_pos hN0 hΛ0
  have hηpos : ∀ i, 0 < η i := fun i => by linarith [(hη i).1, hr0 i]
  have hηlam : ∀ i, η i ≤ smearScale d N Λ := fun i => by linarith [(hη i).2, hrl i]
  have hηle : ∀ i, η i ≤ 1 / 8 := fun i => by linarith [(hη i).2, hr8 i]
  have hrlam : ∀ i, smearRadius Λ X i / 4 ≤ smearScale d N Λ := fun i => by
    linarith [hrl i, hr0 i]
  -- `KK`, `KK0`, `Hh`
  have hKKgen : ∀ ξ : Fin N → ℝ, (∀ i, 0 ≤ ξ i) → (∀ i, ξ i ≤ smearScale d N Λ) →
      (2 * Λ / N) * ∑ i, ξ i ^ 2 / (2 * d) ≤ a ∧ 2 * (1 / (N : ℝ)) * Λ * M₁ * ∑ i, ξ i ^ 2 ≤ 2 * M₁ * a := by
    intro ξ h0 hl
    have h := eta_sq_sum hd hΛ0 hN0 h0 hl
    have hsq : 0 ≤ ∑ i, ξ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    constructor
    · rw [← Finset.sum_div]
      have e : (2 * Λ / (N : ℝ)) * ((∑ i, ξ i ^ 2) / (2 * d)) = ((1 / (N : ℝ)) * Λ * ∑ i, ξ i ^ 2) / d := by
        field_simp
      rw [e]
      have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
      calc ((1 / (N : ℝ)) * Λ * ∑ i, ξ i ^ 2) / d ≤ ((1 / (N : ℝ)) * Λ * ∑ i, ξ i ^ 2) / 1 :=
            div_le_div_of_nonneg_left (by positivity) one_pos hd1'
        _ ≤ a := by rw [div_one]; exact h
    · have e : 2 * (1 / (N : ℝ)) * Λ * M₁ * ∑ i, ξ i ^ 2 = 2 * M₁ * ((1 / (N : ℝ)) * Λ * ∑ i, ξ i ^ 2) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left h (by positivity)
  obtain ⟨hKK, hHh⟩ := hKKgen η (fun i => (hηpos i).le) hηlam
  obtain ⟨hKK0, -⟩ := hKKgen (fun i => smearRadius Λ X i / 4) (fun i => by have := hr0 i; positivity) hrlam
  -- the self energies
  have hη0pos : ∀ i, 0 < smearRadius Λ X i / 4 := fun i => by have := hr0 i; positivity
  have hη0le : ∀ i, smearRadius Λ X i / 4 ≤ 1 / 8 := fun i => by linarith [hr8 i, hr0 i]
  have hcSS := SS_le hN0 hc (sc := selfScale d s) (ξ := η) (C₂ := C₂) (fun i => hS0 (η i) (hηpos i) (hηle i))
  have hcSS0 := SS_le hN0 hc (sc := selfScale d s) (ξ := fun i => smearRadius Λ X i / 4) (C₂ := C₂)
    (fun i => hS0 _ (hη0pos i) (hη0le i))
  -- the comparison `|Comm| ≤ L c MB`
  have hcomm' : |commQuantity d s v X μ| ≤ L * (c * (
      CQ * (2 * F0 + (1 / (N : ℝ)) ^ 2 * ∑ i, S0 d (η i) + (2 * Λ / N) * ∑ i, η i ^ 2 / (2 * d)) +
      Cb * (2 * (2 * F0 + (1 / (N : ℝ)) ^ 2 * ∑ i, S0 d (smearRadius Λ X i / 4) +
            (2 * Λ / N) * ∑ i, (smearRadius Λ X i / 4) ^ 2 / (2 * d)) +
          2 * Cw * ((1 / (N : ℝ)) ^ 2 * ∑ i, rho2 d (smearRadius Λ X i))) +
      Ca * ((1 / (N : ℝ)) ^ 2 * ∑ i, rho2 d (smearRadius Λ X i)) +
      (if d = 2 then K2 * (1 / (N : ℝ))
        else Cs * ((1 / (N : ℝ)) ^ 2 * ∑ i, S0 d (η i)) + 2 * Jl d 0 * (1 / (N : ℝ))) +
      2 * (1 / (N : ℝ)) * Λ * M₁ * ∑ i, η i ^ 2)) := by
    rw [hcomm, abs_mul, abs_of_pos hc]
    calc c * |P0| ≤ c * (L * (_ : ℝ)) := mul_le_mul_of_nonneg_left hbound hc.le
      _ = _ := by ring
  have hRs : rieszEnergy d s X μ = c * F0 := hR
  have hSSS := hcSS
  by_cases hd2 : d = 2
  · -- the logarithmic case
    have hZZ := ZZ_two hd2 hΛ0 hN0 (r := fun i => smearRadius Λ X i) (ξ := η) hr0 (θ := 2) two_pos
      (fun i => (hη i).1.le)
    have hZZ0 := ZZ_two hd2 hΛ0 hN0 (r := fun i => smearRadius Λ X i) (ξ := fun i => smearRadius Λ X i / 4)
      hr0 (θ := 4) (by norm_num) (fun i => le_rfl)
    have hTt : (1 / (N : ℝ)) ^ 2 * ∑ i, rho2 d (smearRadius Λ X i) = u := by
      simp only [rho2_two hd2 (hr0 _), Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      rw [hu]; field_simp
    rw [if_pos hd2] at hcomm'
    have halg := alg_d2 (c := c) (CQ := CQ) (Cb := Cb) (Ca := Ca) (Cw := Cw) (C₂ := C₂) (K2 := K2) (M₁ := M₁)
      (F0 := F0) (SS := (1 / (N : ℝ)) ^ 2 * ∑ i, S0 d (η i))
      (SS0 := (1 / (N : ℝ)) ^ 2 * ∑ i, S0 d (smearRadius Λ X i / 4))
      (KK := (2 * Λ / N) * ∑ i, η i ^ 2 / (2 * d))
      (KK0 := (2 * Λ / N) * ∑ i, (smearRadius Λ X i / 4) ^ 2 / (2 * d))
      (Hh := 2 * (1 / (N : ℝ)) * Λ * M₁ * ∑ i, η i ^ 2)
      (Tt := (1 / (N : ℝ)) ^ 2 * ∑ i, rho2 d (smearRadius Λ X i)) (u := u) (a := a) (lp := lp) (S := S)
      (ZZ := (1 / (N : ℝ)) ^ 2 * ∑ i, selfScale d s (η i))
      (ZZ0 := (1 / (N : ℝ)) ^ 2 * ∑ i, selfScale d s (smearRadius Λ X i / 4)) (R := rieszEnergy d s X μ)
      hc hCQ hCb0 hCa0 hCw hK2 hM₁ hRs hTt hua hKK hKK0 hHh hcSS hcSS0 hZZ hZZ0 hl2 hl4 hu0 hC₂
    refine hcomm'.trans ?_
    refine mul_le_mul_of_nonneg_left (le_trans (le_of_eq (by ring)) (halg.trans ?_)) hL
    have e1 : 0 ≤ (CQ * 2 ^ s + 2 * Cb * 4 ^ s + c * (2 * Cb * Cw + Ca) + Cs * 2 ^ s) * S := by positivity
    have e2 : 0 ≤ ((CQ + 2 * Cb + Cs) * c * C₂ + 2 * c * Jl d 0 + c * (CQ + 2 * Cb + 2 * M₁)) * a := by positivity
    nlinarith [e1, e2]
  · -- `d ≥ 3`
    have hd3 : 3 ≤ d := by omega
    have hZZ := ZZ_ge3 hd3 hN0 (Λ := Λ) (r := fun i => smearRadius Λ X i) (ξ := η) hr0 (θ := 2) two_pos
      (fun i => (hη i).1.le)
    have hZZ0 := ZZ_ge3 hd3 hN0 (Λ := Λ) (r := fun i => smearRadius Λ X i) (ξ := fun i => smearRadius Λ X i / 4)
      hr0 (θ := 4) (by norm_num) (fun i => le_rfl)
    have hTt : (1 / (N : ℝ)) ^ 2 * ∑ i, rho2 d (smearRadius Λ X i) = S := by
      have e : ∑ i, rho2 d (smearRadius Λ X i) = ∑ i, selfExcess d s Λ N (smearRadius Λ X i) :=
        Finset.sum_congr rfl fun i _ => rho2_ge3 hd3 (hr0 i)
      rw [e, hS, one_div_pow]
    have hlp0 : lp = 0 := logPart_ge3 hd3 Λ N
    rw [if_neg hd2] at hcomm'
    have halg := alg_ge3 (c := c) (CQ := CQ) (Cb := Cb) (Ca := Ca) (Cw := Cw) (C₂ := C₂) (Cs := Cs) (J0 := Jl d 0)
      (M₁ := M₁) (F0 := F0) (SS := (1 / (N : ℝ)) ^ 2 * ∑ i, S0 d (η i))
      (SS0 := (1 / (N : ℝ)) ^ 2 * ∑ i, S0 d (smearRadius Λ X i / 4))
      (KK := (2 * Λ / N) * ∑ i, η i ^ 2 / (2 * d))
      (KK0 := (2 * Λ / N) * ∑ i, (smearRadius Λ X i / 4) ^ 2 / (2 * d))
      (Hh := 2 * (1 / (N : ℝ)) * Λ * M₁ * ∑ i, η i ^ 2)
      (Tt := (1 / (N : ℝ)) ^ 2 * ∑ i, rho2 d (smearRadius Λ X i)) (u := u) (a := a) (S := S)
      (ZZ := (1 / (N : ℝ)) ^ 2 * ∑ i, selfScale d s (η i))
      (ZZ0 := (1 / (N : ℝ)) ^ 2 * ∑ i, selfScale d s (smearRadius Λ X i / 4)) (R := rieszEnergy d s X μ)
      (P2 := 2 ^ s) (P4 := 4 ^ s)
      hc hCQ hCb0 hCa0 hCw hCs hM₁ hJ0 hC₂ hRs hTt hua hKK hKK0 hHh hcSS hcSS0 hZZ hZZ0 hu0
    refine hcomm'.trans ?_
    refine mul_le_mul_of_nonneg_left (le_trans (le_of_eq (by ring)) (halg.trans ?_)) hL
    rw [hlp0]
    have e1 : 0 ≤ (CQ + 2 * Cb) * S := by positivity
    have e2 : 0 ≤ (CQ * Real.log 2 + 2 * Cb * Real.log 4 + (CQ + 2 * Cb) * c * C₂ +
        c * (CQ + 2 * Cb + 2 * Cb * Cw + Ca + K2 + 2 * M₁)) * a := by positivity
    nlinarith [e1, e2]

theorem super_core_coulomb_aux (hd : 2 ≤ d) :
    ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 2 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
      ∀ (L : ℝ) (v : Torus d → Euc d), 0 ≤ L → IsLipschitzVF L v →
        |commQuantity d ((d : ℝ) - 2) v X (withDensityReal ρ)| ≤
          C * L * (rieszEnergy d ((d : ℝ) - 2) X (withDensityReal ρ) + logPart d ((d : ℝ) - 2) Λ N +
            (1 / (N : ℝ) ^ 2) * ∑ i, selfExcess d ((d : ℝ) - 2) Λ N (smearRadius Λ X i) +
            K * aNΛ d ((d : ℝ) - 2) Λ N) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨A2, γS, γa, hA2, hγS, hγa, hmain⟩ := coulomb_final_ineq hd
  have hs0 : (0 : ℝ) ≤ (d : ℝ) - 2 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsd : (d : ℝ) - 2 < d := by linarith
  obtain ⟨C₀, hC₀, hcoer⟩ := energy_add_oN_nonneg hd1 hs0 hsd
  have hCpos0 : 0 < A2 + γS + 1 := by positivity
  refine ⟨A2 + γS + 1, ((A2 + γS + 1 - A2) * C₀ + γa) / (A2 + γS + 1), hCpos0,
    div_nonneg (add_nonneg (mul_nonneg (by linarith) hC₀) hγa) hCpos0.le, ?_⟩
  intro Λ hΛ N hN ρ hρ hρΛ X hX L v hL hv
  have h1 := hmain hN hΛ hρ hρΛ hX hL hv
  have hN0 : 0 < N := by omega
  have hΛ0 : 0 < Λ := by linarith
  have hX' : ∀ i j, i ≠ j → X i ≠ X j := fun i j hij h => hX ⟨i, j, hij, h⟩
  obtain ⟨hr0, hrl, hr8, hsep⟩ := radii_facts hd1 hN hΛ X hX'
  have hS0' : 0 ≤ (1 / (N : ℝ) ^ 2) * ∑ i, selfExcess d ((d : ℝ) - 2) Λ N (smearRadius Λ X i) := by
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => ?_)
    exact selfExcess_nonneg hd hΛ0 hN0 (hr0 i) (hrl i)
  have ha0 : 0 ≤ aNΛ d ((d : ℝ) - 2) Λ N := aNΛ_nonneg d _ Λ N hΛ0.le
  have hco := hcoer Λ hΛ N hN ρ hρ hρΛ X hX
  rw [oNΛ_eq] at hco
  set R := rieszEnergy d ((d : ℝ) - 2) X (withDensityReal ρ) with hR
  set lp := logPart d ((d : ℝ) - 2) Λ N with hlp
  set S := (1 / (N : ℝ) ^ 2) * ∑ i, selfExcess d ((d : ℝ) - 2) Λ N (smearRadius Λ X i) with hS
  set a := aNΛ d ((d : ℝ) - 2) Λ N with ha
  have hCpos : 0 < A2 + γS + 1 := by positivity
  have hlp0 : 0 ≤ lp := by
    show 0 ≤ logPart d ((d : ℝ) - 2) Λ N
    unfold logPart
    split_ifs
    · have : (1 : ℝ) ≤ N * Λ := by
        have : (2 : ℝ) ≤ N := by exact_mod_cast hN
        nlinarith
      have := Real.log_nonneg this
      positivity
    · exact le_rfl
  refine h1.trans ?_
  have key : A2 * (R + lp) + γS * S + γa * a ≤
      (A2 + γS + 1) * (R + lp + S + ((A2 + γS + 1 - A2) * C₀ + γa) / (A2 + γS + 1) * a) := by
    have e : (A2 + γS + 1) * (((A2 + γS + 1 - A2) * C₀ + γa) / (A2 + γS + 1) * a) =
        ((A2 + γS + 1 - A2) * C₀ + γa) * a := by field_simp
    have hco' : 0 ≤ R + lp + C₀ * a := by linarith
    have h2 : 0 ≤ (A2 + γS + 1 - A2) * (R + lp + C₀ * a) := mul_nonneg (by linarith) hco'
    have h3 : 0 ≤ (A2 + γS + 1 - γS) * S := mul_nonneg (by linarith) hS0'
    nlinarith [e, h2, h3]
  calc L * (A2 * (R + lp) + γS * S + γa * a) ≤ L * ((A2 + γS + 1) * (R + lp + S +
        ((A2 + γS + 1 - A2) * C₀ + γa) / (A2 + γS + 1) * a)) := mul_le_mul_of_nonneg_left key hL
    _ = _ := by ring

end HRS.Commutator.Renorm
