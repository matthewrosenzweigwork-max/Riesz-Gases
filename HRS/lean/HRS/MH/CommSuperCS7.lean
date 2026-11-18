import HRS.MH.CommSuperDefs
import HRS.MH.CommSuperCS2
import HRS.MH.CommSuperCS3
import HRS.MH.CommSuperCS4
import HRS.MH.CommSuperCS5
import HRS.MH.CommSuperCS6

/-!
# CS7: the compactly supported case (`compact_case`)

Assembly of the torus theorem `HRS.Commutator.commutator_estimate_super` with the dilation `t → 0`,
using the proved packets CS2 (`periodic_cutoff_proof`), CS3 (`conc_measure_proof`), CS4
(`energy_conc_proof`), CS5 (`comm_conc_proof`) and CS6 (`oN_scale_proof`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MH.CommSuper

variable {d N : ℕ} {s : ℝ}

/-- The dilated, recentred field `x ↦ t (v (x / t) - v 0)` is `K`-Lipschitz. -/
theorem cs7_lip_dilate {v : Euc d → Euc d} {K : ℝ≥0} {t : ℝ} (ht : 0 < t)
    (hv : LipschitzWith K v) :
    LipschitzWith K (fun x : Euc d => t • (v (t⁻¹ • x) - v 0)) := by
  have ht0 : t ≠ 0 := ht.ne'
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h1 := hv.dist_le_mul (t⁻¹ • x) (t⁻¹ • y)
  have hx : dist (t⁻¹ • x) (t⁻¹ • y) = t⁻¹ * dist x y := by
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ht)]
  have hd : dist (t • (v (t⁻¹ • x) - v 0)) (t • (v (t⁻¹ • y) - v 0)) =
      t * dist (v (t⁻¹ • x)) (v (t⁻¹ • y)) := by
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos ht, dist_sub_right]
  show dist (t • (v (t⁻¹ • x) - v 0)) (t • (v (t⁻¹ • y) - v 0)) ≤ (K : ℝ) * dist x y
  rw [hd]
  calc t * dist (v (t⁻¹ • x)) (v (t⁻¹ • y)) ≤ t * ((K : ℝ) * dist (t⁻¹ • x) (t⁻¹ • y)) :=
        mul_le_mul_of_nonneg_left h1 ht.le
    _ = (K : ℝ) * (t * (t⁻¹ * dist x y)) := by rw [hx]; ring
    _ = (K : ℝ) * dist x y := by rw [mul_inv_cancel_left₀ ht0]

/-- Power absorption: `t^s |c0|/(2N)`-type term is at most `|c0|/2 · Λ^{s/d} N^{s/d-1}`. -/
theorem cs7_absorb {t Nn Λ s d' c0 : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hN : 2 ≤ Nn) (hΛ : 1 ≤ Λ)
    (hs : 0 ≤ s) (hd' : 0 ≤ d') :
    t ^ s * (-(c0 / (2 * Nn))) ≤ |c0| / 2 * (Λ ^ (s / d') * Nn ^ (s / d' - 1)) := by
  have hNpos : 0 < Nn := by linarith
  have h2Npos : (0 : ℝ) < 2 * Nn := by linarith
  have hts0 : 0 < t ^ s := Real.rpow_pos_of_pos ht s
  have hts1 : t ^ s ≤ 1 := Real.rpow_le_one ht.le ht1 hs
  have habs : |-(c0 / (2 * Nn))| = |c0| / (2 * Nn) := by
    rw [abs_neg, abs_div, abs_of_pos h2Npos]
  have h1 : t ^ s * (-(c0 / (2 * Nn))) ≤ |c0| / (2 * Nn) := by
    calc t ^ s * (-(c0 / (2 * Nn))) ≤ t ^ s * |-(c0 / (2 * Nn))| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hts0.le
      _ ≤ 1 * |-(c0 / (2 * Nn))| := mul_le_mul_of_nonneg_right hts1 (abs_nonneg _)
      _ = |c0| / (2 * Nn) := by rw [one_mul, habs]
  have hp : 1 ≤ Nn ^ (s / d') := Real.one_le_rpow (by linarith) (div_nonneg hs hd')
  have hq : 1 ≤ Λ ^ (s / d') := Real.one_le_rpow hΛ (div_nonneg hs hd')
  have hpq : 1 ≤ Λ ^ (s / d') * Nn ^ (s / d') := one_le_mul_of_one_le_of_one_le hq hp
  have h2 : |c0| / (2 * Nn) ≤ |c0| / 2 * (Λ ^ (s / d') * Nn ^ (s / d' - 1)) := by
    rw [Real.rpow_sub_one hNpos.ne']
    have h3 : |c0| / (2 * Nn) = |c0| / 2 * (1 / Nn) := by ring
    rw [h3]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [show Λ ^ (s / d') * (Nn ^ (s / d') / Nn) = (Λ ^ (s / d') * Nn ^ (s / d')) / Nn by ring]
    exact div_le_div_of_nonneg_right hpq hNpos.le
  exact h1.trans h2

/-- Pure real core of the fixed-`t` estimate (the algebra of CS4, CS5, CS6 combined). -/
theorem cs7_core {A1 K MC ME e ts F P Q R Ot ε η κ a C₀' c0 Nr : ℝ}
    (hA1 : 0 ≤ A1) (hK : 0 ≤ K) (hMC : 0 ≤ MC) (hME : 0 ≤ ME) (he : 0 ≤ e)
    (hts : 0 < ts) (hts1 : ts ≤ 1)
    (hT : |Q| ≤ A1 * (P + Ot))
    (hC : |Q - ts⁻¹ * R| ≤ 8 * K * MC * e)
    (hE : |P - (ts⁻¹ * F + ε - c0 / (2 * Nr))| ≤ 4 * ME * e)
    (hO : Ot = ts⁻¹ * (C₀' * a) + η)
    (hc : ts * ε + ts * η = κ)
    (hca : ts * (-(c0 / (2 * Nr))) ≤ |c0| / 2 * a) :
    |R| ≤ A1 * (F + (κ + (C₀' + |c0| / 2) * a)) + (A1 * (4 * ME) + 8 * K * MC) * e := by
  have hts0 : ts ≠ 0 := hts.ne'
  have hinv : ts * ts⁻¹ = 1 := mul_inv_cancel₀ hts0
  have h1 : |R - ts * Q| ≤ 8 * K * MC * e := by
    have hEq : R - ts * Q = -(ts * (Q - ts⁻¹ * R)) := by linear_combination (-R) * hinv
    rw [hEq, abs_neg, abs_mul, abs_of_pos hts]
    have h8 : 0 ≤ 8 * K * MC * e := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK) hMC) he
    nlinarith [abs_nonneg (Q - ts⁻¹ * R)]
  have h2 : |R| ≤ |R - ts * Q| + ts * |Q| := by
    have h := abs_add_le (R - ts * Q) (ts * Q)
    rw [sub_add_cancel, abs_mul, abs_of_pos hts] at h
    exact h
  have h4 : ts * |Q| ≤ A1 * (ts * (P + Ot)) := by
    calc ts * |Q| ≤ ts * (A1 * (P + Ot)) := mul_le_mul_of_nonneg_left hT hts.le
      _ = A1 * (ts * (P + Ot)) := by ring
  have h5 : ts * P ≤ F + ts * ε + ts * (-(c0 / (2 * Nr))) + ts * (4 * ME * e) := by
    have hP : P ≤ ts⁻¹ * F + ε - c0 / (2 * Nr) + 4 * ME * e := by
      have := (abs_le.mp hE).2
      linarith
    calc ts * P ≤ ts * (ts⁻¹ * F + ε - c0 / (2 * Nr) + 4 * ME * e) :=
          mul_le_mul_of_nonneg_left hP hts.le
      _ = F + ts * ε + ts * (-(c0 / (2 * Nr))) + ts * (4 * ME * e) := by
          linear_combination F * hinv
  have h6 : ts * Ot = C₀' * a + ts * η := by
    rw [hO]
    linear_combination (C₀' * a) * hinv
  have h7 : ts * (4 * ME * e) ≤ 4 * ME * e :=
    mul_le_of_le_one_left (mul_nonneg (mul_nonneg (by norm_num) hME) he) hts1
  have h8 : ts * (P + Ot) ≤ F + (κ + (C₀' + |c0| / 2) * a) + 4 * ME * e := by
    have e1 : ts * (P + Ot) = ts * P + ts * Ot := by ring
    rw [e1]
    linarith [h5, h6, hc, hca, h7]
  have h9 : A1 * (ts * (P + Ot)) ≤ A1 * (F + (κ + (C₀' + |c0| / 2) * a) + 4 * ME * e) :=
    mul_le_mul_of_nonneg_left h8 hA1
  linarith [h1, h2, h4, h9]

/-- Passing to the limit `t → 0` (the bound is affine in `t R0`). -/
theorem cs7_limit {x B A r0 T : ℝ} (hT : 0 < T)
    (h : ∀ t : ℝ, 0 < t → t < T → x ≤ B + A * (t * r0)) : x ≤ B := by
  have hlim : Tendsto (fun t : ℝ => B + A * (t * r0)) (𝓝[>] 0) (𝓝 B) := by
    have hc : Continuous (fun t : ℝ => B + A * (t * r0)) := by fun_prop
    have h0 : Tendsto (fun t : ℝ => B + A * (t * r0)) (𝓝[>] (0 : ℝ))
        (𝓝 (B + A * ((0 : ℝ) * r0))) :=
      tendsto_nhdsWithin_of_tendsto_nhds (hc.tendsto 0)
    simpa using h0
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hT] with t ht
  exact h t ht.1 ht.2

/-- **CS7** (size L).  The compactly supported case: `CompactCase` with `C₀ = C₀' + |c0|/2`, `C = 3C'`. -/
theorem compact_case_proof (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsc : (d : ℝ) - 2 ≤ s) (hsd : s < d) :
    ∃ C₀ C : ℝ, CompactCase d s C₀ C := by
  obtain ⟨δE, ME, c0, hδE, hδE1, hME, hEn⟩ := energy_conc_proof hd hs0 hsd
  obtain ⟨δC, MC, hδC, hδC1, hMC, hCm⟩ := comm_conc_proof hd hs0 hsd
  obtain ⟨C₀', C', hC₀', hC', hTor⟩ := HRS.Commutator.commutator_estimate_super hd hs0 hsc hsd
  refine ⟨C₀' + |c0| / 2, 3 * C', ?_⟩
  unfold CompactCase
  refine ⟨by linarith [abs_nonneg c0], by linarith, ?_⟩
  intro Λ hΛ1 N hN ρ hρ hρΛ R0 hρR0 X hX hXR v K hvK
  obtain ⟨L, hL, hLK⟩ := hvK
  have hK0 : (0 : ℝ) ≤ K := le_trans L.2 hLK
  obtain ⟨Kn, hKn⟩ : ∃ Kn : ℝ≥0, (Kn : ℝ) = K := ⟨⟨K, hK0⟩, rfl⟩
  have hLe : L ≤ Kn := by
    rw [← NNReal.coe_le_coe, hKn]
    exact hLK
  have hLipK : LipschitzWith Kn v := hL.weaken hLe
  have hR0 : 0 ≤ R0 := le_trans (norm_nonneg _) (hXR ⟨0, by omega⟩)
  have hΛpos : 0 < Λ := by linarith
  have hN1 : 1 ≤ N := by omega
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hd' : (0 : ℝ) ≤ (d : ℝ) := by positivity
  have hkey : ∀ t : ℝ, 0 < t → t < min 1 (min (δE / (2 * (R0 + 1))) (δC / (2 * (R0 + 1)))) →
      |Whole.commN d s v X (Whole.withDensityReal ρ)| ≤
        C' * (3 * K) * (Whole.rieszModulatedEnergy d s X (Whole.withDensityReal ρ) +
          oNΛ d s (C₀' + |c0| / 2) Λ N) +
        (C' * (3 * K) * (4 * ME) + 8 * K * MC) * (t * R0) := by
    intro t ht htt
    have ht1 : t ≤ 1 := le_trans htt.le (min_le_left _ _)
    have htE : t < δE / (2 * (R0 + 1)) :=
      lt_of_lt_of_le htt (le_trans (min_le_right _ _) (min_le_left _ _))
    have htC : t < δC / (2 * (R0 + 1)) :=
      lt_of_lt_of_le htt (le_trans (min_le_right _ _) (min_le_right _ _))
    rw [lt_div_iff₀ (by linarith)] at htE htC
    have hE2 : 2 * t * R0 < δE := by linarith
    have hC2 : 2 * t * R0 < δC := by linarith
    have hRt : t * R0 ≤ 1 / 16 := by linarith
    have hts : 0 < t ^ s := Real.rpow_pos_of_pos ht s
    have hts1 : t ^ s ≤ 1 := Real.rpow_le_one ht.le ht1 hs0
    obtain ⟨_, hprob, hbnd, hnc⟩ := conc_measure_proof ht hRt hρ hρR0
    have hΛ' : 1 ≤ (t ^ d)⁻¹ * Λ := by
      have hd1 : t ^ d ≤ 1 := pow_le_one₀ ht.le ht1
      have hdpos : 0 < t ^ d := pow_pos ht d
      have hinv : 1 ≤ (t ^ d)⁻¹ := (one_le_inv₀ hdpos).mpr hd1
      nlinarith
    obtain ⟨w, hwL, hwv⟩ := periodic_cutoff_proof (fun x : Euc d => t • (v (t⁻¹ • x) - v 0))
      Kn (cs7_lip_dilate ht hLipK)
    have hwfield : ∀ x : Euc d, ‖x‖ ≤ 1 / 16 → w (Torus.mk x) = t • (v (t⁻¹ • x) - v 0) := by
      intro x hx
      rw [hwv x hx]
      simp
    have hTc := hCm N hN t R0 Λ ht hC2 ρ hρ hρΛ hρR0 X hX hXR v Kn hLipK w hwfield
    rw [hKn] at hTc hwL
    have hTE := hEn N hN t R0 Λ ht hE2 ρ hρ hρΛ hρR0 X hX hXR
    have hTT := hTor ((t ^ d)⁻¹ * Λ) hΛ' N hN (concDens t ρ) hprob (hbnd Λ hρΛ)
      (fun i => concMap t (X i)) (hnc X hX hXR) (3 * K) w (by linarith) hwL
    have hO : oNΛ d s C₀' ((t ^ d)⁻¹ * Λ) N =
        (t ^ s)⁻¹ * (C₀' * (Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1))) +
          (if s = 0 then Real.log (N * Λ) / (2 * d * N) - Real.log t / (2 * N) else 0) := by
      rw [oN_scale_proof hd ht hΛpos C₀' hN1]
      ring
    have hc : t ^ s * (if s = 0 then Real.log t / (2 * (N : ℝ)) else 0) +
        t ^ s * (if s = 0 then Real.log (N * Λ) / (2 * d * N) - Real.log t / (2 * N) else 0) =
        (if s = 0 then Real.log (N * Λ) / (2 * d * N) else 0) := by
      by_cases hs : s = 0
      · subst hs
        simp <;> ring
      · simp [hs]
    have hca := cs7_absorb ht ht1 hNr hΛ1 hs0 hd' (c0 := c0)
    have hA1 : (0 : ℝ) ≤ C' * (3 * K) := mul_nonneg hC'.le (by linarith)
    have hcore := cs7_core hA1 hK0 hMC hME (mul_nonneg ht.le hR0) hts hts1 hTT hTc hTE hO hc hca
    have hoN : oNΛ d s (C₀' + |c0| / 2) Λ N =
        (if s = 0 then Real.log (N * Λ) / (2 * d * N) else 0) +
          (C₀' + |c0| / 2) * (Λ ^ (s / d) * (N : ℝ) ^ (s / d - 1)) := by
      unfold oNΛ
      ring
    rw [hoN]
    exact hcore
  exact (cs7_limit (lt_min one_pos (lt_min (div_pos hδE (by linarith)) (div_pos hδC (by linarith))))
    hkey).trans_eq (by ring)

end HRS.MH.CommSuper
