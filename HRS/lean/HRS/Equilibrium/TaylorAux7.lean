/-
# HRS.Equilibrium.TaylorAux7 — pointwise reduction and assembly for Lemma 4.7 (packet TAYLOR)
-/
import HRS.Equilibrium.PoleCavity
import HRS.Equilibrium.ProductTransfer
import HRS.Equilibrium.TaylorAux6

open MeasureTheory
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.TaylorAux

variable {d : ℕ} {s : ℝ}

section Pointwise

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β) (ρ : Torus d → ℝ)
  (hρ : SmoothPosDensity ρ) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)

include hd hcrit hβ hρ hc in
/-- For every configuration `Y`: the integrated Taylor remainder is dominated by the truncated
quadratic term plus the integrated tail sum (`|H'| ≤ 1` on the upper side, `H(v) ≤ e^K v²`). -/
theorem taylor_pointwise {K : ℝ} (hK : 0 ≤ K)
    (hKl : ∀ (N : ℕ) (n : ℕ) (i : Fin n) (H : ℝ), 0 ≤ H → ∀ (Y : Config d n) (y : Torus d),
      -K ≤ taylorFieldH d s c β ρ N i H Y y)
    (N : ℕ) (H : ℝ) (hH : 2 ≤ H) (i : Fin (N - 1)) (φ f : Torus d → ℝ)
    (hφm : Measurable φ) (hφ0 : ∀ y, 0 ≤ φ y) (hfφ : ∀ y, f y ≤ φ y) (Y : Config d (N - 1)) :
    ∫⁻ y, ENNReal.ofReal (f y * taylorH (cavityField d s c β ρ N i Y y)) ∂(withDensityReal ρ) ≤
      (∫⁻ y, ENNReal.ofReal (φ y) *
          ENNReal.ofReal (Real.exp K * taylorFieldH d s c β ρ N i H Y y ^ 2) ∂(withDensityReal ρ)) +
        ENNReal.ofReal (β / N) * ∑ j ∈ Finset.univ.erase i,
          taylorT (withDensityReal ρ) φ (taylorG d s c H) (Y j) := by
  obtain ⟨hs0, hsd⟩ := PoleCavityAux.hs_aux hd hcrit
  have hμ := PoleCavityAux.isProbabilityMeasure_mu hρ
  have hN : (0 : ℝ) ≤ β / N := by positivity
  set μ : Measure (Torus d) := withDensityReal ρ with hμdef
  set lam : ℝ := β / N with hlam
  set J : Finset (Fin (N - 1)) := Finset.univ.erase i with hJ
  have hGm := measurable_taylorG hd hs0 hsd c H (s := s)
  have hvm : Measurable fun y => taylorFieldH d s c β ρ N i H Y y :=
    Measurable.of_uncurry_left (f := fun (Y : Config d (N - 1)) (y : Torus d) =>
      taylorFieldH d s c β ρ N i H Y y) (taylor_measurable_fieldH hd hcrit β ρ c (N := N) (N - 1) i H)
  -- the real pointwise inequality
  have hreal : ∀ y, f y * taylorH (cavityField d s c β ρ N i Y y) ≤
      φ y * (Real.exp K * taylorFieldH d s c β ρ N i H Y y ^ 2) +
        φ y * (lam * ∑ j ∈ J, taylorG d s c H (y - Y j)) := by
    intro y
    set v := cavityField d s c β ρ N i Y y with hv
    set w := taylorFieldH d s c β ρ N i H Y y with hw
    have hvw : v - w = lam * ∑ j ∈ J, taylorG d s c H (y - Y j) := by
      simp only [hv, hw, cavityField, taylorFieldH, taylorG, hlam, hJ]
      rw [Finset.sum_sub_distrib]
      ring
    have hGnn : 0 ≤ ∑ j ∈ J, taylorG d s c H (y - Y j) :=
      Finset.sum_nonneg fun j _ => taylorG_nonneg c H (by linarith) hc _
    have hwv : w ≤ v := by
      have : 0 ≤ lam * ∑ j ∈ J, taylorG d s c H (y - Y j) := mul_nonneg hN hGnn
      linarith
    have h1 : taylorH v ≤ Real.exp K * w ^ 2 + lam * ∑ j ∈ J, taylorG d s c H (y - Y j) := by
      have := taylor_H_lip hwv
      have h2 := taylor_H_le hK (hKl N (N - 1) i H (by linarith) Y y)
      linarith
    calc f y * taylorH v ≤ φ y * taylorH v :=
          mul_le_mul_of_nonneg_right (hfφ y) (taylor_H_nonneg v)
      _ ≤ φ y * (Real.exp K * w ^ 2 + lam * ∑ j ∈ J, taylorG d s c H (y - Y j)) :=
          mul_le_mul_of_nonneg_left h1 (hφ0 y)
      _ = _ := by ring
  -- pass to `ℝ≥0∞`
  have hmeas1 : Measurable fun y => ENNReal.ofReal (φ y) *
      ENNReal.ofReal (Real.exp K * taylorFieldH d s c β ρ N i H Y y ^ 2) :=
    hφm.ennreal_ofReal.mul ((measurable_const.mul (hvm.pow_const 2)).ennreal_ofReal)
  have hpt : ∀ y, ENNReal.ofReal (f y * taylorH (cavityField d s c β ρ N i Y y)) ≤
      ENNReal.ofReal (φ y) * ENNReal.ofReal (Real.exp K * taylorFieldH d s c β ρ N i H Y y ^ 2) +
        ENNReal.ofReal lam * ∑ j ∈ J, (ENNReal.ofReal (φ y) * ENNReal.ofReal (taylorG d s c H (y - Y j))) := by
    intro y
    refine (ENNReal.ofReal_le_ofReal (hreal y)).trans ?_
    have hGnn : 0 ≤ ∑ j ∈ J, taylorG d s c H (y - Y j) :=
      Finset.sum_nonneg fun j _ => taylorG_nonneg c H (by linarith) hc _
    rw [ENNReal.ofReal_add (mul_nonneg (hφ0 y) (by positivity)) (mul_nonneg (hφ0 y) (mul_nonneg hN hGnn)),
      ENNReal.ofReal_mul (hφ0 y), ENNReal.ofReal_mul (hφ0 y), ENNReal.ofReal_mul hN,
      ENNReal.ofReal_sum_of_nonneg fun j _ => taylorG_nonneg c H (by linarith) hc _]
    refine add_le_add le_rfl (le_of_eq ?_)
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  calc ∫⁻ y, ENNReal.ofReal (f y * taylorH (cavityField d s c β ρ N i Y y)) ∂μ
      ≤ ∫⁻ y, (ENNReal.ofReal (φ y) *
          ENNReal.ofReal (Real.exp K * taylorFieldH d s c β ρ N i H Y y ^ 2) +
          ENNReal.ofReal lam * ∑ j ∈ J, (ENNReal.ofReal (φ y) *
            ENNReal.ofReal (taylorG d s c H (y - Y j)))) ∂μ := lintegral_mono hpt
    _ = (∫⁻ y, ENNReal.ofReal (φ y) *
          ENNReal.ofReal (Real.exp K * taylorFieldH d s c β ρ N i H Y y ^ 2) ∂μ) +
        ∫⁻ y, ENNReal.ofReal lam * ∑ j ∈ J, (ENNReal.ofReal (φ y) *
            ENNReal.ofReal (taylorG d s c H (y - Y j))) ∂μ := lintegral_add_left hmeas1 _
    _ = _ := by
        congr 1
        have hmT : ∀ j : Fin (N - 1), Measurable fun y => ENNReal.ofReal (φ y) *
            ENNReal.ofReal (taylorG d s c H (y - Y j)) := fun j =>
          hφm.ennreal_ofReal.mul (hGm.comp (measurable_id.sub measurable_const)).ennreal_ofReal
        rw [lintegral_const_mul (f := fun y => ∑ j ∈ J, (ENNReal.ofReal (φ y) *
            ENNReal.ofReal (taylorG d s c H (y - Y j)))) _ (Finset.measurable_sum _ fun j _ => hmT j),
          lintegral_finset_sum _ fun j _ => hmT j]
        rfl

end Pointwise

section Total

/-- `ν = N^{1/8}`. -/
def taylorNu (N : ℕ) : ℝ := (N : ℝ) ^ ((1 : ℝ) / 8)

theorem taylorNu_pow8 (N : ℕ) : taylorNu N ^ 8 = N := by
  unfold taylorNu
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
  norm_num

theorem one_le_taylorNu (N : ℕ) (hN : 1 ≤ N) : 1 ≤ taylorNu N :=
  Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)

theorem taylor_measurable_T {μ : Measure (Torus d)} [SFinite μ] {φ G : Torus d → ℝ}
    (hφ : Measurable φ) (hG : Measurable G) : Measurable (taylorT μ φ G) := by
  unfold taylorT
  refine Measurable.lintegral_prod_right' (f := fun p : Torus d × Torus d =>
    ENNReal.ofReal (φ p.2) * ENNReal.ofReal (G (p.2 - p.1))) ?_
  exact (hφ.comp measurable_snd).ennreal_ofReal.mul
    (hG.comp (measurable_snd.sub measurable_fst)).ennreal_ofReal

/-- The real arithmetic of the final bound at `N = ν⁸`, `H = 2ν⁵`, `M = ν³`. -/
theorem taylor_real_est {ν β Ct kb ℓ : ℝ} (hν : 1 ≤ ν) (hβ : 0 < β) (hCt : 0 ≤ Ct) (hkb : 0 ≤ kb)
    (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ ν ^ 8) :
    (β / ν ^ 8) * ℓ * (Ct / (2 * ν ^ 5)) +
      (β / ν ^ 8) * kb * Real.sqrt (ℓ * (ν ^ 3 * (Ct / (2 * ν ^ 5))) + (ν ^ 3) ^ 2) +
      (β / ν ^ 8) * ℓ * max Ct 1 / (ν ^ 3) ^ 2 ≤
    (β * Ct / 2 + β * kb * Real.sqrt (Ct / 2 + 1) + β * max Ct 1) * (ν ^ 5)⁻¹ := by
  have hν0 : 0 < ν := by linarith
  have hν1 : 1 ≤ ν ^ 5 := one_le_pow₀ hν
  have hν8 : 0 < ν ^ 8 := by positivity
  have hmx : 0 ≤ max Ct 1 := le_trans zero_le_one (le_max_right _ _)
  have t1 : (β / ν ^ 8) * ℓ * (Ct / (2 * ν ^ 5)) ≤ β * Ct / 2 * (ν ^ 5)⁻¹ := by
    have : (β / ν ^ 8) * ℓ ≤ β := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hν8]; nlinarith
    calc (β / ν ^ 8) * ℓ * (Ct / (2 * ν ^ 5)) ≤ β * (Ct / (2 * ν ^ 5)) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = β * Ct / 2 * (ν ^ 5)⁻¹ := by field_simp
  have t2 : (β / ν ^ 8) * kb * Real.sqrt (ℓ * (ν ^ 3 * (Ct / (2 * ν ^ 5))) + (ν ^ 3) ^ 2) ≤
      β * kb * Real.sqrt (Ct / 2 + 1) * (ν ^ 5)⁻¹ := by
    have h1 : ℓ * (ν ^ 3 * (Ct / (2 * ν ^ 5))) + (ν ^ 3) ^ 2 ≤ (ν ^ 3) ^ 2 * (Ct / 2 + 1) := by
      have : ℓ * (ν ^ 3 * (Ct / (2 * ν ^ 5))) ≤ ν ^ 8 * (ν ^ 3 * (Ct / (2 * ν ^ 5))) :=
        mul_le_mul_of_nonneg_right hℓ (by positivity)
      have e : ν ^ 8 * (ν ^ 3 * (Ct / (2 * ν ^ 5))) = (ν ^ 3) ^ 2 * (Ct / 2) := by field_simp
      nlinarith
    have h2 : Real.sqrt (ℓ * (ν ^ 3 * (Ct / (2 * ν ^ 5))) + (ν ^ 3) ^ 2) ≤
        ν ^ 3 * Real.sqrt (Ct / 2 + 1) := by
      refine (Real.sqrt_le_sqrt h1).trans (le_of_eq ?_)
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    calc (β / ν ^ 8) * kb * Real.sqrt (ℓ * (ν ^ 3 * (Ct / (2 * ν ^ 5))) + (ν ^ 3) ^ 2)
        ≤ (β / ν ^ 8) * kb * (ν ^ 3 * Real.sqrt (Ct / 2 + 1)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = β * kb * Real.sqrt (Ct / 2 + 1) * (ν ^ 5)⁻¹ := by field_simp
  have t3 : (β / ν ^ 8) * ℓ * max Ct 1 / (ν ^ 3) ^ 2 ≤ β * max Ct 1 * (ν ^ 5)⁻¹ := by
    have : (β / ν ^ 8) * ℓ ≤ β := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hν8]; nlinarith
    have h6 : (ν ^ 3) ^ 2 = ν ^ 6 := by ring
    rw [h6, mul_div_assoc, div_eq_mul_inv]
    calc (β / ν ^ 8) * ℓ * (max Ct 1 * (ν ^ 6)⁻¹) ≤ β * (max Ct 1 * (ν ^ 6)⁻¹) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ ≤ β * (max Ct 1 * (ν ^ 5)⁻¹) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hmx) hβ.le
          exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hν (by norm_num))
      _ = _ := by ring
  nlinarith [t1, t2, t3]

end Total

section Assembly

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β) (ρ : Torus d → ℝ)
  (hρ : SmoothPosDensity ρ) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)

theorem taylor_log_le {ν : ℝ} (hν : 1 ≤ ν) : Real.log (2 * ν ^ 5) ≤ 6 * ν := by
  have hν0 : 0 < ν := by linarith
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have h1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have h2 : Real.log ν ≤ ν - 1 := Real.log_le_sub_one_of_pos hν0
  push_cast
  nlinarith

theorem taylor_theta_le {ν : ℝ} (hν : 1 ≤ ν) :
    Real.log (2 * ν ^ 5) / (ν ^ 8) + (2 * ν ^ 5) ^ 2 / (ν ^ 8) ^ 2 + 1 / (2 * ν ^ 5) ^ 2 +
      1 / (ν ^ 8) ^ 2 ≤ 12 * (ν ^ 5)⁻¹ := by
  have hν0 : 0 < ν := by linarith
  have hlog := taylor_log_le hν
  have h1 : Real.log (2 * ν ^ 5) / (ν ^ 8) ≤ 6 * (ν ^ 5)⁻¹ := by
    rw [div_le_iff₀ (by positivity)]
    have : 6 * (ν ^ 5)⁻¹ * ν ^ 8 = 6 * ν ^ 3 := by field_simp
    rw [this]
    nlinarith [pow_le_pow_right₀ hν (show 1 ≤ 3 by norm_num), pow_one ν]
  have h2 : (2 * ν ^ 5) ^ 2 / (ν ^ 8) ^ 2 ≤ 4 * (ν ^ 5)⁻¹ := by
    have : (2 * ν ^ 5) ^ 2 / (ν ^ 8) ^ 2 = 4 * (ν ^ 6)⁻¹ := by field_simp; ring
    rw [this]
    have : (ν ^ 6)⁻¹ ≤ (ν ^ 5)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_right₀ hν (by norm_num))
    linarith
  have h3 : 1 / (2 * ν ^ 5) ^ 2 ≤ (ν ^ 5)⁻¹ := by
    have h5 : 1 ≤ ν ^ 5 := one_le_pow₀ hν
    rw [div_le_iff₀ (by positivity)]
    have : (ν ^ 5)⁻¹ * (2 * ν ^ 5) ^ 2 = 4 * ν ^ 5 := by field_simp; norm_num
    rw [this]; nlinarith
  have h4 : 1 / (ν ^ 8) ^ 2 ≤ (ν ^ 5)⁻¹ := by
    rw [one_div]
    refine inv_anti₀ (by positivity) ?_
    calc ν ^ 5 ≤ ν ^ 16 := pow_le_pow_right₀ hν (by norm_num)
      _ = (ν ^ 8) ^ 2 := by ring
  linarith

include hd hcrit hβ hρ hc in
theorem taylor_Lp_total (q : ℕ) (hq : 1 ≤ q) {K : ℝ} (hK : 0 ≤ K) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ N : ℕ, 2 ≤ N → ∀ i : Fin (N - 1), ∀ x : Torus d,
      ∀ φ ∈ ({fun _ => 1, fun y => gPlus d s c (x - y)} : Set (Torus d → ℝ)),
        taylorLp (Measure.pi fun _ : Fin (N - 1) => withDensityReal ρ) ((2 * q : ℕ) : ℝ)
          (fun Y => (∫⁻ y, ENNReal.ofReal (φ y) *
              ENNReal.ofReal (Real.exp K * taylorFieldH d s c β ρ N i (2 * taylorNu N ^ 5) Y y ^ 2)
                ∂(withDensityReal ρ)) +
            ENNReal.ofReal (β / N) * ∑ j ∈ Finset.univ.erase i,
              taylorT (withDensityReal ρ) φ (taylorG d s c (2 * taylorNu N ^ 5)) (Y j)) ≤
          ENNReal.ofReal (Cb * (taylorNu N ^ 5)⁻¹) := by
  have hμ := PoleCavityAux.isProbabilityMeasure_mu hρ
  obtain ⟨hs0, hsd⟩ := PoleCavityAux.hs_aux hd hcrit
  obtain ⟨CB1, hCB10, hCB1⟩ := taylor_B1_bound hd hcrit β hβ ρ hρ c hc q hq hK
  obtain ⟨Ct, hCt0, hCt⟩ := taylor_tail_bounds hd hcrit β hβ ρ hρ c hc (6 * q) (by omega)
  have hkb := taylor_kb_one_le q
  refine ⟨12 * CB1 + (β * Ct / 2 + β * taylor_kb q * Real.sqrt (Ct / 2 + 1) + β * max Ct 1),
    by positivity, fun N hN i x φ hφ => ?_⟩
  set ν : ℝ := taylorNu N with hν
  have hν1 : 1 ≤ ν := one_le_taylorNu N (by omega)
  have hν8 : ν ^ 8 = N := taylorNu_pow8 N
  have hν0 : 0 < ν := by linarith
  set H : ℝ := 2 * ν ^ 5 with hHdef
  have hH : 2 ≤ H := by
    have : 1 ≤ ν ^ 5 := one_le_pow₀ hν1
    rw [hHdef]; linarith
  have hH0 : 0 < H := by linarith
  have hφm : Measurable φ := by
    rcases hφ with rfl | rfl
    · exact measurable_const
    · exact (PoleCavityAux.measurable_gPlus hd hs0 hsd c (s := s)).comp
        (measurable_const.sub measurable_id)
  set μ : Measure (Torus d) := withDensityReal ρ with hμdef
  set Pm : Measure (Config d (N - 1)) := Measure.pi fun _ : Fin (N - 1) => μ with hPm
  have hGm := measurable_taylorG hd hs0 hsd c H (s := s)
  have hTm : Measurable (taylorT μ φ (taylorG d s c H)) := taylor_measurable_T hφm hGm
  have hp1 : (1 : ℝ) ≤ ((2 * q : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * q)
  -- the two pieces
  have hB1 := hCB1 N hN H hH i x φ hφ
  have hB1' : taylorLp Pm ((2 * q : ℕ) : ℝ) (fun Y => ∫⁻ y, ENNReal.ofReal (φ y) *
      ENNReal.ofReal (Real.exp K * taylorFieldH d s c β ρ N i H Y y ^ 2) ∂μ) ≤
      ENNReal.ofReal (CB1 * (12 * (ν ^ 5)⁻¹)) := by
    refine hB1.trans (ENNReal.ofReal_le_ofReal ?_)
    refine mul_le_mul_of_nonneg_left ?_ hCB10
    have := taylor_theta_le hν1
    rw [hν8] at this
    simpa [hHdef] using this
  obtain ⟨hmass, hL1, hLp⟩ := hCt H hH x φ hφ
  have hB2 := taylor_sum_bound (μ := μ) (Finset.univ.erase i) (taylorT μ φ (taylorG d s c H)) hTm q hq
    (m1 := Ct / H) (CT := Ct) (M := ν ^ 3) (lam := β / N) (by positivity) hL1 hLp
    (by positivity) (by positivity)
  have hB2' : taylorLp Pm ((2 * q : ℕ) : ℝ) (fun Y => ENNReal.ofReal (β / N) * ∑ j ∈ Finset.univ.erase i,
      taylorT μ φ (taylorG d s c H) (Y j)) ≤
      ENNReal.ofReal ((β * Ct / 2 + β * taylor_kb q * Real.sqrt (Ct / 2 + 1) + β * max Ct 1) * (ν ^ 5)⁻¹) := by
    refine hB2.trans (ENNReal.ofReal_le_ofReal ?_)
    have hcard : ((Finset.univ.erase i).card : ℝ) ≤ ν ^ 8 := by
      rw [hν8, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      have : N - 1 - 1 ≤ N := by omega
      exact_mod_cast this
    have := taylor_real_est (ν := ν) (β := β) (Ct := Ct) (kb := taylor_kb q)
      (ℓ := ((Finset.univ.erase i).card : ℝ)) hν1 hβ hCt0 (by linarith) (Nat.cast_nonneg _) hcard
    rw [hν8] at this
    simpa [hHdef] using this
  -- Minkowski
  have hB1m : Measurable fun Y : Config d (N - 1) => ∫⁻ y, ENNReal.ofReal (φ y) *
      ENNReal.ofReal (Real.exp K * taylorFieldH d s c β ρ N i H Y y ^ 2) ∂μ := by
    refine Measurable.lintegral_prod_right' (f := fun p : Config d (N - 1) × Torus d =>
      ENNReal.ofReal (φ p.2) * ENNReal.ofReal (Real.exp K * taylorFieldH d s c β ρ N i H p.1 p.2 ^ 2)) ?_
    exact (hφm.comp measurable_snd).ennreal_ofReal.mul
      ((measurable_const.mul
        ((taylor_measurable_fieldH hd hcrit β ρ c (N := N) (N - 1) i H).pow_const 2)).ennreal_ofReal)
  have hB2m : Measurable fun Y : Config d (N - 1) => ENNReal.ofReal (β / N) *
      ∑ j ∈ Finset.univ.erase i, taylorT μ φ (taylorG d s c H) (Y j) :=
    (Finset.measurable_sum _ fun j _ => hTm.comp (measurable_pi_apply j)).const_mul _
  refine (taylorLp_add hp1 hB1m.aemeasurable hB2m.aemeasurable).trans ?_
  refine (add_le_add hB1' hB2').trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  ring

end Assembly

end HRS.TaylorAux
