import HRS.PDE.MovAAux10

/-!
# MOVA Aux11: uniform bounds in `M ≥ 0` and the `Δ`-estimate, the Lipschitz estimate for `u^M - u`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem mova_L1_kM_eq (D : DynData d) (M : ℝ) :
    mova_L1 (mova_kM D M) = ∫ z : Torus d, |periodicRiesz d D.s z - b15c_gReg d D.s M z| := by
  unfold mova_L1 mova_kM
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  exact abs_sub_comm _ _

theorem mova_kM_abs_le (D : DynData d) {M : ℝ} (hM : 0 ≤ M) :
    ∀ᵐ z : Torus d, |mova_kM D M z| ≤ |mova_kM D 0 z| := by
  filter_upwards [KernelGrad.torus_ae_ne' (b15_one_le_d D)] with z hz
  unfold mova_kM
  have h1 := b15c_gReg_le (d := d) D.s M hz
  have h2 := b15c_gReg_mono (d := d) D.s z hM
  have h3 := b15c_gReg_le (d := d) D.s 0 hz
  rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
  linarith

theorem mova_L1_kM_le (D : DynData d) {M : ℝ} (hM : 0 ≤ M) : mova_L1 (mova_kM D M) ≤ mova_L1 (mova_kM D 0) :=
  integral_mono_ae ((mova_integrable_kM D M).abs) ((mova_integrable_kM D 0).abs)
    (mova_kM_abs_le D hM)

theorem mova_L1_gReg_le (D : DynData d) {M : ℝ} (hM : 0 ≤ M) :
    mova_L1 (b15c_gReg d D.s M) ≤ mova_L1 (periodicRiesz d D.s) + mova_L1 (mova_kM D 0) := by
  have hgi := mova_integrable_periodicRiesz (b15_one_le_d D) D.hs0 D.hsd
  have h1 : mova_L1 (b15c_gReg d D.s M) ≤ ∫ z : Torus d, (|periodicRiesz d D.s z| + |mova_kM D M z|) := by
    refine integral_mono (mova_integrable_gReg D M).abs (hgi.abs.add (mova_integrable_kM D M).abs)
      fun z => ?_
    simp only
    unfold mova_kM
    calc |b15c_gReg d D.s M z| = |periodicRiesz d D.s z + (b15c_gReg d D.s M z - periodicRiesz d D.s z)| := by
          congr 1; ring
      _ ≤ _ := abs_add_le _ _
  refine h1.trans ?_
  rw [integral_add hgi.abs (mova_integrable_kM D M).abs]
  exact add_le_add le_rfl (mova_L1_kM_le D hM)

/-- Bound on `Δ` from the closed form. -/
theorem mova_abs_Delta_le (D : DynData d) (M : ℝ) {ρ ρt : ℝ → Torus d → ℝ} {r : ℝ}
    (hρ : Torus.IsCk 2 (ρ r)) (hpos : ∀ x, 0 < ρ r x) (hV : Torus.IsCk 2 D.V)
    (hPDE : ∀ x, ρt r x = mova_pdeRHS D (ρ r) x) {Λ : ℝ} (hΛ : Torus.cbNorm 2 (ρ r) ≤ Λ)
    (x : Torus d) :
    |mova_Delta D M ρ ρt r x| ≤ 2 * d * (Λ * Λ) * mova_L1 (mova_kM D M) := by
  have hρ1 := mova_isCk_one_of_two hρ
  rw [mova_Delta_eq D M hρ hpos hV hPDE x]
  have hki := mova_integrable_kM D M
  have hε := mova_L1_nonneg (mova_kM D M)
  have hdρc : ∀ j, Continuous (Torus.partialDeriv j (ρ r)) := fun j =>
    mova_continuous_partialDeriv hρ1 j
  have hddρc : ∀ j, Continuous (Torus.partialDeriv j (Torus.partialDeriv j (ρ r))) := fun j =>
    mova_continuous_partialDeriv (mova_isCk_partialDeriv hρ j) j
  have hΛ0 : 0 ≤ Λ := (le_trans (abs_nonneg _) (mova_abs_le_cbNorm_two hρ x)).trans hΛ
  have hterm : ∀ j : Fin d, |Torus.partialDeriv j (ρ r) x * convFun (mova_kM D M)
      (Torus.partialDeriv j (ρ r)) x + ρ r x * convFun (mova_kM D M)
        (Torus.partialDeriv j (Torus.partialDeriv j (ρ r))) x| ≤
      2 * (Λ * Λ) * mova_L1 (mova_kM D M) := by
    intro j
    have a1 := mova_abs_partialDeriv_le hρ j x
    have a0 := mova_abs_le_cbNorm_two hρ x
    have a2 := mova_abs_convFun_le hki (hdρc j) (B := Λ) (fun y => (mova_abs_partialDeriv_le hρ j y).trans hΛ) x
    have a3 := mova_abs_convFun_le hki (hddρc j) (B := Λ)
      (fun y => (mova_abs_partialDeriv2_le hρ j y).trans hΛ) x
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have b1 : |Torus.partialDeriv j (ρ r) x| ≤ Λ := a1.trans hΛ
    have b0 : |ρ r x| ≤ Λ := a0.trans hΛ
    have c1 : |Torus.partialDeriv j (ρ r) x| * |convFun (mova_kM D M) (Torus.partialDeriv j (ρ r)) x| ≤
        Λ * (mova_L1 (mova_kM D M) * Λ) :=
      mul_le_mul b1 a2 (abs_nonneg _) hΛ0
    have c2 : |ρ r x| * |convFun (mova_kM D M) (Torus.partialDeriv j (Torus.partialDeriv j (ρ r))) x| ≤
        Λ * (mova_L1 (mova_kM D M) * Λ) :=
      mul_le_mul b0 a3 (abs_nonneg _) hΛ0
    nlinarith
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun j _ => hterm j).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact le_of_eq (by ring)

/-- Bound on `k`. -/
theorem mova_abs_k_le (D : DynData d) {M : ℝ} (hM : 0 ≤ M) {ρ ρt : ℝ → Torus d → ℝ} {r : ℝ}
    (hρ : Torus.IsCk 2 (ρ r)) (hdens : IsProbDensity (ρ r)) (hpos : ∀ x, 0 < ρ r x)
    (hV : Torus.IsCk 2 D.V) (hκ : 0 < D.invβ) (hρtc : Continuous (ρt r))
    (hPDE : ∀ x, ρt r x = mova_pdeRHS D (ρ r) x) {Λ c₀ : ℝ} (hΛ : Torus.cbNorm 2 (ρ r) ≤ Λ)
    (hc₀ : 0 < c₀) (hlow : ∀ x, c₀ ≤ ρ r x) (x : Torus d) :
    |mova_k D M ρ ρt r x| ≤ (1 / c₀ + D.invβ⁻¹ * (mova_L1 (periodicRiesz d D.s) + mova_L1 (mova_kM D 0))) *
      (2 * d * (Λ * Λ) * mova_L1 (mova_kM D M)) := by
  rw [mova_k_eq D M hρ hdens hpos hV hκ hρtc x]
  set Dl := 2 * d * (Λ * Λ) * mova_L1 (mova_kM D M) with hDl
  have hD := mova_abs_Delta_le D M hρ hpos hV hPDE hΛ
  have hDl0 : 0 ≤ Dl := le_trans (abs_nonneg _) (hD x)
  have hβ : 0 < D.invβ⁻¹ := inv_pos.2 hκ
  have hgM := mova_integrable_gReg D M
  have hDc : Continuous (mova_Delta D M ρ ρt r) :=
    (mova_continuous_divRW D M hρ hpos hV).sub hρtc
  have h1 : |mova_Delta D M ρ ρt r x / ρ r x| ≤ Dl / c₀ := by
    rw [abs_div, abs_of_pos (hpos x)]
    calc |mova_Delta D M ρ ρt r x| / ρ r x ≤ Dl / ρ r x :=
          div_le_div_of_nonneg_right (hD x) (hpos x).le
      _ ≤ Dl / c₀ := div_le_div_of_nonneg_left hDl0 hc₀ (hlow x)
  have h2 : |convFun (b15c_gReg d D.s M) (mova_Delta D M ρ ρt r) x| ≤
      (mova_L1 (periodicRiesz d D.s) + mova_L1 (mova_kM D 0)) * Dl :=
    (mova_abs_convFun_le hgM hDc hD x).trans (mul_le_mul_of_nonneg_right (mova_L1_gReg_le D hM) hDl0)
  calc _ ≤ |mova_Delta D M ρ ρt r x / ρ r x| + |D.invβ⁻¹ *
        convFun (b15c_gReg d D.s M) (mova_Delta D M ρ ρt r) x| := abs_add_le _ _
    _ ≤ Dl / c₀ + D.invβ⁻¹ * ((mova_L1 (periodicRiesz d D.s) + mova_L1 (mova_kM D 0)) * Dl) := by
        rw [abs_mul, abs_of_pos hβ]
        exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 hβ.le)
    _ = _ := by ring

end HRS
