import HRS.PDE.MovAAux21

/-!
# MOVA Aux22: dependence of `S^M` on the time derivative `ρt` (needed for the degenerate case `T = 0`).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem mova_phit_diff_le (D : DynData d) {M : ℝ} (hM : 0 ≤ M) {ρ ρt₁ ρt₂ : ℝ → Torus d → ℝ} {r : ℝ}
    (hpos : ∀ x, 0 < ρ r x) {c₀ : ℝ} (hc₀ : 0 < c₀) (hlow : ∀ x, c₀ ≤ ρ r x)
    (hc1 : Continuous (ρt₁ r)) (hc2 : Continuous (ρt₂ r)) (hκ : 0 < D.invβ) {Bρ : ℝ}
    (hB : ∀ x, |ρt₁ r x - ρt₂ r x| ≤ Bρ) (y : Torus d) :
    |movT_phit D M ρ ρt₁ r y - movT_phit D M ρ ρt₂ r y| ≤
      (1 / c₀ + D.invβ⁻¹ * (mova_L1 (periodicRiesz d D.s) + mova_L1 (mova_kM D 0))) * Bρ := by
  have hBρ : 0 ≤ Bρ := le_trans (abs_nonneg _) (hB y)
  have hβ : 0 < D.invβ⁻¹ := inv_pos.2 hκ
  have hgi := mova_integrable_gReg D M
  have e : movT_phit D M ρ ρt₁ r y - movT_phit D M ρ ρt₂ r y =
      D.invβ⁻¹ * convFun (b15c_gReg d D.s M) (fun z => ρt₁ r z - ρt₂ r z) y +
        (ρt₁ r y - ρt₂ r y) / ρ r y := by
    rw [mova_convFun_sub_right hgi hc1 hc2]
    unfold movT_phit
    ring
  rw [e]
  have h1 : |convFun (b15c_gReg d D.s M) (fun z => ρt₁ r z - ρt₂ r z) y| ≤
      mova_L1 (b15c_gReg d D.s M) * Bρ :=
    mova_abs_convFun_le hgi (hc1.sub hc2) hB y
  have h2 : |(ρt₁ r y - ρt₂ r y) / ρ r y| ≤ Bρ / c₀ := by
    rw [abs_div, abs_of_pos (hpos y)]
    calc |ρt₁ r y - ρt₂ r y| / ρ r y ≤ Bρ / ρ r y :=
          div_le_div_of_nonneg_right (hB y) (hpos y).le
      _ ≤ Bρ / c₀ := div_le_div_of_nonneg_left hBρ hc₀ (hlow y)
  have h3 := mova_L1_gReg_le D hM
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_pos hβ]
  have h4 : D.invβ⁻¹ * |convFun (b15c_gReg d D.s M) (fun z => ρt₁ r z - ρt₂ r z) y| ≤
      D.invβ⁻¹ * ((mova_L1 (periodicRiesz d D.s) + mova_L1 (mova_kM D 0)) * Bρ) :=
    mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right h3 hBρ)) hβ.le
  calc _ ≤ D.invβ⁻¹ * ((mova_L1 (periodicRiesz d D.s) + mova_L1 (mova_kM D 0)) * Bρ) + Bρ / c₀ :=
        add_le_add h4 h2
    _ = _ := by ring

theorem mova_srcReg_diff_le (D : DynData d) {M : ℝ} (hM : 0 ≤ M) {ρ ρt₁ ρt₂ : ℝ → Torus d → ℝ} {r : ℝ}
    (hρ : Torus.IsCk 2 (ρ r)) (hpos : ∀ x, 0 < ρ r x) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hlow : ∀ x, c₀ ≤ ρ r x) (hc1 : Continuous (ρt₁ r)) (hc2 : Continuous (ρt₂ r))
    (hκ : 0 < D.invβ) {Bρ : ℝ} (hB : ∀ x, |ρt₁ r x - ρt₂ r x| ≤ Bρ)
    [IsProbabilityMeasure (movT_Q (b15c_gReg d D.s M) D N ρ r)] (X : Config d N) :
    |movT_srcReg D N M ρ ρt₁ r X - movT_srcReg D N M ρ ρt₂ r X| ≤
      2 * N * ((1 / c₀ + D.invβ⁻¹ * (mova_L1 (periodicRiesz d D.s) + mova_L1 (mova_kM D 0))) * Bρ) := by
  set Bd := (1 / c₀ + D.invβ⁻¹ * (mova_L1 (periodicRiesz d D.s) + mova_L1 (mova_kM D 0))) * Bρ with hBd
  have hpt := mova_phit_diff_le D hM hpos hc₀ hlow hc1 hc2 hκ hB
  have hP1 : Continuous (movT_psit D M ρ ρt₁ r : Config d N → ℝ) := by
    unfold movT_psit
    exact continuous_finsetSum _ fun i _ =>
      (mova_continuous_phit D M hρ hpos hc1).comp (continuous_apply i)
  have hP2 : Continuous (movT_psit D M ρ ρt₂ r : Config d N → ℝ) := by
    unfold movT_psit
    exact continuous_finsetSum _ fun i _ =>
      (mova_continuous_phit D M hρ hpos hc2).comp (continuous_apply i)
  have hdiff : ∀ Y : Config d N, |movT_psit D M ρ ρt₁ r Y - movT_psit D M ρ ρt₂ r Y| ≤ N * Bd := by
    intro Y
    unfold movT_psit
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => hpt (Y i)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hI : |∫ Y, movT_psit D M ρ ρt₁ r Y ∂(movT_Q (b15c_gReg d D.s M) D N ρ r) -
      ∫ Y, movT_psit D M ρ ρt₂ r Y ∂(movT_Q (b15c_gReg d D.s M) D N ρ r)| ≤ N * Bd := by
    rw [← integral_sub (mova_integrable_of_continuous_config hP1)
      (mova_integrable_of_continuous_config hP2)]
    have := norm_integral_le_of_norm_le_const (μ := movT_Q (b15c_gReg d D.s M) D N ρ r)
      (f := fun Y : Config d N => movT_psit D M ρ ρt₁ r Y - movT_psit D M ρ ρt₂ r Y)
      (C := N * Bd) (Filter.Eventually.of_forall fun Y => by
        rw [Real.norm_eq_abs]; exact hdiff Y)
    simpa using this
  have e : movT_srcReg D N M ρ ρt₁ r X - movT_srcReg D N M ρ ρt₂ r X =
      -(movT_psit D M ρ ρt₁ r X - movT_psit D M ρ ρt₂ r X) +
        (∫ Y, movT_psit D M ρ ρt₁ r Y ∂(movT_Q (b15c_gReg d D.s M) D N ρ r) -
          ∫ Y, movT_psit D M ρ ρt₂ r Y ∂(movT_Q (b15c_gReg d D.s M) D N ρ r)) := by
    unfold movT_srcReg
    ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg]
  have := hdiff X
  linarith

end HRS
