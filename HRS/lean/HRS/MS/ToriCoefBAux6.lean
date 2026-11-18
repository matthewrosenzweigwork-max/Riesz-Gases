import HRS.MS.ToriCoefBAux5

/-!
# MS-TORI-COEFB, helper file 6: vector transfer, `matVec` bound, and the gradient of `V_L`
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ToriCoefB

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.ToriCoefA

variable {d : ℕ}

/-- Regularity and derivative bounds of `∑_i T_i • e_i` from those of the scalar functions `T_i`. -/
theorem tcb_vec_bound (n : ℕ) (T : Fin d → Euc d → ℝ) (b : ℝ)
    (hT : ∀ i, ContDiff ℝ (n : WithTop ℕ∞) (T i))
    (hb : ∀ i, ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (T i) x‖ ≤ b) :
    ContDiff ℝ (n : WithTop ℕ∞) (fun x => ∑ i, T i x • (EuclideanSpace.single i (1 : ℝ) : Euc d)) ∧
      ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j
        (fun x => ∑ i, T i x • (EuclideanSpace.single i (1 : ℝ) : Euc d)) x‖ ≤ d * b := by
  refine ⟨ContDiff.sum fun i _ => (hT i).smul contDiff_const, fun j hj x => ?_⟩
  have hcd : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      ContDiffAt ℝ (j : WithTop ℕ∞) (fun x => T i x • (EuclideanSpace.single i (1 : ℝ) : Euc d)) x :=
    fun i _ => ((hT i).of_le (by exact_mod_cast hj)).smul contDiff_const |>.contDiffAt
  rw [iteratedFDeriv_fun_sum_apply hcd]
  refine (norm_sum_le _ _).trans ?_
  have : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      ‖iteratedFDeriv ℝ j (fun x => T i x • (EuclideanSpace.single i (1 : ℝ) : Euc d)) x‖ ≤ b := by
    intro i _
    set c : ℝ →L[ℝ] Euc d := ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i (1 : ℝ) : Euc d)
    have hc : ‖c‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun t => ?_
      simp [c, norm_smul]
    have e : (fun x => T i x • (EuclideanSpace.single i (1 : ℝ) : Euc d)) = c ∘ T i := by
      funext x; simp [c]
    rw [e]
    have h1 := c.norm_iteratedFDeriv_comp_left (((hT i).of_le (by exact_mod_cast hj)).contDiffAt
      (x := x)) (le_refl (j : WithTop ℕ∞))
    have h2 := hb i j hj x
    have h3 : 0 ≤ ‖iteratedFDeriv ℝ j (T i) x‖ := norm_nonneg _
    calc _ ≤ ‖c‖ * ‖iteratedFDeriv ℝ j (T i) x‖ := h1
      _ ≤ 1 * ‖iteratedFDeriv ℝ j (T i) x‖ := mul_le_mul_of_nonneg_right hc h3
      _ ≤ b := by rw [one_mul]; exact h2
  calc _ ≤ ∑ i : Fin d, b := Finset.sum_le_sum this
    _ = d * b := by simp

theorem tcb_norm_le_sum (w : Euc d) : ‖w‖ ≤ ∑ j, |w j| := by
  have h : w = ∑ j, w j • (EuclideanSpace.single j (1 : ℝ) : Euc d) := by
    ext b
    simp [Pi.single_apply]
  conv_lhs => rw [h]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
  simp [norm_smul]

theorem tcb_matVec_clm (hd : 1 ≤ d) (M : Matrix (Fin d) (Fin d) ℝ) (MB : ℝ) (hM : PDE.MatBound MB M) :
    ∃ T : Euc d →L[ℝ] Euc d, (∀ v, T v = Torus.matVec M v) ∧ ‖T‖ ≤ (d : ℝ) ^ 2 * MB := by
  have hMB : 0 ≤ MB := (abs_nonneg _).trans (hM ⟨0, hd⟩ ⟨0, hd⟩)
  refine ⟨LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M), fun v => rfl, ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have h1 : ∀ j : Fin d, |Torus.matVec M v j| ≤ d * MB * ‖v‖ := by
    intro j
    rw [HRS.Whole.Q09B.q09b_matVec_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |M j i * v i| ≤ ∑ i : Fin d, MB * ‖v‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          have := PiLp.norm_apply_le v i
          rw [Real.norm_eq_abs] at this
          exact mul_le_mul (hM j i) this (abs_nonneg _) hMB
      _ = d * MB * ‖v‖ := by simp; ring
  show ‖Torus.matVec M v‖ ≤ _
  refine (tcb_norm_le_sum _).trans ?_
  calc ∑ j, |Torus.matVec M v j| ≤ ∑ j : Fin d, (d * MB * ‖v‖) := Finset.sum_le_sum fun j _ => h1 j
    _ = (d : ℝ) ^ 2 * MB * ‖v‖ := by simp; ring

/-! ### The gradient of `V_L` -/

theorem tcb_grad_eq (VL : Euc d → ℝ) :
    gradient VL = (InnerProductSpace.toDual ℝ (Euc d)).symm ∘ fderiv ℝ VL := rfl

theorem tcb_grad_contDiff (VL : Euc d → ℝ) (m : ℕ) (hV : ContDiff ℝ ∞ VL) :
    ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (gradient VL) := by
  rw [tcb_grad_eq]
  refine (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp ?_
  refine hV.fderiv_right ?_
  push_cast
  exact_mod_cast le_top

theorem tcb_grad_iter_norm (VL : Euc d → ℝ) (j : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ j (gradient VL) x‖ = ‖iteratedFDeriv ℝ (j + 1) VL x‖ := by
  rw [tcb_grad_eq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, norm_iteratedFDeriv_fderiv]

theorem tcb_VL_grad_central {ζ : Euc d → ℝ} (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) (L : ℝ) (hL : 1 ≤ L)
    (V : Euc d → ℝ) (hV1 : ContDiff ℝ ∞ V) (ΛV G₀ V₀ : ℝ)
    (hΛ0 : 0 ≤ ΛV) (hG0 : 0 ≤ G₀) (hV0₀ : 0 ≤ V₀)
    (hV2 : ∀ x : Euc d, ‖iteratedFDeriv ℝ 2 V x‖ ≤ ΛV)
    (hV3 : ‖gradient V 0‖ ≤ G₀) (hV0 : |V 0| ≤ V₀)
    (Kz : ℕ → ℝ) (hKz : ∀ (i : ℕ) (y : Euc d), ‖iteratedFDeriv ℝ i ζ y‖ ≤ Kz i)
    (hKz0 : ∀ i, 0 ≤ Kz i) (M : ℝ) (hM : V₀ + G₀ + ΛV ≤ M) (y : Euc d) :
    ‖iteratedFDeriv ℝ 1 (fun x => ζ (L⁻¹ • x) * V x) y‖ ≤ (Kz 0 + Kz 1) * M * (1 + ‖y‖) := by
  have hL0 : 0 < L := by linarith
  have ha0 : 0 < L⁻¹ := inv_pos.2 hL0
  have ha1 : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL
  have haL : L⁻¹ * L = 1 := inv_mul_cancel₀ hL0.ne'
  have hM0 : 0 ≤ M := by linarith
  have hζL : ContDiff ℝ ∞ (fun z : Euc d => ζ (L⁻¹ • z)) := hζ.1.comp (contDiff_id.const_smul L⁻¹)
  have hle := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) hζL hV1 y (n := 1) (by exact_mod_cast le_top)
  refine hle.trans ?_
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_zero,
    Nat.sub_self]
  set r := ‖y‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hX0 : ‖iteratedFDeriv ℝ 0 (fun z => ζ (L⁻¹ • z)) y‖ ≤ Kz 0 :=
    tca_zetaL_le hζ L hL Kz hKz hKz0 0 y
  have hD1 : ‖iteratedFDeriv ℝ 1 V y‖ ≤ G₀ + ΛV * r := by
    rw [norm_iteratedFDeriv_one]
    exact tca_fderiv_bound V hV1 ΛV G₀ hΛ0 hV2 hV3 y
  have hterm0 : ‖iteratedFDeriv ℝ 0 (fun z => ζ (L⁻¹ • z)) y‖ * ‖iteratedFDeriv ℝ 1 V y‖ ≤
      Kz 0 * M * (1 + r) := by
    calc _ ≤ Kz 0 * (G₀ + ΛV * r) :=
          mul_le_mul hX0 hD1 (norm_nonneg _) (hKz0 0)
      _ ≤ Kz 0 * (M * (1 + r)) := by
          refine mul_le_mul_of_nonneg_left ?_ (hKz0 0)
          nlinarith
      _ = Kz 0 * M * (1 + r) := by ring
  have hterm1 : ‖iteratedFDeriv ℝ 1 (fun z => ζ (L⁻¹ • z)) y‖ * ‖iteratedFDeriv ℝ 0 V y‖ ≤
      Kz 1 * M * (1 + r) := by
    by_cases hy : L / 3 ≤ r
    · rw [tca_zero_far L hL0 ζ hζ 1 (tca_zeta_contDiff hζ 1) y hy, zero_mul]
      exact mul_nonneg (mul_nonneg (hKz0 1) hM0) (by linarith)
    · push_neg at hy
      have hXs := tca_zetaL_le_small hζ L hL Kz hKz 1 le_rfl y
      have hVy : ‖iteratedFDeriv ℝ 0 V y‖ ≤ V₀ + (G₀ + ΛV * r) * r := by
        rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
        exact tca_val_bound V hV1 ΛV G₀ V₀ hΛ0 hV2 hV3 hV0 y
      have hs : L⁻¹ * r ≤ 1 / 3 := by
        have h1 := mul_le_mul_of_nonneg_left hy.le ha0.le
        have h2 : L⁻¹ * (L / 3) = 1 / 3 := by rw [← mul_div_assoc, haL]
        linarith
      have h1 : ‖iteratedFDeriv ℝ 1 (fun z => ζ (L⁻¹ • z)) y‖ * ‖iteratedFDeriv ℝ 0 V y‖ ≤
          (L⁻¹ * Kz 1) * (V₀ + (G₀ + ΛV * r) * r) :=
        mul_le_mul hXs hVy (norm_nonneg _) (mul_nonneg ha0.le (hKz0 1))
      have h2 : L⁻¹ * (V₀ + (G₀ + ΛV * r) * r) ≤ M * (1 + r) := by
        have e : L⁻¹ * (V₀ + (G₀ + ΛV * r) * r) =
            L⁻¹ * V₀ + G₀ * (L⁻¹ * r) + ΛV * r * (L⁻¹ * r) := by ring
        have b1 : L⁻¹ * V₀ ≤ V₀ := by nlinarith
        have b2 : G₀ * (L⁻¹ * r) ≤ G₀ * r := by
          have : L⁻¹ * r ≤ r := by nlinarith
          nlinarith
        have b3 : ΛV * r * (L⁻¹ * r) ≤ ΛV * r := by
          have : ΛV * r * (L⁻¹ * r) ≤ ΛV * r * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hΛ0 hr0)
            linarith
          linarith
        rw [e]
        nlinarith
      calc _ ≤ (L⁻¹ * Kz 1) * (V₀ + (G₀ + ΛV * r) * r) := h1
        _ = Kz 1 * (L⁻¹ * (V₀ + (G₀ + ΛV * r) * r)) := by ring
        _ ≤ Kz 1 * (M * (1 + r)) := mul_le_mul_of_nonneg_left h2 (hKz0 1)
        _ = Kz 1 * M * (1 + r) := by ring
  nlinarith

end HRS.MS.ToriCoefB
