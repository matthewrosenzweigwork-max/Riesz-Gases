import HRS.MS.SA12LimitDefs
import HRS.PDE.ToolboxRd.Fourier

/-!
# S.A.12 L14: Fourier interpolation between Sobolev orders `-q` and `m`
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

variable {d : ℕ}

/-- The interpolation inequality for the squared Sobolev norms (`0 < a < 1`, `r = -q a + m (1-a)`). -/
theorem sa12l14_sq_interp {q m r a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hr : r = -q * a + m * (1 - a)) {u : Euc d → ℝ}
    (h1 : HRS.PDE.ToolboxRd.MemSobolev (-q) u) (h2 : HRS.PDE.ToolboxRd.MemSobolev m u) (h3 : HRS.PDE.ToolboxRd.MemSobolev r u) :
    HRS.PDE.ToolboxRd.sobolevNormSq r u ≤ HRS.PDE.ToolboxRd.sobolevNormSq (-q) u ^ a * HRS.PDE.ToolboxRd.sobolevNormSq m u ^ (1 - a) := by
  set P : Euc d → ℝ := fun ξ => ‖HRS.PDE.ToolboxRd.fourierL2 u ξ‖ ^ 2 with hP
  set W : Euc d → ℝ := fun ξ => 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 with hW
  have hW0 : ∀ ξ, 0 < W ξ := fun ξ => by simp only [hW]; positivity
  have hP0 : ∀ ξ, 0 ≤ P ξ := fun ξ => by simp only [hP]; positivity
  set b : ℝ := 1 - a with hb
  have hb0 : 0 < b := by linarith
  have hb1 : b < 1 := by linarith
  have hmeas : ∀ s : ℝ, AEMeasurable (fun ξ => ENNReal.ofReal (W ξ ^ s * P ξ)) volume := by
    intro s
    have := HRS.PDE.ToolboxRd.FourierAux.aesm_wt_mul
      (HRS.PDE.ToolboxRd.FourierAux.aestronglyMeasurable_fourierL2 h2.1) s
    exact ENNReal.measurable_ofReal.comp_aemeasurable this.aemeasurable
  -- pointwise factorization
  have hfac : ∀ ξ, ENNReal.ofReal (W ξ ^ r * P ξ) =
      (ENNReal.ofReal (W ξ ^ (-q) * P ξ)) ^ a * (ENNReal.ofReal (W ξ ^ m * P ξ)) ^ b := by
    intro ξ
    have e1 : (W ξ ^ (-q) * P ξ) ^ a = W ξ ^ (-q * a) * P ξ ^ a := by
      rw [Real.mul_rpow (Real.rpow_nonneg (hW0 ξ).le _) (hP0 ξ), ← Real.rpow_mul (hW0 ξ).le]
    have e2 : (W ξ ^ m * P ξ) ^ b = W ξ ^ (m * b) * P ξ ^ b := by
      rw [Real.mul_rpow (Real.rpow_nonneg (hW0 ξ).le _) (hP0 ξ), ← Real.rpow_mul (hW0 ξ).le]
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (Real.rpow_nonneg (hW0 ξ).le _) (hP0 ξ)) ha0.le,
      ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (Real.rpow_nonneg (hW0 ξ).le _) (hP0 ξ)) hb0.le,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (mul_nonneg (Real.rpow_nonneg (hW0 ξ).le _) (hP0 ξ)) _),
      e1, e2]
    congr 1
    have e3 : W ξ ^ (-q * a) * P ξ ^ a * (W ξ ^ (m * b) * P ξ ^ b) =
        W ξ ^ (-q * a + m * b) * P ξ ^ (a + b) := by
      rw [Real.rpow_add (hW0 ξ), Real.rpow_add' (hP0 ξ) (by linarith)]
      ring
    rw [e3, show a + b = 1 by simp [hb], Real.rpow_one, hr]
  have hpq : (1 / a).HolderConjugate (1 / b) := by
    rw [Real.holderConjugate_iff]
    refine ⟨by rw [lt_div_iff₀ ha0]; linarith, ?_⟩
    simp only [one_div, inv_inv]
    simp [hb]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq
    (f := fun ξ => (ENNReal.ofReal (W ξ ^ (-q) * P ξ)) ^ a)
    (g := fun ξ => (ENNReal.ofReal (W ξ ^ m * P ξ)) ^ b)
    ((hmeas (-q)).pow_const _) ((hmeas m).pow_const _)
  have ea : ∀ F : ℝ≥0∞, (F ^ a) ^ (1 / a) = F := fun F => by
    rw [← ENNReal.rpow_mul, mul_one_div_cancel ha0.ne', ENNReal.rpow_one]
  have eb : ∀ F : ℝ≥0∞, (F ^ b) ^ (1 / b) = F := fun F => by
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hb0.ne', ENNReal.rpow_one]
  simp only [Pi.mul_apply, ea, eb, one_div_one_div] at hH
  have hint : ∀ s : ℝ, HRS.PDE.ToolboxRd.MemSobolev s u →
      ∫⁻ ξ, ENNReal.ofReal (W ξ ^ s * P ξ) = ENNReal.ofReal (HRS.PDE.ToolboxRd.sobolevNormSq s u) := by
    intro s hs
    unfold HRS.PDE.ToolboxRd.sobolevNormSq
    rw [ofReal_integral_eq_lintegral_ofReal hs.2 (Filter.Eventually.of_forall fun ξ =>
      mul_nonneg (Real.rpow_nonneg (hW0 ξ).le _) (hP0 ξ))]
  have hlhs := hint r h3
  rw [show (fun ξ => ENNReal.ofReal (W ξ ^ r * P ξ)) =
      fun ξ => (ENNReal.ofReal (W ξ ^ (-q) * P ξ)) ^ a * (ENNReal.ofReal (W ξ ^ m * P ξ)) ^ b from
    funext hfac] at hlhs
  rw [hint (-q) h1, hint m h2] at hH
  have hS0 : ∀ s, 0 ≤ HRS.PDE.ToolboxRd.sobolevNormSq s u := fun s =>
    integral_nonneg fun ξ => mul_nonneg (Real.rpow_nonneg (hW0 ξ).le _) (hP0 ξ)
  have hle : ENNReal.ofReal (HRS.PDE.ToolboxRd.sobolevNormSq r u) ≤
      ENNReal.ofReal (HRS.PDE.ToolboxRd.sobolevNormSq (-q) u ^ a * HRS.PDE.ToolboxRd.sobolevNormSq m u ^ b) := by
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (hS0 _) _),
      ← ENNReal.ofReal_rpow_of_nonneg (hS0 _) ha0.le,
      ← ENNReal.ofReal_rpow_of_nonneg (hS0 _) hb0.le, ← hlhs]
    exact hH
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.rpow_nonneg (hS0 _) _)
    (Real.rpow_nonneg (hS0 _) _))).1 hle


-- BEGIN SA12.L14
theorem fourier_interpolation (hd : 1 ≤ d) (q m r : ℝ)
    (hq : 0 < q) (hm : 0 ≤ m) (hr0 : -q ≤ r) (hr1 : r ≤ m)
    (u : Euc d → ℝ) (hu : HRS.PDE.ToolboxRd.MemSobolev m u) :
    sobolevNormE r u ≤
      (sobolevNormE (-q) u) ^ ((m - r) / (m + q)) *
      (sobolevNormE m u) ^ ((r + q) / (m + q)) := by
  have hmq : 0 < m + q := by linarith
  have h1 : HRS.PDE.ToolboxRd.MemSobolev (-q) u :=
    HRS.PDE.ToolboxRd.FourierAux.memSobolev_mono (by linarith) hu
  have h3 : HRS.PDE.ToolboxRd.MemSobolev r u :=
    HRS.PDE.ToolboxRd.FourierAux.memSobolev_mono hr1 hu
  rcases hr1.lt_or_eq with hrm | hrm
  swap
  · subst hrm
    simp [sub_self, div_self hmq.ne']
  rcases hr0.lt_or_eq with hrq | hrq
  swap
  · rw [← hrq]
    have e1 : (m - -q) / (m + q) = 1 := by rw [sub_neg_eq_add, div_self hmq.ne']
    have e2 : (-q + q) / (m + q) = 0 := by simp
    rw [e1, e2]
    simp
  set a : ℝ := (m - r) / (m + q) with ha
  set b : ℝ := (r + q) / (m + q) with hb
  have ha0 : 0 < a := div_pos (by linarith) hmq
  have hb0 : 0 < b := div_pos (by linarith) hmq
  have hab : b = 1 - a := by rw [ha, hb]; field_simp; ring
  have ha1 : a < 1 := by linarith
  have hr : r = -q * a + m * (1 - a) := by rw [ha]; field_simp; ring
  have hsq := sa12l14_sq_interp ha0 ha1 hr h1 hu h3
  rw [← hab] at hsq
  have hS0 : ∀ s, 0 ≤ HRS.PDE.ToolboxRd.sobolevNormSq s u := fun s =>
    integral_nonneg fun ξ => mul_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity)
  have hN : ∀ s, HRS.PDE.ToolboxRd.MemSobolev s u →
      sobolevNormE s u = ENNReal.ofReal (Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq s u)) := by
    intro s hs
    simp [HRS.Whole.sobolevNormE, hs]
  rw [hN r h3, hN (-q) h1, hN m hu,
    ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) ha0.le,
    ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) hb0.le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (Real.sqrt_nonneg _) _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsqrt : ∀ (x c : ℝ), 0 ≤ x → Real.sqrt (x ^ c) = Real.sqrt x ^ c := by
    intro x c hx
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx, ← Real.rpow_mul hx, mul_comm]
  calc Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq r u)
      ≤ Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (-q) u ^ a *
          HRS.PDE.ToolboxRd.sobolevNormSq m u ^ b) := Real.sqrt_le_sqrt hsq
    _ = _ := by
        rw [Real.sqrt_mul (Real.rpow_nonneg (hS0 _) _), hsqrt _ _ (hS0 _), hsqrt _ _ (hS0 _)]
-- END SA12.L14

end HRS.MH.AdjointRd.Phase2SA12Limit
