import HRS.MS.WsPrepAux15

/-!
# S21T2 packet A1: rate algebra of the window comparison (assembly step of `S21PrepMetric`)

The window comparison of `S21PrepMetric` is obtained from the window master (`s21m_master`, output
`Γ` with `law Ξ` compared to `γ0 * Γ`) and the initial comparison (`S21InitWin`, output `γ0` compared to the
transported initial path).  This file proves the arithmetic and the identification of the convolution:

* `s21t2_rate_algebra`: from the master bounds (`Cs Wt + F + εs`, `√Wt`-type `W_1` bound) with
  `F ≤ K₁ √N δ_N`, `Wt ≤ K₂ w_N`, `εs ≤ C_init (√N δ_N + i_N)`, `εw ≤ C_init (√N δ_N + j_N)`, get the two
  bounds of `S21PrepMetric` with one constant `C ≥ Cs K₂ + K₁ + C_init` and `C ≥ Cw √K₂ + K₁ + C_init`;
* `s21t2_window_bounds`: the same with the target law `Z` identified by `s21p_Zwin_law` as `γ0 * Γ`.

Pure real/ENNReal arithmetic: no hypothesis beyond the stated bounds and nonnegativity of the constants and rates.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.S21T2

open HRS (smoothDist wassersteinE)
open HRS.Whole HRS.MS.GenPath

/-- Rate algebra for the window comparison (real and `ℝ≥0∞` bounds). -/
theorem s21t2_rate_algebra {Cs Cw K1 K2 Cinit u i w j C : ℝ}
    (hCs : 0 ≤ Cs) (hCw : 0 ≤ Cw) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hCi : 0 ≤ Cinit)
    (hu : 0 ≤ u) (hi : 0 ≤ i) (hw : 0 ≤ w) (hj : 0 ≤ j) (hC : 0 ≤ C)
    (hC1 : Cs * K2 + K1 + Cinit ≤ C) (hC2 : Cw * Real.sqrt K2 + K1 + Cinit ≤ C)
    {S : ℝ} {Wt F εw W1 : ℝ≥0∞} {εs : ℝ}
    (hS : ENNReal.ofReal S ≤ ENNReal.ofReal Cs * Wt + F + ENNReal.ofReal εs)
    (hW1 : W1 ≤ ENNReal.ofReal Cw * Wt ^ (1 / 2 : ℝ) + F + εw)
    (hF : F ≤ ENNReal.ofReal (K1 * u)) (hWt : Wt ≤ ENNReal.ofReal (K2 * w))
    (hεs : εs ≤ Cinit * (u + i)) (hεw : εw ≤ ENNReal.ofReal (Cinit * (u + j))) :
    S ≤ C * (u + w + i) ∧ W1 ≤ ENNReal.ofReal (C * (u + Real.sqrt w + j)) := by
  have hsw : 0 ≤ Real.sqrt w := Real.sqrt_nonneg w
  have hsK : 0 ≤ Real.sqrt K2 := Real.sqrt_nonneg K2
  have hX1 : 0 ≤ u + w + i := by linarith
  have hX2 : 0 ≤ u + Real.sqrt w + j := by linarith
  constructor
  · -- first bound
    have h1 : ENNReal.ofReal Cs * Wt ≤ ENNReal.ofReal (Cs * (K2 * w)) := by
      calc ENNReal.ofReal Cs * Wt ≤ ENNReal.ofReal Cs * ENNReal.ofReal (K2 * w) := by gcongr
        _ = ENNReal.ofReal (Cs * (K2 * w)) := (ENNReal.ofReal_mul hCs).symm
    have hsum : ENNReal.ofReal S ≤ ENNReal.ofReal (Cs * (K2 * w) + K1 * u + Cinit * (u + i)) := by
      calc ENNReal.ofReal S ≤ ENNReal.ofReal Cs * Wt + F + ENNReal.ofReal εs := hS
        _ ≤ ENNReal.ofReal (Cs * (K2 * w)) + ENNReal.ofReal (K1 * u) + ENNReal.ofReal (Cinit * (u + i)) :=
            add_le_add (add_le_add h1 hF) (ENNReal.ofReal_le_ofReal hεs)
        _ = ENNReal.ofReal (Cs * (K2 * w) + K1 * u + Cinit * (u + i)) := by
            rw [ENNReal.ofReal_add (by positivity) (by nlinarith), ENNReal.ofReal_add (by positivity)
              (by nlinarith)]
    have hR : Cs * (K2 * w) + K1 * u + Cinit * (u + i) ≤ C * (u + w + i) := by
      nlinarith [mul_nonneg (mul_nonneg hCs hK2) hu, mul_nonneg (mul_nonneg hCs hK2) hi,
        mul_nonneg hK1 hw, mul_nonneg hK1 hi, mul_nonneg hCi hw, mul_nonneg hC hX1,
        mul_le_mul_of_nonneg_right hC1 hX1]
    have hpos : 0 ≤ C * (u + w + i) := mul_nonneg hC hX1
    exact (ENNReal.ofReal_le_ofReal_iff hpos).1 (hsum.trans (ENNReal.ofReal_le_ofReal hR))
  · -- second bound
    have hWt' : Wt ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt K2 * Real.sqrt w) := by
      calc Wt ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal (K2 * w)) ^ (1 / 2 : ℝ) :=
            ENNReal.rpow_le_rpow hWt (by norm_num)
        _ = ENNReal.ofReal ((K2 * w) ^ (1 / 2 : ℝ)) :=
            ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hK2 hw) (by norm_num)
        _ = ENNReal.ofReal (Real.sqrt K2 * Real.sqrt w) := by
            rw [← Real.sqrt_eq_rpow, Real.sqrt_mul hK2 w]
    have h1 : ENNReal.ofReal Cw * Wt ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Cw * (Real.sqrt K2 * Real.sqrt w)) := by
      calc ENNReal.ofReal Cw * Wt ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal Cw * ENNReal.ofReal (Real.sqrt K2 * Real.sqrt w) :=
            by gcongr
        _ = ENNReal.ofReal (Cw * (Real.sqrt K2 * Real.sqrt w)) := (ENNReal.ofReal_mul hCw).symm
    have hsum : W1 ≤ ENNReal.ofReal (Cw * (Real.sqrt K2 * Real.sqrt w) + K1 * u + Cinit * (u + j)) := by
      calc W1 ≤ ENNReal.ofReal Cw * Wt ^ (1 / 2 : ℝ) + F + εw := hW1
        _ ≤ ENNReal.ofReal (Cw * (Real.sqrt K2 * Real.sqrt w)) + ENNReal.ofReal (K1 * u) +
            ENNReal.ofReal (Cinit * (u + j)) := add_le_add (add_le_add h1 hF) hεw
        _ = ENNReal.ofReal (Cw * (Real.sqrt K2 * Real.sqrt w) + K1 * u + Cinit * (u + j)) := by
            rw [ENNReal.ofReal_add (by positivity) (by nlinarith), ENNReal.ofReal_add (by positivity)
              (by nlinarith)]
    have hR : Cw * (Real.sqrt K2 * Real.sqrt w) + K1 * u + Cinit * (u + j) ≤ C * (u + Real.sqrt w + j) := by
      nlinarith [mul_nonneg (mul_nonneg hCw hsK) hu, mul_nonneg (mul_nonneg hCw hsK) hj,
        mul_nonneg hK1 hsw, mul_nonneg hK1 hj, mul_nonneg hCi hsw, mul_nonneg hC hX2,
        mul_le_mul_of_nonneg_right hC2 hX2]
    exact hsum.trans (ENNReal.ofReal_le_ofReal hR)

/-- The window comparison with the target law identified as `γ0 * Γ` (`s21p_Zwin_law`). -/
theorem s21t2_window_bounds {d : ℕ} {m T : ℝ} {Cs Cw K1 K2 Cinit u i w j C : ℝ}
    (hCs : 0 ≤ Cs) (hCw : 0 ≤ Cw) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hCi : 0 ≤ Cinit)
    (hu : 0 ≤ u) (hi : 0 ≤ i) (hw : 0 ≤ w) (hj : 0 ≤ j) (hC : 0 ≤ C)
    (hC1 : Cs * K2 + K1 + Cinit ≤ C) (hC2 : Cw * Real.sqrt K2 + K1 + Cinit ≤ C)
    (Ξlaw Zlaw γ0 Γ : Measure (OscPath d m T)) [IsProbabilityMeasure γ0] [IsProbabilityMeasure Γ]
    {Wt F εw W1 : ℝ≥0∞} {εs : ℝ}
    (hZl : Zlaw = (γ0.prod Γ).map (fun z : OscPath d m T × OscPath d m T => z.1 + z.2))
    (hS : ENNReal.ofReal (smoothDist 2 Ξlaw ((γ0.prod Γ).map
        (fun z : OscPath d m T × OscPath d m T => z.1 + z.2))) ≤
      ENNReal.ofReal Cs * Wt + F + ENNReal.ofReal εs)
    (hW1 : wassersteinE 1 Ξlaw ((γ0.prod Γ).map
        (fun z : OscPath d m T × OscPath d m T => z.1 + z.2)) ≤ W1)
    (hW1' : W1 ≤ ENNReal.ofReal Cw * Wt ^ (1 / 2 : ℝ) + F + εw)
    (hF : F ≤ ENNReal.ofReal (K1 * u)) (hWt : Wt ≤ ENNReal.ofReal (K2 * w))
    (hεs : εs ≤ Cinit * (u + i)) (hεw : εw ≤ ENNReal.ofReal (Cinit * (u + j))) :
    smoothDist 2 Ξlaw Zlaw ≤ C * (u + w + i) ∧
      wassersteinE 1 Ξlaw Zlaw ≤ ENNReal.ofReal (C * (u + Real.sqrt w + j)) := by
  subst hZl
  have hS' : ENNReal.ofReal (smoothDist 2 Ξlaw ((γ0.prod Γ).map
        (fun z : OscPath d m T × OscPath d m T => z.1 + z.2))) ≤
      ENNReal.ofReal Cs * Wt + F + ENNReal.ofReal εs := hS
  have hW1'' : wassersteinE 1 Ξlaw ((γ0.prod Γ).map
        (fun z : OscPath d m T × OscPath d m T => z.1 + z.2)) ≤
      ENNReal.ofReal Cw * Wt ^ (1 / 2 : ℝ) + F + εw := hW1.trans hW1'
  exact s21t2_rate_algebra hCs hCw hK1 hK2 hCi hu hi hw hj hC hC1 hC2 hS' hW1'' hF hWt hεs hεw

end HRS.MS.S21T2
