import HRS.MD.Cov211Trunc

/-!
# Packet COV211, pointwise lower bounds for `W_2`, `W_1`, `d_j` by the second-moment discrepancy

For probability measures `P, Q` on `ℝ` with sub-Gaussian tails `P(|z| > x) ≤ 4 e^{-x²/(2D)}`:
* `W_2(P,Q) ≥ |∫z²dP - ∫z²dQ| / (2√D')` (`V:eq:response-covariance-W2`);
* `W_1`, `d_j` with the truncation `FL L` (`V:eq:response-truncate-W1`, `V:eq:response-truncate-smooth`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MD.Cov211

/-- `W₂` dominates the second-moment discrepancy. -/
theorem w2_lower (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hP : Integrable (fun x : ℝ => x ^ 2) P) (hQ : Integrable (fun x : ℝ => x ^ 2) Q)
    (D' : ℝ) (hD' : 0 < D') (hPD : ∫ x, x ^ 2 ∂P ≤ D') (hQD : ∫ x, x ^ 2 ∂Q ≤ D') :
    ENNReal.ofReal |∫ x, x ^ 2 ∂P - ∫ x, x ^ 2 ∂Q| ≤
      ENNReal.ofReal (2 * Real.sqrt D') * wassersteinE 2 P Q := by
  have h := second_moment_le_wasserstein P Q hP hQ
  set a := ∫ x, x ^ 2 ∂P
  set b := ∫ x, x ^ 2 ∂Q
  have ha : 0 ≤ a := integral_nonneg fun x => sq_nonneg x
  have hb : 0 ≤ b := integral_nonneg fun x => sq_nonneg x
  have hsa : Real.sqrt a ≤ Real.sqrt D' := Real.sqrt_le_sqrt hPD
  have hsb : Real.sqrt b ≤ Real.sqrt D' := Real.sqrt_le_sqrt hQD
  have key : |a - b| ≤ 2 * Real.sqrt D' * |Real.sqrt a - Real.sqrt b| := by
    have e : a - b = (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) := by
      have := Real.sq_sqrt ha; have := Real.sq_sqrt hb; nlinarith
    rw [e, abs_mul, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    linarith
  calc ENNReal.ofReal |a - b| ≤ ENNReal.ofReal (2 * Real.sqrt D' * |Real.sqrt a - Real.sqrt b|) :=
        ENNReal.ofReal_le_ofReal key
    _ = ENNReal.ofReal (2 * Real.sqrt D') * ENNReal.ofReal |Real.sqrt a - Real.sqrt b| :=
        ENNReal.ofReal_mul (by positivity)
    _ ≤ _ := by gcongr

/-- Universal constant of the `W₁` truncation bound. -/
theorem w1_lower : ∃ M : ℝ, 0 < M ∧ ∀ (P Q : Measure ℝ) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (D : ℝ), 0 < D →
    (∀ x : ℝ, 0 ≤ x → P {z | x < |z|} ≤ ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D)))) →
    (∀ x : ℝ, 0 ≤ x → Q {z | x < |z|} ≤ ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D)))) →
    ∀ L : ℝ, 1 ≤ L →
    ENNReal.ofReal (|∫ z, z ^ 2 ∂P - ∫ z, z ^ 2 ∂Q| - 40 * D * Real.exp (-L ^ 2 / (8 * D))) ≤
      ENNReal.ofReal (M * L) * wassersteinE 1 P Q := by
  obtain ⟨M, hM0, hM⟩ := FL_bounds 1
  refine ⟨M, hM0, fun P Q _ _ D hD htP htQ L hL => ?_⟩
  have hL0 : 0 < L := by linarith
  obtain ⟨hb, hb1⟩ := hM L hL
  have hKpos : 0 < M * L := by positivity
  have hlip := lip_test_le_wasserstein_one P Q (FL L) (M * L) hKpos
    (FL_contDiff (n := 0) L).continuous.measurable (M * L ^ 2)
    (fun x => by
      have := hb 0 (by norm_num) x
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this)
    (fun x y => FL_lipschitz hL0 hb1 x y)
  have hd := abs_sq_diff_le P Q D hD htP htQ hL0
  set Δ := |∫ z, FL L z ∂P - ∫ z, FL L z ∂Q|
  calc ENNReal.ofReal (|∫ z, z ^ 2 ∂P - ∫ z, z ^ 2 ∂Q| - 40 * D * Real.exp (-L ^ 2 / (8 * D)))
      ≤ ENNReal.ofReal Δ := ENNReal.ofReal_le_ofReal (by linarith)
    _ = ENNReal.ofReal (M * L) * ENNReal.ofReal (Δ / (M * L)) := by
        rw [← ENNReal.ofReal_mul hKpos.le]; congr 1; field_simp
    _ ≤ _ := by gcongr

/-- The `d_j` truncation bound, `j ≥ 0`. -/
theorem dj_lower (j : ℕ) : ∃ M : ℝ, 0 < M ∧ ∀ (P Q : Measure ℝ) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (D : ℝ), 0 < D →
    (∀ x : ℝ, 0 ≤ x → P {z | x < |z|} ≤ ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D)))) →
    (∀ x : ℝ, 0 ≤ x → Q {z | x < |z|} ≤ ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D)))) →
    ∀ L : ℝ, 1 ≤ L →
    ENNReal.ofReal (|∫ z, z ^ 2 ∂P - ∫ z, z ^ 2 ∂Q| - 40 * D * Real.exp (-L ^ 2 / (8 * D))) ≤
      ENNReal.ofReal (M * L ^ 2) * ENNReal.ofReal (smoothDist j P Q) := by
  obtain ⟨M, hM0, hM⟩ := FL_bounds j
  refine ⟨((j : ℝ) + 1) * M, by positivity, fun P Q _ _ D hD htP htQ L hL => ?_⟩
  have hL0 : 0 < L := by linarith
  obtain ⟨hb, -⟩ := hM L hL
  have hCn : 0 < ((j : ℝ) + 1) * M * L ^ 2 := by positivity
  have hball := FL_mem_cbUnitBall j hM0 hL hb
  have hFLi : ∀ (R : Measure ℝ) [IsProbabilityMeasure R], Integrable (fun z => FL L z) R := by
    intro R _
    refine Integrable.of_bound (FL_contDiff (n := 0) L).continuous.aestronglyMeasurable (M * L ^ 2)
      (Filter.Eventually.of_forall fun z => ?_)
    have := hb 0 (Nat.zero_le _) z
    rwa [norm_iteratedFDeriv_zero] at this
  have hbt := ball_test_le_smoothDist j P Q (FL L) _ hCn hball (hFLi P) (hFLi Q)
  have hd := abs_sq_diff_le P Q D hD htP htQ hL0
  set Δ := |∫ z, FL L z ∂P - ∫ z, FL L z ∂Q|
  have hsd := smoothDist_nonneg j P Q
  calc ENNReal.ofReal (|∫ z, z ^ 2 ∂P - ∫ z, z ^ 2 ∂Q| - 40 * D * Real.exp (-L ^ 2 / (8 * D)))
      ≤ ENNReal.ofReal Δ := ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ ENNReal.ofReal (((j : ℝ) + 1) * M * L ^ 2 * smoothDist j P Q) :=
        ENNReal.ofReal_le_ofReal hbt
    _ = _ := by rw [ENNReal.ofReal_mul (by positivity)]

end HRS.MD.Cov211
