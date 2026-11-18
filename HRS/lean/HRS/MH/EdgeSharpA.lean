import HRS.Prob.Metrics

/-!
# EdgeSharp Group A: the test function `Φ = c sin ∘ ℓ` (packets A1, A2, A3)

Statements copied verbatim from `HRS/MH/EdgeSharpSpec.lean` (Group A).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.EdgeSharp

open HRS

/-! ### Group A: the test function `Φ = c sin ∘ ℓ` (pure analysis on a normed space) -/

section GroupA

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- Helper for [A1]/[A2]: `iteratedDeriv j sin = fun x => sin (x + j π/2)`. -/
private theorem iteratedDeriv_sin_eq_aux (j : ℕ) :
    iteratedDeriv j Real.sin = fun x => Real.sin (x + j * (Real.pi / 2)) := by
  induction j with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have h : HasDerivAt (fun x => Real.sin (x + n * (Real.pi / 2))) (Real.cos (x + n * (Real.pi / 2))) x := by
      simpa using ((hasDerivAt_id x).add_const ((n : ℝ) * (Real.pi / 2))).sin
    rw [h.deriv, ← Real.sin_add_pi_div_two]
    congr 1
    push_cast
    ring

/-- Helper: `|iteratedFDeriv ℝ j sin x| ≤ 1`. -/
private theorem norm_iteratedFDeriv_sin_le_one (j : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ j Real.sin x‖ ≤ 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_sin_eq_aux, Real.norm_eq_abs]
  exact Real.abs_sin_le_one _

/-- Helper: `iteratedDeriv 3 sin x = -cos x`. -/
private theorem iteratedDeriv_three_sin_aux (x : ℝ) :
    iteratedDeriv 3 Real.sin x = -Real.cos x := by
  rw [iteratedDeriv_sin_eq_aux]
  show Real.sin (x + ((3 : ℕ) : ℝ) * (Real.pi / 2)) = -Real.cos x
  have h : x + ((3 : ℕ) : ℝ) * (Real.pi / 2) = (x + Real.pi / 2) + Real.pi := by
    push_cast; ring
  rw [h, Real.sin_add_pi, Real.sin_add_pi_div_two]

/-- [A1] `‖D^j (c sin ∘ ℓ)(z)‖ ≤ |c| ‖ℓ‖^j` for every `j`.  Route: `iteratedDeriv j sin = fun x => sin (x + j π/2)` by induction
(`iteratedDeriv_succ`, `Real.deriv_sin`, `Real.sin_add_pi_div_two`; no Mathlib lemma `iteratedDeriv_sin`), hence
`‖iteratedFDeriv ℝ j sin t‖ = ‖iteratedDeriv j sin t‖ ≤ 1` (`norm_iteratedFDeriv_eq_norm_iteratedDeriv`, `Real.abs_sin_le_one`);
`ContinuousLinearMap.iteratedFDeriv_comp_right` (needs `ContDiff ℝ j sin`, `Real.contDiff_sin`) and
`ContinuousMultilinearMap.norm_compContinuousLinearMap_le`; the factor `c` by `iteratedFDeriv_const_smul_apply`. -/
theorem norm_iteratedFDeriv_sin_comp_le (ℓ : B →L[ℝ] ℝ) (c : ℝ) (j : ℕ) (z : B) :
    ‖iteratedFDeriv ℝ j (fun z => c * Real.sin (ℓ z)) z‖ ≤ |c| * ‖ℓ‖ ^ j := by
  have hfun : (fun z => c * Real.sin (ℓ z)) = (c • Real.sin) ∘ ℓ := by
    funext z; simp [smul_eq_mul]
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right (f := c • Real.sin) ℓ
    (Real.contDiff_sin.const_smul c) z (le_refl _)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [iteratedFDeriv_const_smul_apply Real.contDiff_sin.contDiffAt, norm_smul, Real.norm_eq_abs,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h1 := norm_iteratedFDeriv_sin_le_one j (ℓ z)
  have h2 : ‖iteratedFDeriv ℝ j Real.sin (ℓ z)‖ * |c| ≤ |c| := by
    nlinarith [abs_nonneg c, norm_nonneg (iteratedFDeriv ℝ j Real.sin (ℓ z))]
  calc |c| * ‖iteratedFDeriv ℝ j Real.sin (ℓ z)‖ * ‖ℓ‖ ^ j
      = (‖iteratedFDeriv ℝ j Real.sin (ℓ z)‖ * |c|) * ‖ℓ‖ ^ j := by ring
    _ ≤ |c| * ‖ℓ‖ ^ j := mul_le_mul_of_nonneg_right h2 (pow_nonneg (norm_nonneg _) j)

/-- [A2] Third derivative: `D³(c sin ∘ ℓ)(z) = -c cos(ℓ z) · (ℓ ⊗ ℓ ⊗ ℓ)`, with the trilinear map used in
`SatisfiesCubicFormula`.  Route: `ContinuousLinearMap.iteratedFDeriv_comp_right` with `i = 3`; `iteratedFDeriv ℝ 3 sin t = (iteratedDeriv 3 sin t) • mkPiAlgebraFin ℝ 3 ℝ`
(`iteratedFDeriv_eq_equiv_comp`, `ContinuousMultilinearMap.piFieldEquiv`, or ext + `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod`
and `ContinuousMultilinearMap.mkPiAlgebraFin_apply`), `iteratedDeriv 3 sin = -cos` by `iteratedDeriv_succ` three times;
finish by `ext m` and `ContinuousMultilinearMap.compContinuousLinearMap_apply` (there is no named `smul_compContinuousLinearMap` lemma). -/
theorem iteratedFDeriv_three_sin_comp (ℓ : B →L[ℝ] ℝ) (c : ℝ) (z : B) :
    iteratedFDeriv ℝ 3 (fun z => c * Real.sin (ℓ z)) z =
      (-c * Real.cos (ℓ z)) •
        (ContinuousMultilinearMap.mkPiAlgebraFin ℝ 3 ℝ).compContinuousLinearMap (fun _ : Fin 3 => ℓ) := by
  have hfun : (fun z => c * Real.sin (ℓ z)) = (c • Real.sin) ∘ ℓ := by
    funext z; simp [smul_eq_mul]
  have key : iteratedFDeriv ℝ 3 (c • Real.sin) (ℓ z) =
      (-c * Real.cos (ℓ z)) • ContinuousMultilinearMap.mkPiAlgebraFin ℝ 3 ℝ := by
    refine ContinuousMultilinearMap.ext fun m => ?_
    rw [iteratedFDeriv_const_smul_apply Real.contDiff_sin.contDiffAt, smul_apply, smul_apply,
      iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
      List.prod_ofFn, iteratedDeriv_three_sin_aux, smul_eq_mul, smul_eq_mul]
    ring
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right (f := c • Real.sin) (n := 3) ℓ
    (Real.contDiff_sin.const_smul c) z (by norm_num), key]
  refine ContinuousMultilinearMap.ext fun m => ?_
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]

/-- [A3] `Φ = c sin ∘ ℓ` with `c = 1/(1+∑_{j≤5}‖ℓ‖^j)` lies in the `C_b^5` unit ball.  Route: `ContDiff` by `Real.contDiff_sin.comp`
and `ℓ.contDiff`; `BddAbove` for `j ≤ 5` from [A1] (`⟨c ‖ℓ‖^j, ..⟩`); `cbNorm 5 Φ = ∑_{j<6} ⨆ z ‖D^jΦ z‖ ≤ ∑ c ‖ℓ‖^j ≤ 1`
(`ciSup_le`, `Finset.sum_le_sum`, `Finset.mul_sum`, `div_mul_cancel`). -/
theorem sinPhi_mem_cbUnitBall (ℓ : B →L[ℝ] ℝ) :
    (fun z => (1 / (1 + ∑ j ∈ Finset.range 6, ‖ℓ‖ ^ j)) * Real.sin (ℓ z)) ∈ CbUnitBall B 5 := by
  have : Nonempty B := ⟨0⟩
  have hS : 0 ≤ ∑ j ∈ Finset.range 6, ‖ℓ‖ ^ j :=
    Finset.sum_nonneg (fun j _ => pow_nonneg (norm_nonneg _) j)
  have hpos : (0 : ℝ) < 1 + ∑ j ∈ Finset.range 6, ‖ℓ‖ ^ j := by linarith
  have hc0 : 0 ≤ 1 / (1 + ∑ j ∈ Finset.range 6, ‖ℓ‖ ^ j) := by positivity
  have hcS : (1 / (1 + ∑ j ∈ Finset.range 6, ‖ℓ‖ ^ j)) * (∑ j ∈ Finset.range 6, ‖ℓ‖ ^ j) ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one hpos]
    linarith
  refine ⟨?_, ?_, ?_⟩
  · exact contDiff_const.mul (Real.contDiff_sin.comp ℓ.contDiff)
  · intro j _
    refine ⟨(1 / (1 + ∑ j ∈ Finset.range 6, ‖ℓ‖ ^ j)) * ‖ℓ‖ ^ j, ?_⟩
    rintro _ ⟨z, rfl⟩
    have := norm_iteratedFDeriv_sin_comp_le ℓ (1 / (1 + ∑ j ∈ Finset.range 6, ‖ℓ‖ ^ j)) j z
    rwa [abs_of_nonneg hc0] at this
  · unfold cbNorm
    calc ∑ j ∈ Finset.range (5 + 1), ⨆ z : B,
          ‖iteratedFDeriv ℝ j (fun z => (1 / (1 + ∑ j ∈ Finset.range 6, ‖ℓ‖ ^ j)) * Real.sin (ℓ z)) z‖
        ≤ ∑ j ∈ Finset.range (5 + 1), (1 / (1 + ∑ j ∈ Finset.range 6, ‖ℓ‖ ^ j)) * ‖ℓ‖ ^ j := by
          refine Finset.sum_le_sum (fun j _ => ciSup_le (fun z => ?_))
          have := norm_iteratedFDeriv_sin_comp_le ℓ (1 / (1 + ∑ j ∈ Finset.range 6, ‖ℓ‖ ^ j)) j z
          rwa [abs_of_nonneg hc0] at this
      _ = (1 / (1 + ∑ j ∈ Finset.range 6, ‖ℓ‖ ^ j)) * ∑ j ∈ Finset.range 6, ‖ℓ‖ ^ j := by
          rw [Finset.mul_sum]
      _ ≤ 1 := hcS

end GroupA

end HRS.MH.EdgeSharp
