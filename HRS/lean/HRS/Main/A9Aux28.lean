import HRS.Main.A9Aux27

/-!
# Packet A9, part 28: bounded `C²` test functions (trigonometric and cylinder-tail tests)

* `a9_mem_ball_of_bounds`: a `C²` function with all derivatives of order `≤ 2` bounded by `M` lies, after
  scaling by `1/(3M)`, in the `C_b²` unit ball;
* `a9_trig_mem`: `sin ∘ L`, `cos ∘ L` for a continuous linear functional `L`;
* `a9psi θ y = 1 - exp (-θ ‖y‖²)` and its bounds `|ψ| ≤ 1`, `‖Dψ‖ ≤ √θ`, `‖D²ψ‖ ≤ 6θ`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Main.A9

section Ball

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

theorem a9_mem_ball_of_bounds {f : B → ℝ} (hf : ContDiff ℝ 2 f) {M : ℝ} (hM : 0 < M)
    (hb : ∀ j ≤ 2, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ M) :
    (fun z => (1 / (3 * M)) * f z) ∈ CbUnitBall B 2 := by
  set c : ℝ := 1 / (3 * M) with hc
  have hc0 : 0 < c := by positivity
  have e : (fun z => c * f z) = c • f := by funext z; simp
  have hb' : ∀ j ≤ 2, ∀ z, ‖iteratedFDeriv ℝ j (fun z => c * f z) z‖ ≤ c * M := by
    intro j hj z
    rw [e, iteratedFDeriv_const_smul_apply (hf.of_le (by exact_mod_cast hj)).contDiffAt,
      norm_smul, Real.norm_eq_abs, abs_of_pos hc0]
    exact mul_le_mul_of_nonneg_left (hb j hj z) hc0.le
  refine ⟨contDiff_const.mul hf, fun j hj => ⟨c * M, ?_⟩, ?_⟩
  · rintro _ ⟨z, rfl⟩; exact hb' j hj z
  · unfold cbNorm
    calc ∑ j ∈ Finset.range (2 + 1), ⨆ z : B, ‖iteratedFDeriv ℝ j (fun z => c * f z) z‖
        ≤ ∑ j ∈ Finset.range (2 + 1), c * M := by
          refine Finset.sum_le_sum fun j hj => ?_
          exact Real.iSup_le (hb' j (by simpa [Nat.lt_succ_iff] using hj)) (by positivity)
      _ = 1 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hc]
          push_cast; field_simp

theorem a9_trig_mem (φ : ℝ → ℝ) (hφ : ContDiff ℝ 2 φ)
    (hb : ∀ j ≤ 2, ∀ u, ‖iteratedFDeriv ℝ j φ u‖ ≤ 1) (L : StrongDual ℝ B) :
    (fun z => (1 / (3 * max 1 (‖L‖ ^ 2))) * φ (L z)) ∈ CbUnitBall B 2 := by
  have hM : (0 : ℝ) < max 1 (‖L‖ ^ 2) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hL : ∀ j ≤ 2, ‖L‖ ^ j ≤ max 1 (‖L‖ ^ 2) := by
    intro j hj
    have h0 := norm_nonneg L
    interval_cases j
    · simp
    · rcases le_total ‖L‖ 1 with h | h
      · simpa using (le_max_of_le_left h)
      · simpa using le_max_of_le_right (by nlinarith)
    · exact le_max_right _ _
  have := a9_mem_ball_of_bounds (B := B) (f := fun z => φ (L z)) (hφ.comp L.contDiff) hM
    (fun j hj z => by
      have h2 := L.iteratedFDeriv_comp_right (hφ.of_le (by exact_mod_cast hj)) z (i := j) le_rfl
      have e : (fun z => φ (L z)) = φ ∘ L := rfl
      rw [e, h2]
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      have h3 : ∏ _i : Fin j, ‖L‖ = ‖L‖ ^ j := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [h3]
      calc ‖iteratedFDeriv ℝ j φ (L z)‖ * ‖L‖ ^ j ≤ 1 * ‖L‖ ^ j :=
            mul_le_mul_of_nonneg_right (hb j hj _) (by positivity)
        _ ≤ _ := by rw [one_mul]; exact hL j hj)
  exact this

theorem a9_sin_mem (L : StrongDual ℝ B) :
    (fun z => (1 / (3 * max 1 (‖L‖ ^ 2))) * Real.sin (L z)) ∈ CbUnitBall B 2 :=
  a9_trig_mem Real.sin Real.contDiff_sin
    (fun j _ u => by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      exact Real.abs_iteratedDeriv_sin_le_one j u) L

theorem a9_cos_mem (L : StrongDual ℝ B) :
    (fun z => (1 / (3 * max 1 (‖L‖ ^ 2))) * Real.cos (L z)) ∈ CbUnitBall B 2 :=
  a9_trig_mem Real.cos Real.contDiff_cos
    (fun j _ u => by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      exact Real.abs_iteratedDeriv_cos_le_one j u) L

end Ball

section Psi

variable {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B]

/-- the cylinder-tail test `y ↦ 1 - exp (-θ ‖y‖²)`. -/
def a9psi (θ : ℝ) (y : B) : ℝ := 1 - Real.exp (-(θ * ‖y‖ ^ 2))

theorem a9psi_nonneg (θ : ℝ) (hθ : 0 ≤ θ) (y : B) : 0 ≤ a9psi θ y := by
  unfold a9psi
  have : Real.exp (-(θ * ‖y‖ ^ 2)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖y‖])
  linarith

theorem a9psi_le_one (θ : ℝ) (hθ : 0 ≤ θ) (y : B) : a9psi θ y ≤ 1 := by
  unfold a9psi
  have := Real.exp_pos (-(θ * ‖y‖ ^ 2))
  linarith

theorem a9psi_contDiff (θ : ℝ) : ContDiff ℝ 2 (a9psi (B := B) θ) := by
  unfold a9psi
  exact contDiff_const.sub (Real.contDiff_exp.comp (contDiff_const.mul (contDiff_norm_sq ℝ)).neg)

/-- the inner product as a real-linear map `B →L StrongDual ℝ B`. -/
def a9inL : B →L[ℝ] StrongDual ℝ B :=
  (isBoundedBilinearMap_inner (𝕜 := ℝ) (E := B)).toContinuousLinearMap

theorem a9inL_apply (y v : B) : a9inL y v = inner ℝ y v := rfl

theorem a9inL_eq (y : B) : a9inL y = innerSL ℝ y := by
  ext v; rw [a9inL_apply]; rfl

theorem a9inL_norm (y : B) : ‖a9inL y‖ = ‖y‖ := by rw [a9inL_eq, innerSL_apply_norm]

theorem a9inL_norm_le : ‖(a9inL : B →L[ℝ] StrongDual ℝ B)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by rw [a9inL_norm, one_mul]

/-- the first derivative of `ψ_θ`. -/
def a9psiG (θ : ℝ) (y : B) : StrongDual ℝ B :=
  (2 * θ * Real.exp (-(θ * ‖y‖ ^ 2))) • a9inL y

theorem a9psi_hasFDerivAt (θ : ℝ) (y : B) : HasFDerivAt (a9psi (B := B) θ) (a9psiG θ y) y := by
  have h1 := (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have h2 : HasFDerivAt (a9psi (B := B) θ) _ y := ((h1.const_mul θ).neg.exp).const_sub 1
  refine h2.congr_fderiv ?_
  ext v
  simp [a9psiG, a9inL_eq]
  ring

theorem a9psi_fderiv (θ : ℝ) : fderiv ℝ (a9psi (B := B) θ) = a9psiG θ := by
  funext y; exact (a9psi_hasFDerivAt θ y).fderiv

theorem a9psiG_hasFDerivAt (θ : ℝ) (y : B) :
    HasFDerivAt (a9psiG (B := B) θ)
      ((2 * θ * Real.exp (-(θ * ‖y‖ ^ 2))) • (a9inL : B →L[ℝ] StrongDual ℝ B) +
        ((-(4 * θ ^ 2 * Real.exp (-(θ * ‖y‖ ^ 2)))) • a9inL y).smulRight (a9inL y)) y := by
  have h1 := (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have hc := (((h1.const_mul θ).neg.exp).const_mul (2 * θ))
  have hf := (a9inL : B →L[ℝ] StrongDual ℝ B).hasFDerivAt (x := y)
  have h3 : HasFDerivAt (a9psiG (B := B) θ) _ y := hc.smul hf
  refine h3.congr_fderiv ?_
  ext v w
  simp [a9inL_eq]
  left
  ring

theorem a9psi_norm_fderiv_le (θ : ℝ) (hθ : 0 < θ) (y : B) : ‖a9psiG θ y‖ ≤ Real.sqrt θ := by
  unfold a9psiG
  rw [norm_smul, a9inL_norm, Real.norm_eq_abs, abs_of_pos (by positivity)]
  set r := ‖y‖
  have hs := Real.sqrt_pos.2 hθ
  have hsq : Real.sqrt θ ^ 2 = θ := Real.sq_sqrt hθ.le
  -- u e^{-u²} ≤ 1/2 with u = √θ r
  have hu : Real.sqrt θ * r * Real.exp (-(θ * r ^ 2)) ≤ 1 / 2 := by
    have h1 : 1 + (Real.sqrt θ * r) ^ 2 ≤ Real.exp ((Real.sqrt θ * r) ^ 2) := by
      have := Real.add_one_le_exp ((Real.sqrt θ * r) ^ 2); linarith
    have h2 : (Real.sqrt θ * r) ^ 2 = θ * r ^ 2 := by rw [mul_pow, hsq]
    rw [h2] at h1
    have h3 : 2 * (Real.sqrt θ * r) ≤ Real.exp (θ * r ^ 2) := by
      nlinarith [sq_nonneg (Real.sqrt θ * r - 1), h2]
    have h4 : Real.exp (-(θ * r ^ 2)) = (Real.exp (θ * r ^ 2))⁻¹ := Real.exp_neg _
    rw [h4, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    linarith
  have : 2 * θ * Real.exp (-(θ * r ^ 2)) * r = 2 * Real.sqrt θ * (Real.sqrt θ * r * Real.exp (-(θ * r ^ 2))) := by
    rw [show θ = Real.sqrt θ * Real.sqrt θ from (Real.mul_self_sqrt hθ.le).symm]
    simp only [Real.mul_self_sqrt hθ.le]
    ring_nf
    rw [Real.sq_sqrt hθ.le]
    ring
  rw [this]
  nlinarith

theorem a9psi_norm_fderiv2_le (θ : ℝ) (hθ : 0 < θ) (y : B) :
    ‖(2 * θ * Real.exp (-(θ * ‖y‖ ^ 2))) • (a9inL : B →L[ℝ] StrongDual ℝ B) +
        ((-(4 * θ ^ 2 * Real.exp (-(θ * ‖y‖ ^ 2)))) • a9inL y).smulRight (a9inL y)‖ ≤ 6 * θ := by
  set r := ‖y‖
  set e := Real.exp (-(θ * r ^ 2)) with he
  have he0 : 0 < e := Real.exp_pos _
  have he1 : e ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg r])
  -- θ r² e ≤ 1
  have hx : θ * r ^ 2 * e ≤ 1 := by
    have h1 : θ * r ^ 2 + 1 ≤ Real.exp (θ * r ^ 2) := Real.add_one_le_exp _
    have h4 : e = (Real.exp (θ * r ^ 2))⁻¹ := Real.exp_neg _
    rw [h4, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    nlinarith [sq_nonneg r]
  have n1 : ‖(2 * θ * e) • (a9inL : B →L[ℝ] StrongDual ℝ B)‖ ≤ 2 * θ := by
    refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc 2 * θ * e * ‖(a9inL : B →L[ℝ] StrongDual ℝ B)‖ ≤ 2 * θ * e * 1 := by
          gcongr; exact a9inL_norm_le
      _ ≤ 2 * θ := by nlinarith
  have n2 : ‖((-(4 * θ ^ 2 * e)) • a9inL y).smulRight (a9inL y)‖ ≤ 4 * θ := by
    refine (ContinuousLinearMap.norm_smulRight_apply _ _).le.trans ?_
    have h5 : ‖(-(4 * θ ^ 2 * e)) • a9inL y‖ = 4 * θ ^ 2 * e * ‖y‖ := by
      rw [norm_smul, a9inL_norm, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
    rw [h5, a9inL_norm]
    nlinarith [mul_pos hθ he0]
  have := norm_add_le ((2 * θ * e) • (a9inL : B →L[ℝ] StrongDual ℝ B))
    (((-(4 * θ ^ 2 * e)) • a9inL y).smulRight (a9inL y))
  linarith

theorem a9psi_bounds (θ : ℝ) (hθ : 0 < θ) :
    ∀ j ≤ 2, ∀ y : B, ‖iteratedFDeriv ℝ j (a9psi θ) y‖ ≤ 1 + Real.sqrt θ + 6 * θ := by
  have hs := Real.sqrt_nonneg θ
  intro j hj y
  interval_cases j
  · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_nonneg (a9psi_nonneg θ hθ.le y)]
    have := a9psi_le_one θ hθ.le y
    linarith
  · rw [norm_iteratedFDeriv_one, a9psi_fderiv]
    have := a9psi_norm_fderiv_le θ hθ y
    linarith
  · have h2 : ‖iteratedFDeriv ℝ 2 (a9psi θ) y‖ = ‖fderiv ℝ (fderiv ℝ (a9psi θ)) y‖ := by
      rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
    rw [h2, a9psi_fderiv, (a9psiG_hasFDerivAt θ y).fderiv]
    have := a9psi_norm_fderiv2_le θ hθ y
    linarith

theorem a9psi_mem_ball (θ : ℝ) (hθ : 0 < θ) :
    (fun z : B => (1 / (3 * (1 + Real.sqrt θ + 6 * θ))) * a9psi θ z) ∈ CbUnitBall B 2 :=
  a9_mem_ball_of_bounds (a9psi_contDiff θ)
    (by have := Real.sqrt_nonneg θ; positivity) (a9psi_bounds θ hθ)

end Psi

end HRS.Main.A9
