import Mathlib

/-!
# Lindeberg replacement with third-order Taylor remainder (helper for Yurinskii's coupling)

Package METR-04 (Lemma A.37).  For independent centred random vectors `ξ_i` in `ℝⁿ` and
independent centred Gaussians `ζ_i` with the same covariances, and a test function `f ∈ C²`
whose Hessian is Lipschitz in the quadratic-form sense
`|D²f(x)[v,v] - D²f(y)[v,v]| ≤ K ‖x-y‖ ‖v‖²`, we show
`|E f(∑ξ_i) - E f(∑ζ_i)| ≤ K ∑ (E‖ξ_i‖³ + E‖ζ_i‖³)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Matrix

namespace HRS.Yurinskii

section Taylor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Second-order Taylor bound when only the quadratic form of the Hessian is Lipschitz. -/
lemma taylor_quad {f : E → ℝ} (hf : ContDiff ℝ 2 f) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x y v : E, |iteratedFDeriv ℝ 2 f x ![v, v] - iteratedFDeriv ℝ 2 f y ![v, v]| ≤
      L * ‖x - y‖ * ‖v‖ ^ 2)
    (x v : E) :
    |f (x + v) - f x - fderiv ℝ f x v - (1 / 2) * iteratedFDeriv ℝ 2 f x ![v, v]| ≤
      L * ‖v‖ ^ 3 := by
  have hd1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  set B : ℝ := iteratedFDeriv ℝ 2 f x ![v, v] with hB
  have hBx : B = fderiv ℝ (fderiv ℝ f) x v v := by
    simp [hB, iteratedFDeriv_two_apply]
  have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ => x + s • v) v s := by
    intro s; simpa using ((hasDerivAt_id s).smul_const v).const_add x
  have hφ : ∀ s : ℝ, HasDerivAt (fun s : ℝ => f (x + s • v)) (fderiv ℝ f (x + s • v) v) s :=
    fun s => (hd1 (x + s • v)).hasFDerivAt.comp_hasDerivAt s (hline s)
  have hφ' : ∀ s : ℝ, HasDerivAt (fun s : ℝ => fderiv ℝ f (x + s • v) v)
      (fderiv ℝ (fderiv ℝ f) (x + s • v) v v) s := by
    intro s
    have h1 := (hd2 (x + s • v)).hasFDerivAt.comp_hasDerivAt s (hline s)
    have h2 := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt s h1
    exact h2
  set k : ℝ → ℝ := fun s => fderiv ℝ f (x + s • v) v - s * B with hk
  have hkd : ∀ s, HasDerivAt k (fderiv ℝ (fderiv ℝ f) (x + s • v) v v - B) s := by
    intro s
    have := (hφ' s).sub ((hasDerivAt_id s).mul_const B)
    simp only [one_mul, id] at this
    exact this
  set g : ℝ → ℝ := fun s => f (x + s • v) - s * fderiv ℝ f x v - (1 / 2) * s ^ 2 * B with hg
  have hgd : ∀ s, HasDerivAt g (k s - fderiv ℝ f x v) s := by
    intro s
    have h1 := (hφ s).sub ((hasDerivAt_id s).mul_const (fderiv ℝ f x v))
    have h2 := (((hasDerivAt_id s).pow 2).const_mul (1 / 2 : ℝ)).mul_const B
    have := h1.sub h2
    convert this using 1
    · funext y; simp [hg]
    · simp [hk]; ring
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope g (fun s => k s - fderiv ℝ f x v) zero_lt_one
    (fun s _ => (hgd s).continuousAt.continuousWithinAt) (fun s _ => hgd s)
  obtain ⟨η, hη, hηe⟩ := exists_hasDerivAt_eq_slope k
    (fun s => fderiv ℝ (fderiv ℝ f) (x + s • v) v v - B) hξ.1
    (fun s _ => (hkd s).continuousAt.continuousWithinAt) (fun s _ => hkd s)
  have e1 : g 1 - g 0 = f (x + v) - f x - fderiv ℝ f x v - (1 / 2) * B := by
    simp [hg]; ring
  have e2 : k ξ - k 0 = ξ * (fderiv ℝ (fderiv ℝ f) (x + η • v) v v - B) := by
    rw [sub_zero] at hηe
    have : ξ ≠ 0 := hξ.1.ne'
    field_simp at hηe
    simp only [hk] at hηe ⊢
    simp at hηe ⊢
    linarith
  have e3 : |fderiv ℝ (fderiv ℝ f) (x + η • v) v v - B| ≤ L * ‖v‖ ^ 3 := by
    have : fderiv ℝ (fderiv ℝ f) (x + η • v) v v - B =
        iteratedFDeriv ℝ 2 f (x + η • v) ![v, v] - iteratedFDeriv ℝ 2 f x ![v, v] := by
      simp [iteratedFDeriv_two_apply, hBx]
    rw [this]
    refine (hL _ _ _).trans ?_
    have h6 : ‖(x + η • v) - x‖ ≤ ‖v‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hη.1]
      nlinarith [norm_nonneg v, hη.2, hξ.2]
    calc L * ‖x + η • v - x‖ * ‖v‖ ^ 2 ≤ L * ‖v‖ * ‖v‖ ^ 2 := by gcongr
      _ = L * ‖v‖ ^ 3 := by ring
  have hgabs : g 1 - g 0 = k ξ - fderiv ℝ f x v := by
    have := hξe
    simp only [sub_zero, div_one] at this
    linarith
  have e4 : g 1 - g 0 = (k ξ - k 0) := by
    rw [hgabs]; simp [hk]
  rw [← e1, e4, e2, abs_mul, abs_of_pos hξ.1]
  calc ξ * |fderiv ℝ (fderiv ℝ f) (x + η • v) v v - B| ≤ 1 * (L * ‖v‖ ^ 3) := by
        gcongr
        · exact hξ.2.le
    _ = _ := one_mul _

end Taylor

section Swap

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

lemma expand1 (L : 𝔼 →L[ℝ] ℝ) (y : 𝔼) : L y = ∑ c, y c * L (EuclideanSpace.single c 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr y]
  simp [map_sum]

lemma expand2 (B : 𝔼 →L[ℝ] 𝔼 →L[ℝ] ℝ) (y : 𝔼) :
    B y y = ∑ c, ∑ d, y c * y d * B (EuclideanSpace.single c 1) (EuclideanSpace.single d 1) := by
  have h0 : B y = ∑ c, y c • B (EuclideanSpace.single c 1) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr y]
    simp [map_sum]
  have h1 : B y y = ∑ c, y c * B (EuclideanSpace.single c 1) y := by
    rw [h0]; simp
  rw [h1]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [expand1 (B (EuclideanSpace.single c 1)) y, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

/-- The class of test functions for the Lindeberg replacement. -/
structure TestFn (K : ℝ) (f : 𝔼 → ℝ) : Prop where
  contDiff : ContDiff ℝ 2 f
  K_nonneg : 0 ≤ K
  bdd0 : ∃ M, ∀ x, |f x| ≤ M
  bdd1 : ∃ M, ∀ x, ‖fderiv ℝ f x‖ ≤ M
  bdd2 : ∃ M, ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M
  hess : ∀ x y v : 𝔼, |fderiv ℝ (fderiv ℝ f) x v v - fderiv ℝ (fderiv ℝ f) y v v| ≤
    K * ‖x - y‖ * ‖v‖ ^ 2

lemma TestFn.measurable {K : ℝ} {f : 𝔼 → ℝ} (hf : TestFn K f) : Measurable f :=
  hf.contDiff.continuous.measurable

lemma TestFn.continuous_fderiv {K : ℝ} {f : 𝔼 → ℝ} (hf : TestFn K f) :
    Continuous (fderiv ℝ f) := hf.contDiff.continuous_fderiv (by norm_num)

lemma TestFn.continuous_fderiv2 {K : ℝ} {f : 𝔼 → ℝ} (hf : TestFn K f) :
    Continuous (fderiv ℝ (fderiv ℝ f)) :=
  (hf.contDiff.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero

lemma taylor_testFn {K : ℝ} {f : 𝔼 → ℝ} (hf : TestFn K f) (x v : 𝔼) :
    |f (x + v) - f x - fderiv ℝ f x v - (1 / 2) * fderiv ℝ (fderiv ℝ f) x v v| ≤ K * ‖v‖ ^ 3 := by
  have := taylor_quad hf.contDiff hf.K_nonneg (fun x y v => by
    simpa [iteratedFDeriv_two_apply] using hf.hess x y v) x v
  simpa [iteratedFDeriv_two_apply] using this

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma integrable_norm_of_pow3 {Y : Ω → 𝔼} (hY : Measurable Y)
    (h3 : Integrable (fun ω => ‖Y ω‖ ^ 3) P) :
    Integrable (fun ω => ‖Y ω‖) P ∧ Integrable (fun ω => ‖Y ω‖ ^ 2) P := by
  have hb : Integrable (fun ω => 1 + ‖Y ω‖ ^ 3) P := (integrable_const 1).add h3
  constructor
  · refine hb.mono' hY.norm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rcases le_total ‖Y ω‖ 1 with h | h
    · nlinarith [pow_nonneg (norm_nonneg (Y ω)) 3]
    · nlinarith [norm_nonneg (Y ω), mul_nonneg (norm_nonneg (Y ω)) (sq_nonneg (‖Y ω‖ - 1))]
  · refine hb.mono' (hY.norm.pow_const 2).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rcases le_total ‖Y ω‖ 1 with h | h
    · nlinarith [pow_nonneg (norm_nonneg (Y ω)) 3, norm_nonneg (Y ω)]
    · nlinarith [norm_nonneg (Y ω)]

lemma norm_coord_le (y : 𝔼) (c : Fin n) : |y c| ≤ ‖y‖ := by
  have := PiLp.norm_apply_le y c
  rwa [Real.norm_eq_abs] at this

lemma norm_single_one (c : Fin n) : ‖(EuclideanSpace.single c (1 : ℝ) : 𝔼)‖ = 1 := by
  simp

/-- Core estimate of one Lindeberg step. -/
lemma swap_step_bound {X Y : Ω → 𝔼} {K : ℝ} {f : 𝔼 → ℝ} (hf : TestFn K f)
    (hX : Measurable X) (hY : Measurable Y)
    (hind : IndepFun X Y P) (hY0 : ∀ c, ∫ ω, Y ω c ∂P = 0)
    (hY3 : Integrable (fun ω => ‖Y ω‖ ^ 3) P) :
    |∫ ω, f (X ω + Y ω) ∂P - ∫ ω, f (X ω) ∂P -
      (1 / 2) * ∑ c, ∑ d, (∫ ω, fderiv ℝ (fderiv ℝ f) (X ω) (EuclideanSpace.single c 1)
        (EuclideanSpace.single d 1) ∂P) * ∫ ω, Y ω c * Y ω d ∂P| ≤
      K * ∫ ω, ‖Y ω‖ ^ 3 ∂P := by
  obtain ⟨M0, hM0⟩ := hf.bdd0
  obtain ⟨M1, hM1⟩ := hf.bdd1
  obtain ⟨M2, hM2⟩ := hf.bdd2
  obtain ⟨hY1, hY2⟩ := integrable_norm_of_pow3 hY hY3
  set g : Fin n → 𝔼 → ℝ := fun c x => fderiv ℝ f x (EuclideanSpace.single c 1) with hg
  set H : Fin n → Fin n → 𝔼 → ℝ := fun c d x =>
    fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single c 1) (EuclideanSpace.single d 1) with hH
  have hgc : ∀ c, Continuous (g c) := fun c => by
    simp only [hg]
    exact (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single c 1)).continuous.comp
      hf.continuous_fderiv
  have hHc : ∀ c d, Continuous (H c d) := fun c d => by
    simp only [hH]
    exact ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single d 1)).continuous.comp
      ((ContinuousLinearMap.apply ℝ (𝔼 →L[ℝ] ℝ) (EuclideanSpace.single c 1)).continuous.comp
      hf.continuous_fderiv2))
  have hgb : ∀ c x, |g c x| ≤ M1 := fun c x => by
    have := (fderiv ℝ f x).le_opNorm (EuclideanSpace.single c 1)
    rw [norm_single_one, mul_one, Real.norm_eq_abs] at this
    exact this.trans (hM1 x)
  have hHb : ∀ c d x, |H c d x| ≤ M2 := fun c d x => by
    have h1 := (fderiv ℝ (fderiv ℝ f) x).le_opNorm (EuclideanSpace.single c 1)
    have h2 := (fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single c 1)).le_opNorm
      (EuclideanSpace.single d 1)
    rw [norm_single_one, mul_one] at h1 h2
    rw [Real.norm_eq_abs] at h2
    exact (h2.trans (h1.trans (hM2 x)))
  have hYc : ∀ c, Measurable fun ω => Y ω c := fun c => by fun_prop
  have hYcI : ∀ c, Integrable (fun ω => Y ω c) P := fun c =>
    hY1.mono' (hYc c).aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact norm_coord_le _ _)
  have hYcdI : ∀ c d, Integrable (fun ω => Y ω c * Y ω d) P := fun c d =>
    hY2.mono' ((hYc c).mul (hYc d)).aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_mul]
      calc |Y ω c| * |Y ω d| ≤ ‖Y ω‖ * ‖Y ω‖ :=
            mul_le_mul (norm_coord_le _ _) (norm_coord_le _ _) (abs_nonneg _) (norm_nonneg _)
        _ = ‖Y ω‖ ^ 2 := by ring)
  have hfI : ∀ Z : Ω → 𝔼, Measurable Z → Integrable (fun ω => f (Z ω)) P := fun Z hZ =>
    (integrable_const M0).mono' (hf.measurable.comp hZ).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hM0 _)
  have hXY : Measurable fun ω => X ω + Y ω := hX.add hY
  have hlinI : ∀ c, Integrable (fun ω => Y ω c * g c (X ω)) P := fun c =>
    (hY1.mul_const M1).mono' ((hYc c).mul ((hgc c).measurable.comp hX)).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (norm_coord_le _ _) (hgb _ _) (abs_nonneg _) (norm_nonneg _))
  have hquadI : ∀ c d, Integrable (fun ω => Y ω c * Y ω d * H c d (X ω)) P := fun c d =>
    (hY2.mul_const M2).mono' (((hYc c).mul (hYc d)).mul ((hHc c d).measurable.comp hX)).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        calc |Y ω c| * |Y ω d| * |H c d (X ω)| ≤ ‖Y ω‖ * ‖Y ω‖ * M2 :=
              mul_le_mul (mul_le_mul (norm_coord_le _ _) (norm_coord_le _ _) (abs_nonneg _)
                (norm_nonneg _)) (hHb _ _ _) (abs_nonneg _) (by positivity)
          _ = ‖Y ω‖ ^ 2 * M2 := by ring)
  -- independence
  have hlin : ∀ c, ∫ ω, Y ω c * g c (X ω) ∂P = 0 := by
    intro c
    have hi : IndepFun (fun ω => g c (X ω)) (fun ω => Y ω c) P :=
      hind.comp (φ := g c) (ψ := fun y : 𝔼 => y c) (hgc c).measurable (by fun_prop)
    have := hi.integral_fun_mul_eq_mul_integral
      ((hgc c).measurable.comp hX).aestronglyMeasurable (hYc c).aestronglyMeasurable
    calc ∫ ω, Y ω c * g c (X ω) ∂P = ∫ ω, g c (X ω) * Y ω c ∂P := by
          congr 1; ext ω; ring
      _ = 0 := by rw [this, hY0 c, mul_zero]
  have hquad : ∀ c d, ∫ ω, Y ω c * Y ω d * H c d (X ω) ∂P =
      (∫ ω, H c d (X ω) ∂P) * ∫ ω, Y ω c * Y ω d ∂P := by
    intro c d
    have hi : IndepFun (fun ω => H c d (X ω)) (fun ω => Y ω c * Y ω d) P :=
      hind.comp (φ := H c d) (ψ := fun y : 𝔼 => y c * y d) (hHc c d).measurable (by fun_prop)
    have := hi.integral_fun_mul_eq_mul_integral
      ((hHc c d).measurable.comp hX).aestronglyMeasurable ((hYc c).mul (hYc d)).aestronglyMeasurable
    calc ∫ ω, Y ω c * Y ω d * H c d (X ω) ∂P = ∫ ω, H c d (X ω) * (Y ω c * Y ω d) ∂P := by
          congr 1; ext ω; ring
      _ = _ := this
  -- remainder
  set R : Ω → ℝ := fun ω => f (X ω + Y ω) - f (X ω) - ∑ c, Y ω c * g c (X ω) -
    (1 / 2) * ∑ c, ∑ d, Y ω c * Y ω d * H c d (X ω) with hR
  have hRb : ∀ ω, |R ω| ≤ K * ‖Y ω‖ ^ 3 := by
    intro ω
    have h := taylor_testFn hf (X ω) (Y ω)
    have e1 : fderiv ℝ f (X ω) (Y ω) = ∑ c, Y ω c * g c (X ω) := expand1 _ _
    have e2 : fderiv ℝ (fderiv ℝ f) (X ω) (Y ω) (Y ω) =
        ∑ c, ∑ d, Y ω c * Y ω d * H c d (X ω) := expand2 _ _
    rw [e1, e2] at h
    simpa only [hR, sub_sub] using h
  have hlinSum : Integrable (fun ω => ∑ c, Y ω c * g c (X ω)) P :=
    integrable_finsetSum _ fun c _ => hlinI c
  have hquadSum : Integrable (fun ω => ∑ c, ∑ d, Y ω c * Y ω d * H c d (X ω)) P :=
    integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun d _ => hquadI c d
  have hI12 : Integrable (fun ω => f (X ω + Y ω) - f (X ω)) P := (hfI _ hXY).sub (hfI X hX)
  have hI123 : Integrable (fun ω => f (X ω + Y ω) - f (X ω) - ∑ c, Y ω c * g c (X ω)) P :=
    hI12.sub hlinSum
  have hI4 : Integrable (fun ω => (1 / 2 : ℝ) * ∑ c, ∑ d, Y ω c * Y ω d * H c d (X ω)) P :=
    hquadSum.const_mul _
  have hRI : Integrable R P := hI123.sub hI4
  have hRint : ∫ ω, R ω ∂P = ∫ ω, f (X ω + Y ω) ∂P - ∫ ω, f (X ω) ∂P -
      (1 / 2) * ∑ c, ∑ d, (∫ ω, H c d (X ω) ∂P) * ∫ ω, Y ω c * Y ω d ∂P := by
    simp only [hR]
    rw [integral_sub hI123 hI4, integral_sub hI12 hlinSum, integral_sub (hfI _ hXY) (hfI X hX),
      integral_const_mul, integral_finsetSum _ fun c _ => hlinI c,
      integral_finsetSum _ fun c _ => integrable_finsetSum _ fun d _ => hquadI c d]
    simp_rw [integral_finsetSum _ fun d _ => hquadI _ d, hlin, hquad]
    simp
  have : |∫ ω, R ω ∂P| ≤ K * ∫ ω, ‖Y ω‖ ^ 3 ∂P := by
    calc |∫ ω, R ω ∂P| ≤ ∫ ω, |R ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω, K * ‖Y ω‖ ^ 3 ∂P := integral_mono hRI.abs (hY3.const_mul K) hRb
      _ = _ := integral_const_mul _ _
  rw [hRint] at this
  exact this

/-- One Lindeberg swap. -/
lemma swap_diff {X Y Z : Ω → 𝔼} {K : ℝ} {f : 𝔼 → ℝ} (hf : TestFn K f)
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hindY : IndepFun X Y P) (hindZ : IndepFun X Z P)
    (hY0 : ∀ c, ∫ ω, Y ω c ∂P = 0) (hZ0 : ∀ c, ∫ ω, Z ω c ∂P = 0)
    (hYZ : ∀ c d, ∫ ω, Y ω c * Y ω d ∂P = ∫ ω, Z ω c * Z ω d ∂P)
    (hY3 : Integrable (fun ω => ‖Y ω‖ ^ 3) P) (hZ3 : Integrable (fun ω => ‖Z ω‖ ^ 3) P) :
    |∫ ω, f (X ω + Y ω) ∂P - ∫ ω, f (X ω + Z ω) ∂P| ≤
      K * (∫ ω, ‖Y ω‖ ^ 3 ∂P + ∫ ω, ‖Z ω‖ ^ 3 ∂P) := by
  have h1 := swap_step_bound hf hX hY hindY hY0 hY3
  have h2 := swap_step_bound hf hX hZ hindZ hZ0 hZ3
  simp_rw [hYZ] at h1
  set a := ∫ ω, f (X ω + Y ω) ∂P
  set b := ∫ ω, f (X ω + Z ω) ∂P
  set q := (1 / 2 : ℝ) * ∑ c, ∑ d, (∫ ω, fderiv ℝ (fderiv ℝ f) (X ω) (EuclideanSpace.single c 1)
        (EuclideanSpace.single d 1) ∂P) * ∫ ω, Z ω c * Z ω d ∂P
  have : |a - b| ≤ |a - ∫ ω, f (X ω) ∂P - q| + |b - ∫ ω, f (X ω) ∂P - q| := by
    have := abs_sub (a - ∫ ω, f (X ω) ∂P - q) (b - ∫ ω, f (X ω) ∂P - q)
    calc |a - b| = |(a - ∫ ω, f (X ω) ∂P - q) - (b - ∫ ω, f (X ω) ∂P - q)| := by ring_nf
      _ ≤ _ := this
  calc |a - b| ≤ _ := this
    _ ≤ K * ∫ ω, ‖Y ω‖ ^ 3 ∂P + K * ∫ ω, ‖Z ω‖ ^ 3 ∂P := add_le_add h1 h2
    _ = _ := by ring

end Swap

section Telescope

variable {n : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin n)
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Lindeberg telescoping over the hybrid sums. -/
theorem lindeberg_telescope {N : ℕ} {K : ℝ} {f : 𝔼 → ℝ} (hf : TestFn K f)
    (V : Fin N ⊕ Fin N → Ω → 𝔼) (hVm : ∀ t, Measurable (V t)) (hV : iIndepFun V P)
    (h0 : ∀ t c, ∫ ω, V t ω c ∂P = 0)
    (h2 : ∀ i c d, ∫ ω, V (Sum.inl i) ω c * V (Sum.inl i) ω d ∂P =
      ∫ ω, V (Sum.inr i) ω c * V (Sum.inr i) ω d ∂P)
    (h3 : ∀ t, Integrable (fun ω => ‖V t ω‖ ^ 3) P) :
    |∫ ω, f (∑ i, V (Sum.inl i) ω) ∂P - ∫ ω, f (∑ i, V (Sum.inr i) ω) ∂P| ≤
      K * ∑ i, (∫ ω, ‖V (Sum.inl i) ω‖ ^ 3 ∂P + ∫ ω, ‖V (Sum.inr i) ω‖ ^ 3 ∂P) := by
  classical
  -- hybrid sums
  let W : ℕ → Ω → 𝔼 := fun k ω => ∑ i : Fin N,
    (if i.val < k then V (Sum.inl i) ω else V (Sum.inr i) ω)
  let a : ℕ → ℝ := fun k => ∫ ω, f (W k ω) ∂P
  have hW0 : ∀ ω, W 0 ω = ∑ i, V (Sum.inr i) ω := fun ω => by simp [W]
  have hWN : ∀ ω, W N ω = ∑ i, V (Sum.inl i) ω := fun ω => by
    simp only [W]
    exact Finset.sum_congr rfl fun i _ => by simp [i.2]
  -- one step
  have hstep : ∀ k : ℕ, ∀ hk : k < N, |a (k + 1) - a k| ≤
      K * (∫ ω, ‖V (Sum.inl ⟨k, hk⟩) ω‖ ^ 3 ∂P + ∫ ω, ‖V (Sum.inr ⟨k, hk⟩) ω‖ ^ 3 ∂P) := by
    intro k hk
    set j : Fin N := ⟨k, hk⟩ with hj
    let s : Fin N → Fin N ⊕ Fin N := fun i => if i.val < k then Sum.inl i else Sum.inr i
    have hs_inj : Function.Injective s := by
      intro i i' h
      simp only [s] at h
      split_ifs at h with h1 h2 h2 <;> simp_all
    set X : Ω → 𝔼 := fun ω => ∑ i ∈ Finset.univ.erase j, V (s i) ω with hX
    have hXm : Measurable X := by
      simp only [hX]
      exact Finset.measurable_sum _ fun i _ => hVm _
    have hXeq : X = ∑ t ∈ (Finset.univ.erase j).image s, V t := by
      rw [Finset.sum_image (fun i _ i' _ h => hs_inj h)]
      ext ω; simp [hX]
    have hnotl : Sum.inl j ∉ (Finset.univ.erase j).image s := by
      simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true, not_exists, not_and]
      intro i hij h
      apply hij
      simp only [s] at h
      split_ifs at h with h1 <;> simp_all
    have hnotr : Sum.inr j ∉ (Finset.univ.erase j).image s := by
      simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true, not_exists, not_and]
      intro i hij h
      apply hij
      simp only [s] at h
      split_ifs at h with h1 <;> simp_all
    have hindl : IndepFun X (V (Sum.inl j)) P := by
      rw [hXeq]; exact hV.indepFun_finsetSum_of_notMem hVm hnotl
    have hindr : IndepFun X (V (Sum.inr j)) P := by
      rw [hXeq]; exact hV.indepFun_finsetSum_of_notMem hVm hnotr
    have hWk1 : ∀ ω, W (k + 1) ω = X ω + V (Sum.inl j) ω := by
      intro ω
      simp only [W, hX]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), add_comm]
      refine congrArg₂ (· + ·) ?_ ?_
      · refine Finset.sum_congr rfl fun i hi => ?_
        have hij : i ≠ j := Finset.ne_of_mem_erase hi
        have : i.val ≠ k := fun h => hij (Fin.ext h)
        simp only [s]
        by_cases hlt : i.val < k
        · simp [hlt, Nat.lt_succ_of_lt hlt]
        · have : ¬ i.val < k + 1 := by omega
          simp [hlt, this]
      · simp [hj]
    have hWk : ∀ ω, W k ω = X ω + V (Sum.inr j) ω := by
      intro ω
      simp only [W, hX]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), add_comm]
      refine congrArg₂ (· + ·) ?_ ?_
      · refine Finset.sum_congr rfl fun i hi => ?_
        simp only [s]
        split_ifs <;> rfl
      · simp [hj]
    have := swap_diff hf hXm (hVm _) (hVm _) hindl hindr (h0 _) (h0 _) (h2 j) (h3 _) (h3 _)
    simp only [a, hWk1, hWk]
    exact this
  have hsum : a N - a 0 = ∑ k ∈ Finset.range N, (a (k + 1) - a k) := (Finset.sum_range_sub a N).symm
  have haN : a N = ∫ ω, f (∑ i, V (Sum.inl i) ω) ∂P := by simp only [a, hWN]
  have ha0 : a 0 = ∫ ω, f (∑ i, V (Sum.inr i) ω) ∂P := by simp only [a, hW0]
  rw [← haN, ← ha0, hsum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  let B : ℕ → ℝ := fun k => if hk : k < N then
    K * (∫ ω, ‖V (Sum.inl ⟨k, hk⟩) ω‖ ^ 3 ∂P + ∫ ω, ‖V (Sum.inr ⟨k, hk⟩) ω‖ ^ 3 ∂P) else 0
  calc ∑ k ∈ Finset.range N, |a (k + 1) - a k| ≤ ∑ k ∈ Finset.range N, B k :=
        Finset.sum_le_sum fun k hk => by
          have hk' : k < N := Finset.mem_range.1 hk
          simp only [B, dif_pos hk']
          exact hstep k hk'
    _ = ∑ i : Fin N, B i := (Fin.sum_univ_eq_sum_range B N).symm
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [B, dif_pos i.2]
end Telescope

section PiForm

variable {n : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin n)

lemma integral_comp_eval {ι : Type*} [Fintype ι] (μ : ι → Measure 𝔼) [∀ i, IsProbabilityMeasure (μ i)]
    (t : ι) (g : 𝔼 → ℝ) (hg : Measurable g) :
    ∫ ω, g (ω t) ∂(Measure.pi μ) = ∫ x, g x ∂(μ t) := by
  have hmp := measurePreserving_eval μ t
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hg.aestronglyMeasurable]

lemma integrable_comp_eval {ι : Type*} [Fintype ι] (μ : ι → Measure 𝔼) [∀ i, IsProbabilityMeasure (μ i)]
    (t : ι) (g : 𝔼 → ℝ) (hg : Measurable g) (h : Integrable g (μ t)) :
    Integrable (fun ω => g (ω t)) (Measure.pi μ) := by
  have hmp := measurePreserving_eval μ t
  rw [← hmp.map_eq] at h
  exact (integrable_map_measure hg.aestronglyMeasurable hmp.measurable.aemeasurable).1 h

/-- Lindeberg replacement on product measures. -/
theorem lindeberg_pi {N : ℕ} {K : ℝ} {f : 𝔼 → ℝ} (hf : TestFn K f)
    (ρ γ : Fin N → Measure 𝔼) [∀ i, IsProbabilityMeasure (ρ i)] [∀ i, IsProbabilityMeasure (γ i)]
    (h0ρ : ∀ i c, ∫ x, x c ∂(ρ i) = 0) (h0γ : ∀ i c, ∫ x, x c ∂(γ i) = 0)
    (h2 : ∀ i c d, ∫ x, x c * x d ∂(ρ i) = ∫ x, x c * x d ∂(γ i))
    (h3ρ : ∀ i, Integrable (fun x => ‖x‖ ^ 3) (ρ i))
    (h3γ : ∀ i, Integrable (fun x => ‖x‖ ^ 3) (γ i)) :
    |∫ x, f x ∂((Measure.pi ρ).map (fun p => ∑ i, p i)) -
        ∫ x, f x ∂((Measure.pi γ).map (fun p => ∑ i, p i))| ≤
      K * ∑ i, (∫ x, ‖x‖ ^ 3 ∂(ρ i) + ∫ x, ‖x‖ ^ 3 ∂(γ i)) := by
  classical
  set μ : Fin N ⊕ Fin N → Measure 𝔼 := Sum.elim ρ γ with hμ
  haveI : ∀ t, IsProbabilityMeasure (μ t) := fun t => by
    rcases t with i | i <;> simp [hμ] <;> infer_instance
  set Q : Measure (Fin N ⊕ Fin N → 𝔼) := Measure.pi μ with hQ
  let V : Fin N ⊕ Fin N → (Fin N ⊕ Fin N → 𝔼) → 𝔼 := fun t ω => ω t
  have hVm : ∀ t, Measurable (V t) := fun t => measurable_pi_apply t
  have hV : iIndepFun V Q := iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hcoord : ∀ c : Fin n, Measurable fun x : 𝔼 => x c := fun c => by fun_prop
  -- moments
  have e0 : ∀ t c, ∫ ω, V t ω c ∂Q = ∫ x, x c ∂(μ t) := fun t c =>
    integral_comp_eval μ t (fun x => x c) (hcoord c)
  have e2 : ∀ t c d, ∫ ω, V t ω c * V t ω d ∂Q = ∫ x, x c * x d ∂(μ t) := fun t c d =>
    integral_comp_eval μ t (fun x => x c * x d) ((hcoord c).mul (hcoord d))
  have e3 : ∀ t, ∫ ω, ‖V t ω‖ ^ 3 ∂Q = ∫ x, ‖x‖ ^ 3 ∂(μ t) := fun t =>
    integral_comp_eval μ t (fun x => ‖x‖ ^ 3) (measurable_norm.pow_const 3)
  have i3 : ∀ t, Integrable (fun ω => ‖V t ω‖ ^ 3) Q := by
    intro t
    refine integrable_comp_eval μ t (fun x => ‖x‖ ^ 3) (measurable_norm.pow_const 3) ?_
    rcases t with i | i
    · exact h3ρ i
    · exact h3γ i
  have key := lindeberg_telescope hf V hVm hV
    (fun t c => by rw [e0]; rcases t with i | i; exacts [h0ρ i c, h0γ i c])
    (fun i c d => by rw [e2, e2]; exact h2 i c d) i3
  -- identify the laws
  have hlaw : ∀ (g : Fin N → Measure 𝔼) [∀ i, IsProbabilityMeasure (g i)] (inj : Fin N → Fin N ⊕ Fin N),
      Function.Injective inj → (∀ i, μ (inj i) = g i) →
      Q.map (fun ω i => ω (inj i)) = Measure.pi g := by
    intro g _ inj hinj hg
    have h1 := hV.precomp hinj
    rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => (hVm _).aemeasurable)] at h1
    have hmap_i : ∀ i, Q.map (V (inj i)) = g i := by
      intro i
      have := (measurePreserving_eval μ (inj i)).map_eq
      rw [← hg i, ← this]
    simp_rw [hmap_i] at h1
    exact h1
  have hsum : ∀ (g : Fin N → Measure 𝔼) [∀ i, IsProbabilityMeasure (g i)] (inj : Fin N → Fin N ⊕ Fin N),
      Function.Injective inj → (∀ i, μ (inj i) = g i) →
      ∫ ω, f (∑ i, V (inj i) ω) ∂Q = ∫ x, f x ∂((Measure.pi g).map (fun p => ∑ i, p i)) := by
    intro g _ inj hinj hg
    have hsm : Measurable (fun p : Fin N → 𝔼 => ∑ i, p i) :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    have hmq : Measurable (fun (ω : Fin N ⊕ Fin N → 𝔼) (i : Fin N) => ω (inj i)) :=
      Measurable.of_eval fun i => measurable_pi_apply _
    rw [integral_map hsm.aemeasurable hf.measurable.aestronglyMeasurable, ← hlaw g inj hinj hg]
    exact (integral_map hmq.aemeasurable ((hf.measurable.comp hsm).aestronglyMeasurable :
        AEStronglyMeasurable (fun x : Fin N → 𝔼 => f (∑ i, x i)) _)).symm
  rw [← hsum ρ Sum.inl Sum.inl_injective (fun i => rfl),
    ← hsum γ Sum.inr Sum.inr_injective (fun i => rfl)]
  refine key.trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [e3, e3]; rfl

/-- The fourth moment of a standard real Gaussian. -/
def c4 : ℝ := ∫ x, x ^ 4 ∂(gaussianReal 0 1)

lemma c4_nonneg : 0 ≤ c4 := integral_nonneg fun x => by positivity

lemma integral_pow4_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 4 ∂(gaussianReal 0 v) = (v : ℝ) ^ 2 * c4 := by
  have h : gaussianReal 0 v = (gaussianReal 0 1).map (fun x => Real.sqrt v * x) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · rw [← NNReal.coe_inj]
      simp [Real.sq_sqrt v.coe_nonneg]
  rw [h, integral_map (by fun_prop) (by fun_prop)]
  have : ∀ x : ℝ, (Real.sqrt v * x) ^ 4 = (v : ℝ) ^ 2 * x ^ 4 := fun x => by
    rw [mul_pow]
    congr 1
    have := Real.sq_sqrt v.coe_nonneg
    calc Real.sqrt v ^ 4 = (Real.sqrt v ^ 2) ^ 2 := by ring
      _ = _ := by rw [this]
  simp_rw [this]
  rw [integral_const_mul]
  rfl

lemma integral_coord_pow4 {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosSemidef) (i : Fin n) :
    ∫ y, (y i) ^ 4 ∂(multivariateGaussian (0 : 𝔼) Q) = (Q i i) ^ 2 * c4 := by
  have hmp := measurePreserving_eval_multivariateGaussian (μ := (0 : 𝔼)) hQ (i := i)
  have hmeq : Measure.map (fun x : 𝔼 => x i) (multivariateGaussian (0 : 𝔼) Q) =
      gaussianReal 0 (Q i i).toNNReal := hmp.map_eq
  have h1 : ∫ x, x ^ 4 ∂(gaussianReal 0 (Q i i).toNNReal) =
      ∫ y, (y i) ^ 4 ∂(multivariateGaussian (0 : 𝔼) Q) := by
    rw [← hmeq, integral_map hmp.measurable.aemeasurable (by fun_prop)]
  rw [← h1, integral_pow4_gaussianReal, Real.coe_toNNReal _ hQ.diag_nonneg]

lemma integral_coord_zero {Q : Matrix (Fin n) (Fin n) ℝ} (c : Fin n) :
    ∫ y, y c ∂(multivariateGaussian (0 : 𝔼) Q) = 0 := by
  have := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj c : 𝔼 →L[ℝ] ℝ)
    (IsGaussian.integrable_id (μ := multivariateGaussian (0 : 𝔼) Q))
  simpa using this

lemma memLp_coord {Q : Matrix (Fin n) (Fin n) ℝ} (c : Fin n) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (fun y : 𝔼 => y c) p (multivariateGaussian (0 : 𝔼) Q) := by
  have hmem : MemLp id p (multivariateGaussian (0 : 𝔼) Q) :=
    IsGaussian.memLp_id _ p hp
  exact (EuclideanSpace.proj c : 𝔼 →L[ℝ] ℝ).comp_memLp' hmem

lemma integral_coord_mul {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosSemidef) (c d : Fin n) :
    ∫ y, y c * y d ∂(multivariateGaussian (0 : 𝔼) Q) = Q c d := by
  have h := covariance_eval_multivariateGaussian (μ := (0 : 𝔼)) hQ c d
  rw [covariance_eq_sub (memLp_coord c 2 (by simp)) (memLp_coord d 2 (by simp)),
    integral_coord_zero, integral_coord_zero, mul_zero, sub_zero] at h
  exact h

lemma sq_le_mul_of_quad {A B C : ℝ} (h : ∀ t : ℝ, 0 ≤ A * (t * t) + (-2 * B) * t + C) :
    B ^ 2 ≤ A * C := by
  have := discrim_le_zero h
  simp only [discrim] at this
  nlinarith

lemma integrable_coord_pow {Q : Matrix (Fin n) (Fin n) ℝ} (c : Fin n) (k : ℕ) (hk : k ≠ 0) :
    Integrable (fun y : 𝔼 => (y c) ^ k) (multivariateGaussian (0 : 𝔼) Q) := by
  have h := (memLp_coord (Q := Q) c k (by simpa using hk)).integrable_norm_pow
    (p := k) (by simpa using hk)
  have h' : Integrable (fun y : 𝔼 => ‖y c‖ ^ k) (multivariateGaussian (0 : 𝔼) Q) := by
    simpa using h
  refine h'.mono' ((by fun_prop : Measurable fun y : 𝔼 => (y c) ^ k).aestronglyMeasurable)
    (ae_of_all _ fun y => by simp [norm_pow])

/-- Cauchy–Schwarz for the cross fourth moments of a centred Gaussian. -/
lemma integral_cross_le {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosSemidef) (c d : Fin n) :
    ∫ y, (y c) ^ 2 * (y d) ^ 2 ∂(multivariateGaussian (0 : 𝔼) Q) ≤ c4 * (Q c c * Q d d) := by
  set γ := multivariateGaussian (0 : 𝔼) Q with hγ
  have i4c := integrable_coord_pow (Q := Q) c 4 (by norm_num)
  have i4d := integrable_coord_pow (Q := Q) d 4 (by norm_num)
  have i22 : Integrable (fun y : 𝔼 => (y c) ^ 2 * (y d) ^ 2) γ := by
    refine (i4c.add i4d).mono' ((by fun_prop : Measurable fun y : 𝔼 => (y c) ^ 2 * (y d) ^ 2).aestronglyMeasurable)
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg ((y c) ^ 2 - (y d) ^ 2)]
  set A := ∫ y, (y c) ^ 4 ∂γ with hA
  set C := ∫ y, (y d) ^ 4 ∂γ with hC
  set B := ∫ y, (y c) ^ 2 * (y d) ^ 2 ∂γ with hB
  have hquad : ∀ t : ℝ, 0 ≤ A * (t * t) + (-2 * B) * t + C := by
    intro t
    have h0 : 0 ≤ ∫ y, (t * (y c) ^ 2 - (y d) ^ 2) ^ 2 ∂γ := integral_nonneg fun y => sq_nonneg _
    have : ∫ y, (t * (y c) ^ 2 - (y d) ^ 2) ^ 2 ∂γ = A * (t * t) + (-2 * B) * t + C := by
      have e : ∀ y : 𝔼, (t * (y c) ^ 2 - (y d) ^ 2) ^ 2 =
          (t * t) * (y c) ^ 4 + (-2 * t) * ((y c) ^ 2 * (y d) ^ 2) + (y d) ^ 4 := fun y => by ring
      simp_rw [e]
      have j1 : Integrable (fun y : 𝔼 => (t * t) * (y c) ^ 4) γ := i4c.const_mul _
      have j2 : Integrable (fun y : 𝔼 => (-2 * t) * ((y c) ^ 2 * (y d) ^ 2)) γ := i22.const_mul _
      have j12 : Integrable (fun y : 𝔼 => (t * t) * (y c) ^ 4 +
          (-2 * t) * ((y c) ^ 2 * (y d) ^ 2)) γ := j1.add j2
      rw [integral_add j12 i4d, integral_add j1 j2, integral_const_mul, integral_const_mul]
      ring
    linarith
  have hsq := sq_le_mul_of_quad hquad
  have hAv : A = (Q c c) ^ 2 * c4 := integral_coord_pow4 hQ c
  have hCv : C = (Q d d) ^ 2 * c4 := integral_coord_pow4 hQ d
  have hB0 : 0 ≤ B := integral_nonneg fun y => by positivity
  have hc4 := c4_nonneg
  have hqc := hQ.diag_nonneg (i := c)
  have hqd := hQ.diag_nonneg (i := d)
  have hR : 0 ≤ c4 * (Q c c * Q d d) := by positivity
  by_contra hlt
  push Not at hlt
  have : (c4 * (Q c c * Q d d)) ^ 2 < B ^ 2 := by nlinarith
  have h2 : B ^ 2 ≤ (Q c c) ^ 2 * c4 * ((Q d d) ^ 2 * c4) := by rw [← hAv, ← hCv]; exact hsq
  nlinarith

lemma integral_norm_sq_gauss {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosSemidef) :
    ∫ y, ‖y‖ ^ 2 ∂(multivariateGaussian (0 : 𝔼) Q) = ∑ c, Q c c := by
  have hi : ∀ c : Fin n, Integrable (fun y : 𝔼 => (y c) ^ 2) (multivariateGaussian (0 : 𝔼) Q) :=
    fun c => integrable_coord_pow c 2 (by norm_num)
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum _ fun c _ => hi c]
  refine Finset.sum_congr rfl fun c _ => ?_
  have := integral_coord_mul hQ c c
  simpa [sq] using this

lemma integral_norm_pow4_le {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosSemidef) :
    ∫ y, ‖y‖ ^ 4 ∂(multivariateGaussian (0 : 𝔼) Q) ≤ c4 * (∑ c, Q c c) ^ 2 := by
  set γ := multivariateGaussian (0 : 𝔼) Q with hγ
  have i22 : ∀ c d : Fin n, Integrable (fun y : 𝔼 => (y c) ^ 2 * (y d) ^ 2) γ := by
    intro c d
    have i4c := integrable_coord_pow (Q := Q) c 4 (by norm_num)
    have i4d := integrable_coord_pow (Q := Q) d 4 (by norm_num)
    refine (i4c.add i4d).mono' ((by fun_prop : Measurable fun y : 𝔼 => (y c) ^ 2 * (y d) ^ 2).aestronglyMeasurable)
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg ((y c) ^ 2 - (y d) ^ 2)]
  have e : ∀ y : 𝔼, ‖y‖ ^ 4 = ∑ c, ∑ d, (y c) ^ 2 * (y d) ^ 2 := fun y => by
    have : ‖y‖ ^ 2 = ∑ c, (y c) ^ 2 := EuclideanSpace.real_norm_sq_eq y
    calc ‖y‖ ^ 4 = (‖y‖ ^ 2) ^ 2 := by ring
      _ = (∑ c, (y c) ^ 2) * (∑ d, (y d) ^ 2) := by rw [this]; ring
      _ = _ := Finset.sum_mul_sum _ _ _ _
  simp_rw [e]
  rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun d _ => i22 c d]
  calc ∑ c, ∫ y, ∑ d, (y c) ^ 2 * (y d) ^ 2 ∂γ
      = ∑ c, ∑ d, ∫ y, (y c) ^ 2 * (y d) ^ 2 ∂γ := by
        refine Finset.sum_congr rfl fun c _ => ?_
        exact integral_finsetSum _ fun d _ => i22 c d
    _ ≤ ∑ c, ∑ d, c4 * (Q c c * Q d d) :=
        Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun d _ => integral_cross_le hQ c d
    _ = c4 * (∑ c, Q c c) ^ 2 := by
        simp_rw [← Finset.mul_sum, ← Finset.sum_mul]; ring

/-- The matrix of second moments. -/
def momentMatrix (ρ : Measure 𝔼) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun c d => ∫ x, x c * x d ∂ρ

lemma integrable_coord_mul {ρ : Measure 𝔼} (h2 : Integrable (fun x : 𝔼 => ‖x‖ ^ 2) ρ)
    (c d : Fin n) : Integrable (fun x : 𝔼 => x c * x d) ρ := by
  refine h2.mono' ((by fun_prop : Measurable fun x : 𝔼 => x c * x d).aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc |x c| * |x d| ≤ ‖x‖ * ‖x‖ :=
        mul_le_mul (by simpa using PiLp.norm_apply_le x c) (by simpa using PiLp.norm_apply_le x d)
          (abs_nonneg _) (norm_nonneg _)
    _ = ‖x‖ ^ 2 := by ring

lemma momentMatrix_posSemidef (ρ : Measure 𝔼) [IsProbabilityMeasure ρ]
    (h2 : Integrable (fun x : 𝔼 => ‖x‖ ^ 2) ρ) : (momentMatrix ρ).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v => ?_⟩
  · ext c d
    simp [momentMatrix, mul_comm]
  · have hI := integrable_coord_mul h2
    have : star v ⬝ᵥ (momentMatrix ρ *ᵥ v) = ∫ x, (∑ c, v c * x c) ^ 2 ∂ρ := by
      have e : ∀ x : 𝔼, (∑ c, v c * x c) ^ 2 = ∑ c, ∑ d, (v c * v d) * (x c * x d) := fun x => by
        rw [sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
      simp_rw [e]
      rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun d _ => (hI c d).const_mul _]
      simp only [dotProduct, Matrix.mulVec, momentMatrix, Matrix.of_apply, Pi.star_apply, star_trivial,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [integral_finsetSum _ fun d _ => (hI c d).const_mul _]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [integral_const_mul]; ring
    rw [this]
    exact integral_nonneg fun x => sq_nonneg _

lemma trace_momentMatrix (ρ : Measure 𝔼) (h2 : Integrable (fun x : 𝔼 => ‖x‖ ^ 2) ρ) :
    ∑ c, momentMatrix ρ c c = ∫ x, ‖x‖ ^ 2 ∂ρ := by
  have hI := integrable_coord_mul h2
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum _ fun c _ => by simpa [sq] using hI c c]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp [momentMatrix, sq]

lemma lyapunov (ρ : Measure 𝔼) [IsProbabilityMeasure ρ]
    (h2 : Integrable (fun x : 𝔼 => ‖x‖ ^ 2) ρ) (h3 : Integrable (fun x : 𝔼 => ‖x‖ ^ 3) ρ) :
    (Real.sqrt (∫ x, ‖x‖ ^ 2 ∂ρ)) ^ 3 ≤ ∫ x, ‖x‖ ^ 3 ∂ρ := by
  set m := ∫ x, ‖x‖ ^ 2 ∂ρ with hm
  set M := ∫ x, ‖x‖ ^ 3 ∂ρ with hM
  have hm0 : 0 ≤ m := integral_nonneg fun x => by positivity
  have hM0 : 0 ≤ M := integral_nonneg fun x => by positivity
  set u := Real.sqrt m with hu
  have hu2 : u ^ 2 = m := Real.sq_sqrt hm0
  rcases (Real.sqrt_nonneg m).eq_or_lt with h0 | hpos
  · have hu0 : u = 0 := by rw [hu]; exact h0.symm
    rw [hu0]; simpa using hM0
  · have hu_pos : 0 < u := hpos
    have hpt : ∀ x : 𝔼, ‖x‖ ^ 2 ≤ (2 / 3) * (‖x‖ ^ 3 / u) + u ^ 2 / 3 := fun x => by
      have ha := norm_nonneg x
      have hrhs : (2 / 3) * (‖x‖ ^ 3 / u) + u ^ 2 / 3 = (2 * ‖x‖ ^ 3 + u ^ 3) / (3 * u) := by
        field_simp
      rw [hrhs, le_div_iff₀ (by linarith)]
      nlinarith [mul_nonneg (sq_nonneg (‖x‖ - u)) (by linarith : 0 ≤ 2 * ‖x‖ + u)]
    have hint : Integrable (fun x : 𝔼 => (2 / 3) * (‖x‖ ^ 3 / u) + u ^ 2 / 3) ρ :=
      ((h3.div_const u).const_mul _).add (integrable_const _)
    have h1 := integral_mono h2 hint hpt
    rw [integral_add ((h3.div_const u).const_mul _) (integrable_const _), integral_const_mul,
      integral_div] at h1
    simp only [integral_const, probReal_univ, one_smul, smul_eq_mul, one_mul] at h1
    rw [← hm, ← hM] at h1
    have h4 : m = u ^ 2 := hu2.symm
    have h5 : u ^ 3 ≤ M := by
      have : (2 / 3) * u ^ 2 ≤ (2 / 3) * (M / u) := by linarith
      have h6 : u ^ 2 ≤ M / u := by linarith
      rw [le_div_iff₀ hu_pos] at h6
      nlinarith
    exact h5

lemma integrable_norm_pow_gauss {Q : Matrix (Fin n) (Fin n) ℝ} (k : ℕ) (hk : k ≠ 0) :
    Integrable (fun y : 𝔼 => ‖y‖ ^ k) (multivariateGaussian (0 : 𝔼) Q) := by
  have := (IsGaussian.memLp_id (multivariateGaussian (0 : 𝔼) Q) k (by simpa using hk)).integrable_norm_pow
    (p := k) (by simpa using hk)
  simpa using this

/-- Third absolute moment of the Gaussian with the same covariance. -/
theorem gauss_m3_le (ρ : Measure 𝔼) [IsProbabilityMeasure ρ]
    (h2 : Integrable (fun x : 𝔼 => ‖x‖ ^ 2) ρ) (h3 : Integrable (fun x : 𝔼 => ‖x‖ ^ 3) ρ) :
    ∫ y, ‖y‖ ^ 3 ∂(multivariateGaussian (0 : 𝔼) (momentMatrix ρ)) ≤
      (1 + c4 / 2) * ∫ x, ‖x‖ ^ 3 ∂ρ := by
  have hQ := momentMatrix_posSemidef ρ h2
  set γ := multivariateGaussian (0 : 𝔼) (momentMatrix ρ) with hγ
  set m2 := ∫ x, ‖x‖ ^ 2 ∂ρ with hm2
  have hm2γ : ∫ y, ‖y‖ ^ 2 ∂γ = m2 := by
    rw [hγ, integral_norm_sq_gauss hQ, trace_momentMatrix ρ h2]
  have hm4 : ∫ y, ‖y‖ ^ 4 ∂γ ≤ c4 * m2 ^ 2 := by
    have := integral_norm_pow4_le hQ
    rwa [trace_momentMatrix ρ h2] at this
  have hM0 : 0 ≤ ∫ x, ‖x‖ ^ 3 ∂ρ := integral_nonneg fun x => by positivity
  have hm0 : 0 ≤ m2 := integral_nonneg fun x => by positivity
  have hc4 := c4_nonneg
  have i2 : Integrable (fun y : 𝔼 => ‖y‖ ^ 2) γ := integrable_norm_pow_gauss 2 (by norm_num)
  have i3 : Integrable (fun y : 𝔼 => ‖y‖ ^ 3) γ := integrable_norm_pow_gauss 3 (by norm_num)
  have i4 : Integrable (fun y : 𝔼 => ‖y‖ ^ 4) γ := integrable_norm_pow_gauss 4 (by norm_num)
  have hm3γ0 : 0 ≤ ∫ y, ‖y‖ ^ 3 ∂γ := integral_nonneg fun y => by positivity
  -- integrated AM-GM
  have key : ∀ t : ℝ, 0 < t → 2 * t * ∫ y, ‖y‖ ^ 3 ∂γ ≤ t ^ 2 * m2 + ∫ y, ‖y‖ ^ 4 ∂γ := by
    intro t ht
    have hpt : ∀ y : 𝔼, 2 * t * ‖y‖ ^ 3 ≤ t ^ 2 * ‖y‖ ^ 2 + ‖y‖ ^ 4 := fun y => by
      nlinarith [mul_nonneg (sq_nonneg ‖y‖) (sq_nonneg (t - ‖y‖))]
    have iR : Integrable (fun y : 𝔼 => t ^ 2 * ‖y‖ ^ 2 + ‖y‖ ^ 4) γ := (i2.const_mul _).add i4
    have := integral_mono (i3.const_mul (2 * t)) iR hpt
    rw [integral_const_mul, integral_add (i2.const_mul _) i4, integral_const_mul, hm2γ] at this
    exact this
  have hlya := lyapunov ρ h2 h3
  set u := Real.sqrt m2 with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = m2 := Real.sq_sqrt hm0
  rcases hu0.eq_or_lt with h0 | hpos
  · have hm2z : m2 = 0 := by rw [← hu2, ← h0]; ring
    have := key 1 one_pos
    rw [hm2z] at this hm4
    nlinarith
  · have hk := key ((1 + c4) * u) (by positivity)
    have hm4' : ∫ y, ‖y‖ ^ 4 ∂γ ≤ c4 * u ^ 4 := by
      refine hm4.trans (le_of_eq ?_)
      rw [← hu2]; ring
    set m3 := ∫ y, ‖y‖ ^ 3 ∂γ with hm3
    have h1 : 2 * (1 + c4) * u * m3 ≤ 2 * (1 + c4) * u * ((1 + c4 / 2) * u ^ 3) := by
      have e : 2 * (1 + c4) * u * ((1 + c4 / 2) * u ^ 3) = (1 + c4) * (2 + c4) * u ^ 4 := by ring
      rw [e]
      have : ((1 + c4) * u) ^ 2 * m2 = (1 + c4) ^ 2 * u ^ 4 := by rw [← hu2]; ring
      nlinarith [pow_nonneg hu0 4]
    have h2' : m3 ≤ (1 + c4 / 2) * u ^ 3 := le_of_mul_le_mul_left h1 (by positivity)
    calc m3 ≤ (1 + c4 / 2) * u ^ 3 := h2'
      _ ≤ (1 + c4 / 2) * ∫ x, ‖x‖ ^ 3 ∂ρ := by gcongr

lemma pi_map_sum_gauss {N : ℕ} (Q : Fin N → Matrix (Fin n) (Fin n) ℝ) (hQ : ∀ i, (Q i).PosSemidef) :
    (Measure.pi fun i => multivariateGaussian (0 : 𝔼) (Q i)).map (fun p => ∑ i, p i) =
      multivariateGaussian (0 : 𝔼) (∑ i, Q i) := by
  have hsum : (∑ i, Q i).PosSemidef := Matrix.posSemidef_sum _ fun i _ => hQ i
  refine Measure.ext_of_charFun ?_
  rw [charFun_map_sum_pi_eq_prod]
  ext t
  rw [Finset.prod_apply, charFun_multivariateGaussian hsum]
  simp_rw [charFun_multivariateGaussian (hQ _)]
  rw [← Complex.exp_sum]
  congr 1
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub, Finset.sum_neg_distrib,
    Matrix.sum_mulVec, dotProduct_sum]
  push_cast
  rw [Finset.sum_div]



/-- **Lindeberg replacement by Gaussians** with matching covariance: for independent centred
`ρ_i` with finite third moments and `Z ∼ N(0, ∑ Cov ρ_i)`. -/
theorem lindeberg_gauss {N : ℕ} {K : ℝ} {f : 𝔼 → ℝ} (hf : TestFn K f)
    (ρ : Fin N → Measure 𝔼) [∀ i, IsProbabilityMeasure (ρ i)]
    (h0ρ : ∀ i c, ∫ x, x c ∂(ρ i) = 0)
    (h3ρ : ∀ i, Integrable (fun x : 𝔼 => ‖x‖ ^ 3) (ρ i)) :
    |∫ x, f x ∂((Measure.pi ρ).map (fun p => ∑ i, p i)) -
        ∫ x, f x ∂(multivariateGaussian (0 : 𝔼) (∑ i, momentMatrix (ρ i)))| ≤
      K * ((2 + c4 / 2) * ∑ i, ∫ x, ‖x‖ ^ 3 ∂(ρ i)) := by
  have h2ρ : ∀ i, Integrable (fun x : 𝔼 => ‖x‖ ^ 2) (ρ i) := fun i =>
    (integrable_norm_of_pow3 (P := ρ i) (Y := id) measurable_id (h3ρ i)).2
  have hQ : ∀ i, (momentMatrix (ρ i)).PosSemidef := fun i => momentMatrix_posSemidef _ (h2ρ i)
  set γ : Fin N → Measure 𝔼 := fun i => multivariateGaussian (0 : 𝔼) (momentMatrix (ρ i)) with hγ
  have key := lindeberg_pi hf ρ γ h0ρ (fun i c => integral_coord_zero c)
    (fun i c d => by simp only [hγ]; rw [integral_coord_mul (hQ i)]; rfl)
    h3ρ (fun i => integrable_norm_pow_gauss 3 (by norm_num))
  rw [show (Measure.pi γ) = Measure.pi fun i => multivariateGaussian (0 : 𝔼) (momentMatrix (ρ i))
    from rfl, pi_map_sum_gauss _ hQ] at key
  refine key.trans ?_
  have hm3 : ∀ i, ∫ x, ‖x‖ ^ 3 ∂(γ i) ≤ (1 + c4 / 2) * ∫ x, ‖x‖ ^ 3 ∂(ρ i) := fun i =>
    gauss_m3_le (ρ i) (h2ρ i) (h3ρ i)
  have : ∑ i, (∫ x, ‖x‖ ^ 3 ∂(ρ i) + ∫ x, ‖x‖ ^ 3 ∂(γ i)) ≤
      (2 + c4 / 2) * ∑ i, ∫ x, ‖x‖ ^ 3 ∂(ρ i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have := hm3 i
    nlinarith
  exact mul_le_mul_of_nonneg_left this hf.K_nonneg

end PiForm

end HRS.Yurinskii
