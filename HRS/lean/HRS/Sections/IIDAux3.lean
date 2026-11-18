import HRS.Sections.IIDAux2

/-!
# IID helper chain, part 3: Lindeberg with Gaussian smoothing on measures
(see the chain plan in `IIDAux1`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Convolution

namespace HRS.IID

section Gauss

variable {p : ℕ}

lemma integral_inner_mul_inner (a b : EuclideanSpace ℝ (Fin p)) :
    ∫ u, inner ℝ a u * inner ℝ b u ∂(gam p) = inner ℝ a b := by
  have h2 : ∀ c : EuclideanSpace ℝ (Fin p), Integrable (fun z => (inner ℝ c z) ^ 2) (gam p) := fun c => by
    simpa using integrable_inner_pow c 1
  have e : ∀ u, inner ℝ a u * inner ℝ b u =
      ((inner ℝ (a + b) u) ^ 2 - (inner ℝ (a - b) u) ^ 2) / 4 := fun u => by
    simp only [inner_add_left, inner_sub_left]; ring
  simp_rw [e]
  rw [integral_div, integral_sub (h2 _) (h2 _), integral_inner_sq, integral_inner_sq,
    norm_add_sq_real, norm_sub_sq_real]
  ring

/-- Law of `s • B u` for `u` standard Gaussian: `N(0, s² B²)`. -/
def nuS (B : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    Measure (EuclideanSpace ℝ (Fin p)) := (gam p).map (fun u => s • B u)

variable {B : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)}

lemma measurable_smulB (B : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    Measurable fun u : EuclideanSpace ℝ (Fin p) => s • B u := by fun_prop

instance isProb_nuS (s : ℝ) : IsProbabilityMeasure (nuS B s) := by
  unfold nuS; infer_instance

lemma integral_nuS (s : ℝ) {h : EuclideanSpace ℝ (Fin p) → ℝ} (hh : Continuous h) :
    ∫ z, h z ∂(nuS B s) = ∫ u, h (s • B u) ∂(gam p) := by
  unfold nuS
  exact integral_map (measurable_smulB B s).aemeasurable hh.aestronglyMeasurable

lemma charFun_nuS (hBs : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y)) (s : ℝ)
    (w : EuclideanSpace ℝ (Fin p)) :
    charFun (nuS B s) w = charFun (gam p) (s • B w) := by
  unfold nuS
  rw [charFun_apply, charFun_apply, integral_map (measurable_smulB B s).aemeasurable (by fun_prop)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  congr 3
  rw [real_inner_smul_left, real_inner_smul_right, hBs]

lemma charFun_nuS_eq (hBs : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y)) (s : ℝ)
    (w : EuclideanSpace ℝ (Fin p)) :
    charFun (nuS B s) w = Complex.exp (-((s ^ 2 * ‖B w‖ ^ 2 / 2 : ℝ) : ℂ)) := by
  rw [charFun_nuS hBs, charFun_stdGaussian, norm_smul]
  congr 1
  have h : (‖s‖ * ‖B w‖) ^ 2 = s ^ 2 * ‖B w‖ ^ 2 := by rw [mul_pow, Real.norm_eq_abs, sq_abs]
  have h' : ((‖s‖ * ‖B w‖ : ℝ) : ℂ) ^ 2 = ((s ^ 2 * ‖B w‖ ^ 2 : ℝ) : ℂ) := by
    rw [← h]; push_cast; ring
  rw [h']; push_cast; ring

lemma nuS_conv (hBs : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y)) (a b c : ℝ)
    (h : c ^ 2 = a ^ 2 + b ^ 2) : nuS B a ∗ nuS B b = nuS B c := by
  refine Measure.ext_of_charFun ?_
  funext w
  rw [charFun_conv, charFun_nuS_eq hBs, charFun_nuS_eq hBs, charFun_nuS_eq hBs,
    ← Complex.exp_add]
  congr 1
  rw [h]
  push_cast
  ring

lemma nuS_zero : nuS B 0 = Measure.dirac 0 := by
  unfold nuS
  have : (fun u : EuclideanSpace ℝ (Fin p) => (0 : ℝ) • B u) = fun _ => 0 := by
    funext u; simp
  rw [this, Measure.map_const]
  simp

lemma integral_nuS_inner (hBs : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y)) (s : ℝ)
    (w : EuclideanSpace ℝ (Fin p)) : ∫ z, inner ℝ w z ∂(nuS B s) = 0 := by
  rw [integral_nuS s (by fun_prop)]
  have e : ∀ u, inner ℝ w (s • B u) = s * inner ℝ (B w) u := fun u => by
    rw [real_inner_smul_right, ← hBs]
  simp_rw [e]
  rw [integral_const_mul]
  have := integral_strongDual_stdGaussian (innerSL ℝ (B w))
  simp only [innerSL_apply_apply] at this
  rw [this, mul_zero]

lemma integral_nuS_inner_mul (hBs : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y)) (s : ℝ)
    (w w' : EuclideanSpace ℝ (Fin p)) :
    ∫ z, inner ℝ w z * inner ℝ w' z ∂(nuS B s) = s ^ 2 * inner ℝ (B w) (B w') := by
  rw [integral_nuS s (by fun_prop)]
  have e : ∀ u, inner ℝ w (s • B u) * inner ℝ w' (s • B u) =
      s ^ 2 * (inner ℝ (B w) u * inner ℝ (B w') u) := fun u => by
    rw [real_inner_smul_right, real_inner_smul_right, ← hBs, ← hBs]; ring
  simp_rw [e]
  rw [integral_const_mul, integral_inner_mul_inner]

lemma isGaussian_nuS (s : ℝ) : IsGaussian (nuS B s) := by
  have : nuS B s = (gam p).map ⇑(s • B) := rfl
  rw [this]; infer_instance

lemma isCenteredGaussian_nuS (s : ℝ) : IsCenteredGaussian (nuS B s) := by
  refine ⟨isGaussian_nuS s, fun L => ?_⟩
  have : nuS B s = (gam p).map ⇑(s • B) := rfl
  rw [this, integral_map (s • B).continuous.aemeasurable L.continuous.aestronglyMeasurable]
  exact integral_strongDual_stdGaussian (L.comp (s • B))

lemma integrable_nuS_norm_sq (s : ℝ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin p) => ‖z‖ ^ 2) (nuS B s) := by
  have hi := HRS.EdgeAux.gaussian_integrable_pow (isCenteredGaussian_gam (p := p)) 2
  unfold nuS
  rw [integrable_map_measure (by fun_prop) (measurable_smulB B s).aemeasurable]
  refine (hi.const_mul ((|s| * ‖B‖) ^ 2)).mono' (by fun_prop) (Filter.Eventually.of_forall fun u => ?_)
  simp only [Function.comp, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity), norm_smul, Real.norm_eq_abs, ← mul_pow]
  have : ‖B u‖ ≤ ‖B‖ * ‖u‖ := B.le_opNorm u
  calc (|s| * ‖B u‖) ^ 2 ≤ (|s| * (‖B‖ * ‖u‖)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left this (abs_nonneg _)) 2
    _ = (|s| * ‖B‖ * ‖u‖) ^ 2 := by ring

/-- Convolution powers. -/
def cpow (μ : Measure (EuclideanSpace ℝ (Fin p))) : ℕ → Measure (EuclideanSpace ℝ (Fin p))
  | 0 => Measure.dirac 0
  | k + 1 => μ ∗ cpow μ k

instance isProb_cpow (μ : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure μ] (k : ℕ) :
    IsProbabilityMeasure (cpow μ k) := by
  induction k with
  | zero => simp only [cpow]; infer_instance
  | succ k ih => simp only [cpow]; infer_instance

lemma cpow_nuS (hBs : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y)) (s : ℝ) (k : ℕ) :
    cpow (nuS B s) k = nuS B (Real.sqrt k * s) := by
  induction k with
  | zero => simp [cpow, nuS_zero]
  | succ k ih =>
    simp only [cpow]
    rw [ih, nuS_conv hBs s (Real.sqrt k * s) (Real.sqrt ((k + 1 : ℕ) : ℝ) * s)]
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    push_cast; ring

lemma pi_map_sum_eq_cpow (μ : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure μ] (N : ℕ) :
    (Measure.pi fun _ : Fin N => μ).map (fun x => ∑ i, x i) = cpow μ N := by
  induction N with
  | zero =>
    simp only [cpow]
    rw [Measure.pi_of_empty]
    have hm : Measurable (fun x : Fin 0 → EuclideanSpace ℝ (Fin p) => ∑ i, x i) := by fun_prop
    rw [Measure.map_dirac' hm]
    simp
  | succ N ih =>
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => μ) 0
    have hsum : (fun x : Fin (N + 1) → EuclideanSpace ℝ (Fin p) => ∑ i, x i) =
        (fun q : EuclideanSpace ℝ (Fin p) × (Fin N → EuclideanSpace ℝ (Fin p)) => q.1 + ∑ j, q.2 j) ∘
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => EuclideanSpace ℝ (Fin p)) 0) := by
      funext x
      simp [Fin.sum_univ_succ, MeasurableEquiv.piFinSuccAbove, Fin.tail]
    rw [hsum, ← Measure.map_map (by fun_prop) hmp.measurable, hmp.map_eq]
    simp only [cpow]
    rw [← ih, Measure.conv]
    have hsm : Measurable (fun x : Fin N → EuclideanSpace ℝ (Fin p) => ∑ i, x i) := by fun_prop
    have h1 : μ.prod ((Measure.pi fun _ : Fin N => μ).map (fun x => ∑ i, x i)) =
        (μ.prod (Measure.pi fun _ : Fin N => μ)).map (Prod.map id (fun x => ∑ i, x i)) := by
      rw [← Measure.map_prod_map _ _ measurable_id hsm, Measure.map_id]
    rw [h1, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl

end Gauss

section MM

variable {p : ℕ}

/-- First two moments of a measure: centred, finite second moment, covariance `κ B²`. -/
structure MomMatch (B : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)) (κ : ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin p))) : Prop where
  int2 : Integrable (fun y => ‖y‖ ^ 2) μ
  mean : ∀ w, ∫ y, inner ℝ w y ∂μ = 0
  cov : ∀ w w', ∫ y, inner ℝ w y * inner ℝ w' y ∂μ = κ * inner ℝ (B w) (B w')

lemma nuS_momMatch {B : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)}
    (hBs : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y)) (s : ℝ) : MomMatch B (s ^ 2) (nuS B s) :=
  ⟨integrable_nuS_norm_sq s, integral_nuS_inner hBs s, integral_nuS_inner_mul hBs s⟩

variable {B : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)} {κ : ℝ}
  {μ : Measure (EuclideanSpace ℝ (Fin p))} [IsProbabilityMeasure μ]

lemma MomMatch.integrable_norm (h : MomMatch B κ μ) :
    Integrable (fun y : EuclideanSpace ℝ (Fin p) => ‖y‖) μ := by
  refine ((integrable_const (1 : ℝ)).add h.int2).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  show ‖y‖ ≤ 1 + ‖y‖ ^ 2
  nlinarith [sq_nonneg (‖y‖ - 1)]

lemma MomMatch.integrable_inner_mul (h : MomMatch B κ μ) (a b : EuclideanSpace ℝ (Fin p)) :
    Integrable (fun y => inner ℝ a y * inner ℝ b y) μ := by
  refine (h.int2.const_mul (‖a‖ * ‖b‖)).mono' (by fun_prop) (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |inner ℝ a y| ≤ ‖a‖ * ‖y‖ := by
    have := abs_real_inner_le_norm a y; exact this
  have h2 : |inner ℝ b y| ≤ ‖b‖ * ‖y‖ := by
    have := abs_real_inner_le_norm b y; exact this
  calc |inner ℝ a y| * |inner ℝ b y| ≤ (‖a‖ * ‖y‖) * (‖b‖ * ‖y‖) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = ‖a‖ * ‖b‖ * ‖y‖ ^ 2 := by ring

lemma MomMatch.integrable_inner (h : MomMatch B κ μ) (a : EuclideanSpace ℝ (Fin p)) :
    Integrable (fun y => inner ℝ a y) μ := by
  refine (h.integrable_norm.const_mul ‖a‖).mono' (by fun_prop) (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  exact abs_real_inner_le_norm a y

lemma adj_inner (N : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (e y : EuclideanSpace ℝ (Fin p)) :
    inner ℝ (ContinuousLinearMap.adjoint N e) y = inner ℝ (N y) e := by
  rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm]

lemma MomMatch.integral_inner_N (h : MomMatch B κ μ)
    (N : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)) (u : EuclideanSpace ℝ (Fin p)) :
    ∫ y, inner ℝ (N y) u ∂μ = 0 := by
  have e : ∀ y, inner ℝ (N y) u = inner ℝ (ContinuousLinearMap.adjoint N u) y := fun y =>
    (adj_inner N u y).symm
  simp_rw [e]
  exact h.mean _

lemma MomMatch.integral_inner_N_sq (h : MomMatch B κ μ)
    (N : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)) (u : EuclideanSpace ℝ (Fin p)) :
    ∫ y, (inner ℝ (N y) u) ^ 2 ∂μ = κ * ‖B (ContinuousLinearMap.adjoint N u)‖ ^ 2 := by
  have e : ∀ y, (inner ℝ (N y) u) ^ 2 =
      inner ℝ (ContinuousLinearMap.adjoint N u) y * inner ℝ (ContinuousLinearMap.adjoint N u) y := fun y => by
    rw [sq, adj_inner]
  simp_rw [e]
  rw [h.cov, real_inner_self_eq_norm_sq]

lemma MomMatch.integral_norm_N_sq (h : MomMatch B κ μ)
    (N : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)) :
    ∫ y, ‖N y‖ ^ 2 ∂μ =
      κ * ∑ i : Fin p, ‖B (ContinuousLinearMap.adjoint N (EuclideanSpace.single i (1 : ℝ)))‖ ^ 2 := by
  have e : ∀ y, ‖N y‖ ^ 2 = ∑ i : Fin p, (inner ℝ (N y) (EuclideanSpace.single i (1 : ℝ))) ^ 2 := fun y => by
    rw [EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm, EuclideanSpace.inner_single_left]; simp
  simp_rw [e]
  rw [integral_finsetSum _ (fun i _ => ?_), Finset.mul_sum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    exact h.integral_inner_N_sq N _
  · have := h.integrable_inner_mul (ContinuousLinearMap.adjoint N (EuclideanSpace.single i (1 : ℝ)))
      (ContinuousLinearMap.adjoint N (EuclideanSpace.single i (1 : ℝ)))
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [sq, adj_inner]

lemma integrable_norm_gam : Integrable (fun u : EuclideanSpace ℝ (Fin p) => ‖u‖) (gam p) := by
  simpa using HRS.EdgeAux.gaussian_integrable_pow (isCenteredGaussian_gam (p := p)) 1

lemma integrable_norm_sq_gam : Integrable (fun u : EuclideanSpace ℝ (Fin p) => ‖u‖ ^ 2) (gam p) :=
  HRS.EdgeAux.gaussian_integrable_pow (isCenteredGaussian_gam (p := p)) 2

lemma integrable_q_inner {q : EuclideanSpace ℝ (Fin p) → ℝ} (hq : Continuous q) {W : ℝ}
    (hW : ∀ u, |q u| ≤ W) (c : EuclideanSpace ℝ (Fin p)) :
    Integrable (fun u => q u * inner ℝ c u) (gam p) := by
  refine (integrable_norm_gam.const_mul (W * ‖c‖)).mono' (by fun_prop)
    (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc |q u| * |inner ℝ c u| ≤ W * (‖c‖ * ‖u‖) :=
        mul_le_mul (hW u) (abs_real_inner_le_norm c u) (abs_nonneg _) ((abs_nonneg _).trans (hW u))
    _ = W * ‖c‖ * ‖u‖ := by ring

lemma integrable_q_inner_sq {q : EuclideanSpace ℝ (Fin p) → ℝ} (hq : Continuous q) {W : ℝ}
    (hW : ∀ u, |q u| ≤ W) (c : EuclideanSpace ℝ (Fin p)) :
    Integrable (fun u => q u * ((inner ℝ c u) ^ 2 - ‖c‖ ^ 2)) (gam p) := by
  have h2 : Integrable (fun u : EuclideanSpace ℝ (Fin p) => (inner ℝ c u) ^ 2 - ‖c‖ ^ 2) (gam p) := by
    have := integrable_inner_pow c 1
    simp only [mul_one] at this
    exact this.sub (integrable_const _)
  exact h2.bdd_mul (c := W) hq.aestronglyMeasurable (Filter.Eventually.of_forall fun u => by
    simpa [Real.norm_eq_abs] using hW u)

/-- The linear-plus-quadratic part of the Taylor expansion of the smoothed function. -/
def Tform (N : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (q : EuclideanSpace ℝ (Fin p) → ℝ) (y : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ∫ u, q u * inner ℝ (N y) u ∂(gam p) +
    (∫ u, q u * ((inner ℝ (N y) u) ^ 2 - ‖N y‖ ^ 2) ∂(gam p)) / 2

/-- Common value of `∫ Tform dμ` for all `μ` with the prescribed first two moments. -/
def Tconst (B N : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)) (κ : ℝ)
    (q : EuclideanSpace ℝ (Fin p) → ℝ) : ℝ :=
  ∫ u, q u * (κ * ‖B (ContinuousLinearMap.adjoint N u)‖ ^ 2 / 2 -
    κ * (∑ i : Fin p, ‖B (ContinuousLinearMap.adjoint N (EuclideanSpace.single i (1 : ℝ)))‖ ^ 2) / 2) ∂(gam p)

/-- The joint integrand of `Tform`. -/
def Gjoint (N : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (q : EuclideanSpace ℝ (Fin p) → ℝ) (y u : EuclideanSpace ℝ (Fin p)) : ℝ :=
  q u * (inner ℝ (N y) u + ((inner ℝ (N y) u) ^ 2 - ‖N y‖ ^ 2) / 2)

lemma Tform_eq {q : EuclideanSpace ℝ (Fin p) → ℝ} (hq : Continuous q) {W : ℝ} (hW : ∀ u, |q u| ≤ W)
    (N : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)) (y : EuclideanSpace ℝ (Fin p)) :
    Tform N q y = ∫ u, Gjoint N q y u ∂(gam p) := by
  unfold Tform
  have i1 := integrable_q_inner hq hW (N y)
  have i2 := integrable_q_inner_sq hq hW (N y)
  have e : ∀ u, Gjoint N q y u = q u * inner ℝ (N y) u +
      (q u * ((inner ℝ (N y) u) ^ 2 - ‖N y‖ ^ 2)) / 2 := fun u => by simp only [Gjoint]; ring
  simp_rw [e]
  rw [integral_add i1 (i2.div_const 2), integral_div]

lemma integrable_Gjoint (h : MomMatch B κ μ) {q : EuclideanSpace ℝ (Fin p) → ℝ} (hq : Continuous q)
    {W : ℝ} (hW : ∀ u, |q u| ≤ W) (N : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)) :
    Integrable (Function.uncurry (Gjoint N q)) (μ.prod (gam p)) := by
  have hW0 : 0 ≤ W := (abs_nonneg _).trans (hW 0)
  have hNn : 0 ≤ ‖N‖ := norm_nonneg _
  have hbound : ∀ y u, |Gjoint N q y u| ≤ W * (‖N‖ * (‖y‖ * ‖u‖) +
      (‖N‖ ^ 2 * (‖y‖ ^ 2 * ‖u‖ ^ 2) + ‖N‖ ^ 2 * (‖y‖ ^ 2 * 1)) / 2) := fun y u => by
    have hNy : ‖N y‖ ≤ ‖N‖ * ‖y‖ := N.le_opNorm y
    have h1 : |inner ℝ (N y) u| ≤ ‖N‖ * (‖y‖ * ‖u‖) := by
      calc |inner ℝ (N y) u| ≤ ‖N y‖ * ‖u‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖N‖ * ‖y‖) * ‖u‖ := mul_le_mul_of_nonneg_right hNy (norm_nonneg _)
        _ = ‖N‖ * (‖y‖ * ‖u‖) := by ring
    have h2 : (inner ℝ (N y) u) ^ 2 ≤ ‖N‖ ^ 2 * (‖y‖ ^ 2 * ‖u‖ ^ 2) := by
      calc (inner ℝ (N y) u) ^ 2 = |inner ℝ (N y) u| ^ 2 := (sq_abs _).symm
        _ ≤ (‖N‖ * (‖y‖ * ‖u‖)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ = ‖N‖ ^ 2 * (‖y‖ ^ 2 * ‖u‖ ^ 2) := by ring
    have h3 : ‖N y‖ ^ 2 ≤ ‖N‖ ^ 2 * (‖y‖ ^ 2 * 1) := by
      calc ‖N y‖ ^ 2 ≤ (‖N‖ * ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hNy 2
        _ = ‖N‖ ^ 2 * (‖y‖ ^ 2 * 1) := by ring
    unfold Gjoint
    rw [abs_mul]
    refine mul_le_mul (hW u) ?_ (abs_nonneg _) hW0
    calc |inner ℝ (N y) u + ((inner ℝ (N y) u) ^ 2 - ‖N y‖ ^ 2) / 2|
        ≤ |inner ℝ (N y) u| + |((inner ℝ (N y) u) ^ 2 - ‖N y‖ ^ 2) / 2| := abs_add_le _ _
      _ ≤ ‖N‖ * (‖y‖ * ‖u‖) + (‖N‖ ^ 2 * (‖y‖ ^ 2 * ‖u‖ ^ 2) + ‖N‖ ^ 2 * (‖y‖ ^ 2 * 1)) / 2 := by
          gcongr
          rw [abs_div, abs_two]
          gcongr
          rw [abs_le]
          constructor <;> nlinarith [sq_nonneg (inner ℝ (N y) u), sq_nonneg ‖N y‖]
  have b1 := h.integrable_norm.mul_prod (integrable_norm_gam (p := p))
  have b2 := h.int2.mul_prod (integrable_norm_sq_gam (p := p))
  have b3 := h.int2.mul_prod (integrable_const (1 : ℝ) (μ := gam p))
  have hb : Integrable (fun z : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin p) =>
      W * (‖N‖ * (‖z.1‖ * ‖z.2‖) +
        (‖N‖ ^ 2 * (‖z.1‖ ^ 2 * ‖z.2‖ ^ 2) + ‖N‖ ^ 2 * (‖z.1‖ ^ 2 * 1)) / 2)) (μ.prod (gam p)) :=
    ((b1.const_mul ‖N‖).add (((b2.const_mul (‖N‖ ^ 2)).add (b3.const_mul (‖N‖ ^ 2))).div_const 2)).const_mul W
  refine hb.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · have : Continuous (fun z : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin p) =>
        Gjoint N q z.1 z.2) := by
      unfold Gjoint
      fun_prop
    exact this.aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact hbound z.1 z.2

lemma integrable_Tform (h : MomMatch B κ μ) {q : EuclideanSpace ℝ (Fin p) → ℝ}
    (hq : Continuous q) {W : ℝ} (hW : ∀ u, |q u| ≤ W)
    (N : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)) :
    Integrable (Tform N q) μ := by
  have := (integrable_Gjoint h hq hW N).integral_prod_left
  refine this.congr (Filter.Eventually.of_forall fun y => ?_)
  exact (Tform_eq hq hW N y).symm

lemma integral_Tform (h : MomMatch B κ μ) {q : EuclideanSpace ℝ (Fin p) → ℝ} (hq : Continuous q)
    {W : ℝ} (hW : ∀ u, |q u| ≤ W) (N : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)) :
    ∫ y, Tform N q y ∂μ = Tconst B N κ q := by
  have hint := integrable_Gjoint h hq hW N
  simp_rw [Tform_eq hq hW N]
  rw [integral_integral_swap hint]
  unfold Tconst
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [Gjoint]
  have i1 : Integrable (fun y => inner ℝ (N y) u) μ := by
    have := h.integrable_inner (ContinuousLinearMap.adjoint N u)
    exact this.congr (Filter.Eventually.of_forall fun y => adj_inner N u y)
  have i2 : Integrable (fun y => (inner ℝ (N y) u) ^ 2) μ := by
    have := h.integrable_inner_mul (ContinuousLinearMap.adjoint N u) (ContinuousLinearMap.adjoint N u)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [sq, adj_inner]
  have i3 : Integrable (fun y => ‖N y‖ ^ 2) μ := by
    refine (h.int2.const_mul (‖N‖ ^ 2)).mono' (by fun_prop) (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖N y‖ ^ 2 ≤ (‖N‖ * ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (N.le_opNorm y) 2
      _ = ‖N‖ ^ 2 * ‖y‖ ^ 2 := by ring
  have i4 : Integrable (fun y => ((inner ℝ (N y) u) ^ 2 - ‖N y‖ ^ 2) / 2) μ :=
    (i2.sub i3).div_const 2
  rw [integral_const_mul, integral_add i1 i4, integral_div,
    integral_sub i2 i3, h.integral_inner_N, h.integral_inner_N_sq, h.integral_norm_N_sq]
  ring

end MM

section Step

variable {p : ℕ} {B binv : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)}

/-- The Gaussian-smoothed test function `x ↦ E f(x + √t B u)`. -/
def smoothF (B : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)) (t : ℝ)
    (f : EuclideanSpace ℝ (Fin p) → ℝ) (x : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ∫ u, f (x + Real.sqrt t • B u) ∂(gam p)

/-- The direction map `y ↦ (√t)⁻¹ B⁻¹ y` with `√t B (N y) = y`. -/
def Nmap (binv : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)) (t : ℝ) :
    EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p) := (Real.sqrt t)⁻¹ • binv

lemma shift_key (hBb : ∀ y, B (binv y) = y) {t : ℝ} (ht : 0 < t) (x u y : EuclideanSpace ℝ (Fin p))
    (s : ℝ) :
    x + Real.sqrt t • B (u + s • Nmap binv t y) = (x + Real.sqrt t • B u) + s • y := by
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  have h1 : B (Nmap binv t y) = (Real.sqrt t)⁻¹ • y := by
    simp only [Nmap, ContinuousLinearMap.smul_apply, map_smul, hBb]
  rw [map_add, map_smul, h1, smul_add, smul_smul, smul_smul]
  have h2 : Real.sqrt t * s * (Real.sqrt t)⁻¹ = s := by field_simp
  rw [h2]
  abel

lemma smooth_taylor_lip (hBb : ∀ y, B (binv y) = y) {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : LipschitzWith 1 f) {R : ℝ} (hR : ∀ z, |f z| ≤ R)
    (x y : EuclideanSpace ℝ (Fin p)) :
    |smoothF B t f (x + y) - smoothF B t f x -
        Tform (Nmap binv t) (fun u => f (x + Real.sqrt t • B u)) y| ≤
      Real.sqrt 2 * ‖y‖ * ‖Nmap binv t y‖ ^ 2 / 6 := by
  set c := Nmap binv t y with hc
  set q : EuclideanSpace ℝ (Fin p) → ℝ := fun u => f (x + Real.sqrt t • B u) with hq
  have hqm : Measurable q := hf.continuous.measurable.comp (by fun_prop)
  have hL : ∀ (z : EuclideanSpace ℝ (Fin p)) (s : ℝ), 0 ≤ s → |q (z + s • c) - q z| ≤ ‖y‖ * s := by
    intro z s hs
    simp only [hq]
    rw [shift_key hBb ht x z y s]
    have := hf.dist_le_mul ((x + Real.sqrt t • B z) + s • y) (x + Real.sqrt t • B z)
    rw [Real.dist_eq, dist_eq_norm] at this
    simp only [NNReal.coe_one, one_mul, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs] at this
    calc |f ((x + Real.sqrt t • B z) + s • y) - f (x + Real.sqrt t • B z)| ≤ s * ‖y‖ := this
      _ = ‖y‖ * s := by ring
  have hmain := taylor_line_lip c hqm (W := R) (fun u => hR _) hL
  have e1 : ∫ z, q (z + c) ∂(gam p) = smoothF B t f (x + y) := by
    unfold smoothF
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have := shift_key hBb ht x u y 1
    simp only [one_smul] at this
    simp only [hq, hc, this]
    congr 1; abel
  have e0 : ∫ z, q z ∂(gam p) = smoothF B t f x := rfl
  unfold Tform at *
  rw [e1, e0] at hmain
  have : smoothF B t f (x + y) - smoothF B t f x -
      (∫ u, q u * inner ℝ (Nmap binv t y) u ∂(gam p) +
        (∫ u, q u * ((inner ℝ (Nmap binv t y) u) ^ 2 - ‖Nmap binv t y‖ ^ 2) ∂(gam p)) / 2) =
      smoothF B t f (x + y) - smoothF B t f x - ∫ u, q u * inner ℝ c u ∂(gam p) -
        (∫ u, q u * ((inner ℝ c u) ^ 2 - ‖c‖ ^ 2) ∂(gam p)) / 2 := by ring
  rw [this]
  calc _ ≤ Real.sqrt 2 * ‖y‖ * ‖c‖ ^ 2 / 6 := hmain
    _ = _ := rfl

lemma smooth_taylor_C2 (hBb : ∀ y, B (binv y) = y) {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : ContDiff ℝ 2 f) {M0 M1 M2 : ℝ}
    (h0 : ∀ z, |f z| ≤ M0) (h1 : ∀ z, ‖fderiv ℝ f z‖ ≤ M1)
    (h2 : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ M2) (x y : EuclideanSpace ℝ (Fin p)) :
    |smoothF B t f (x + y) - smoothF B t f x -
        Tform (Nmap binv t) (fun u => f (x + Real.sqrt t • B u)) y| ≤
      2 * (M2 * ‖y‖ * ‖y‖) * ‖Nmap binv t y‖ / 6 := by
  set c := Nmap binv t y with hc
  have hmain := taylor_line_C2 hf h0 h1 h2 (fun u => x + Real.sqrt t • B u) (by fun_prop) c y
    (fun u s => shift_key hBb ht x u y s)
  have e1 : ∫ u, f (x + Real.sqrt t • B (u + c)) ∂(gam p) = smoothF B t f (x + y) := by
    unfold smoothF
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    have := shift_key hBb ht x u y 1
    simp only [one_smul] at this
    simp only [hc, this]
    congr 1; abel
  rw [e1] at hmain
  unfold Tform
  have : smoothF B t f (x + y) - smoothF B t f x -
      (∫ u, f (x + Real.sqrt t • B u) * inner ℝ (Nmap binv t y) u ∂(gam p) +
        (∫ u, f (x + Real.sqrt t • B u) * ((inner ℝ (Nmap binv t y) u) ^ 2 - ‖Nmap binv t y‖ ^ 2) ∂(gam p)) / 2) =
      smoothF B t f (x + y) - ∫ u, f (x + Real.sqrt t • B u) ∂(gam p) -
        ∫ u, f (x + Real.sqrt t • B u) * inner ℝ c u ∂(gam p) -
        (∫ u, f (x + Real.sqrt t • B u) * ((inner ℝ c u) ^ 2 - ‖c‖ ^ 2) ∂(gam p)) / 2 := by
    unfold smoothF; ring
  rw [this]
  exact hmain

lemma measurable_smooth {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : Measurable f)
    (ρ : Measure (EuclideanSpace ℝ (Fin p))) [SFinite ρ] :
    Measurable fun v => ∫ w, f (v + w) ∂ρ := by
  have : StronglyMeasurable (fun z : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin p) =>
      f (z.1 + z.2)) := (hf.comp (by fun_prop)).stronglyMeasurable
  exact (this.integral_prod_right' (ν := ρ)).measurable

lemma step_abs {B : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)} {κ : ℝ}
    {μ ν : Measure (EuclideanSpace ℝ (Fin p))} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MomMatch B κ μ) (hν : MomMatch B κ ν) (g : EuclideanSpace ℝ (Fin p) → ℝ)
    (hg : Measurable g) {R : ℝ} (hgR : ∀ v, |g v| ≤ R)
    {q : EuclideanSpace ℝ (Fin p) → ℝ} (hq : Continuous q) {W : ℝ} (hW : ∀ u, |q u| ≤ W)
    (N : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)) (x : EuclideanSpace ℝ (Fin p))
    (Rm : EuclideanSpace ℝ (Fin p) → ℝ) (hRμ : Integrable Rm μ) (hRν : Integrable Rm ν)
    (hrem : ∀ y, |g (x + y) - g x - Tform N q y| ≤ Rm y) :
    |∫ y, g (x + y) ∂μ - ∫ z, g (x + z) ∂ν| ≤ ∫ y, Rm y ∂μ + ∫ z, Rm z ∂ν := by
  have hgi : ∀ (m' : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure m'],
      Integrable (fun y => g (x + y)) m' := fun m' _ =>
    Integrable.of_bound ((hg.comp (by fun_prop)).aestronglyMeasurable) R
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hgR _)
  have key : ∀ (m' : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure m'], MomMatch B κ m' →
      ∫ y, (g (x + y) - g x - Tform N q y) ∂m' = ∫ y, g (x + y) ∂m' - g x - Tconst B N κ q := by
    intro m' _ hl
    have hT := integrable_Tform hl hq hW N
    have hA : Integrable (fun y => g (x + y) - g x) m' := (hgi m').sub (integrable_const _)
    rw [integral_sub hA hT, integral_sub (hgi m') (integrable_const _),
      integral_Tform hl hq hW N]
    simp
  have hbd : ∀ (m' : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure m'],
      Integrable Rm m' → |∫ y, (g (x + y) - g x - Tform N q y) ∂m'| ≤ ∫ y, Rm y ∂m' := by
    intro m' _ hr
    have := norm_integral_le_of_norm_le (f := fun y => g (x + y) - g x - Tform N q y) hr
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hrem y)
    simpa [Real.norm_eq_abs] using this
  have h1 := hbd μ hRμ
  have h2 := hbd ν hRν
  rw [key μ hμ] at h1
  rw [key ν hν] at h2
  have : ∫ y, g (x + y) ∂μ - ∫ z, g (x + z) ∂ν =
      (∫ y, g (x + y) ∂μ - g x - Tconst B N κ q) - (∫ y, g (x + y) ∂ν - g x - Tconst B N κ q) := by ring
  rw [this]
  calc _ ≤ |∫ y, g (x + y) ∂μ - g x - Tconst B N κ q| + |∫ y, g (x + y) ∂ν - g x - Tconst B N κ q| :=
        abs_sub _ _
    _ ≤ _ := add_le_add h1 h2

end Step

section Tele

variable {p : ℕ}

lemma integral_conv_conv {α m ρ : Measure (EuclideanSpace ℝ (Fin p))} [IsProbabilityMeasure α]
    [IsProbabilityMeasure m] [IsProbabilityMeasure ρ] {f : EuclideanSpace ℝ (Fin p) → ℝ}
    (hf : Measurable f) {R : ℝ} (hR : ∀ v, |f v| ≤ R) :
    ∫ z, f z ∂(α ∗ (m ∗ ρ)) = ∫ x, ∫ y, (∫ w, f (x + y + w) ∂ρ) ∂m ∂α := by
  have hint : ∀ (m' : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure m'] (x : EuclideanSpace ℝ (Fin p)),
      Integrable (fun v => f (x + v)) m' := fun m' _ x =>
    Integrable.of_bound (hf.comp (by fun_prop)).aestronglyMeasurable R
      (Filter.Eventually.of_forall fun v => by simpa [Real.norm_eq_abs] using hR _)
  have hI : Integrable f (α ∗ (m ∗ ρ)) :=
    Integrable.of_bound hf.aestronglyMeasurable R
      (Filter.Eventually.of_forall fun v => by simpa [Real.norm_eq_abs] using hR _)
  rw [integral_conv hI]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [integral_conv (hint (m ∗ ρ) x)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  beta_reduce
  simp only [add_assoc]

lemma tele_step (μ ν : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : Measurable f) {R : ℝ}
    (hR : ∀ v, |f v| ≤ R) (N k : ℕ) (hk : k < N) :
    ∫ z, f z ∂(cpow μ (k + 1) ∗ cpow ν (N - (k + 1))) - ∫ z, f z ∂(cpow μ k ∗ cpow ν (N - k)) =
      ∫ x, ((∫ y, (fun v => ∫ w, f (v + w) ∂(cpow ν (N - (k + 1)))) (x + y) ∂μ) -
        ∫ z, (fun v => ∫ w, f (v + w) ∂(cpow ν (N - (k + 1)))) (x + z) ∂ν) ∂(cpow μ k) := by
  set ρ := cpow ν (N - (k + 1)) with hρ
  set g : EuclideanSpace ℝ (Fin p) → ℝ := fun v => ∫ w, f (v + w) ∂ρ with hg
  have hgm : Measurable g := measurable_smooth hf ρ
  have hgR : ∀ v, |g v| ≤ R := fun v => by
    have := norm_integral_le_of_norm_le_const (μ := ρ) (f := fun w => f (v + w)) (C := R)
      (Filter.Eventually.of_forall fun w => by simpa [Real.norm_eq_abs] using hR _)
    simpa [g, Real.norm_eq_abs] using this
  have h1 : cpow μ (k + 1) ∗ cpow ν (N - (k + 1)) = cpow μ k ∗ (μ ∗ ρ) := by
    show (μ ∗ cpow μ k) ∗ ρ = _
    rw [Measure.conv_comm μ, Measure.conv_assoc]
  have h2 : cpow μ k ∗ cpow ν (N - k) = cpow μ k ∗ (ν ∗ ρ) := by
    have : N - k = (N - (k + 1)) + 1 := by omega
    rw [this]; rfl
  rw [h1, h2, integral_conv_conv hf hR, integral_conv_conv hf hR]
  have hmeas : ∀ (m' : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure m'],
      Integrable (fun x => ∫ y, g (x + y) ∂m') (cpow μ k) := fun m' _ =>
    Integrable.of_bound (measurable_smooth hgm m').aestronglyMeasurable R
      (Filter.Eventually.of_forall fun x => by
        have := norm_integral_le_of_norm_le_const (μ := m') (f := fun y => g (x + y)) (C := R)
          (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hgR _)
        simpa [Real.norm_eq_abs] using this)
  rw [← integral_sub (hmeas μ) (hmeas ν)]

/-- Telescoping bound for convolution powers. -/
lemma telescope_abs (μ ν : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : Measurable f) {R : ℝ}
    (hR : ∀ v, |f v| ≤ R) (N : ℕ) (C : ℕ → ℝ)
    (hC : ∀ k < N, ∀ x, |(∫ y, (fun v => ∫ w, f (v + w) ∂(cpow ν (N - (k + 1)))) (x + y) ∂μ) -
        ∫ z, (fun v => ∫ w, f (v + w) ∂(cpow ν (N - (k + 1)))) (x + z) ∂ν| ≤ C k) :
    |∫ z, f z ∂(cpow μ N) - ∫ z, f z ∂(cpow ν N)| ≤ ∑ k ∈ Finset.range N, C k := by
  set a : ℕ → ℝ := fun k => ∫ z, f z ∂(cpow μ k ∗ cpow ν (N - k)) with ha
  have haN : a N = ∫ z, f z ∂(cpow μ N) := by
    simp only [ha, Nat.sub_self, cpow, Measure.conv_dirac_zero]
  have ha0 : a 0 = ∫ z, f z ∂(cpow ν N) := by
    simp only [ha, Nat.sub_zero, cpow, Measure.dirac_zero_conv]
  have hsum : a N - a 0 = ∑ k ∈ Finset.range N, (a (k + 1) - a k) := (Finset.sum_range_sub a N).symm
  rw [← haN, ← ha0, hsum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  have hk' : k < N := Finset.mem_range.1 hk
  have := tele_step μ ν hf hR N k hk'
  simp only [ha]
  rw [this]
  have h := norm_integral_le_of_norm_le_const (μ := cpow μ k) (C := C k)
    (f := fun x => ((∫ y, (fun v => ∫ w, f (v + w) ∂(cpow ν (N - (k + 1)))) (x + y) ∂μ) -
        ∫ z, (fun v => ∫ w, f (v + w) ∂(cpow ν (N - (k + 1)))) (x + z) ∂ν))
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC k hk' x)
  simpa [Real.norm_eq_abs] using h

end Tele

section Moments2

variable {p : ℕ}

lemma integral_mul_le_sqrt {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f g : α → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hfm : AEStronglyMeasurable f μ)
    (hgm : AEStronglyMeasurable g μ) (hf : Integrable (fun x => f x ^ 2) μ)
    (hg : Integrable (fun x => g x ^ 2) μ) :
    ∫ x, f x * g x ∂μ ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have hfL : MemLp f (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by simp]
    exact (memLp_two_iff_integrable_sq hfm).2 hf
  have hgL : MemLp g (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by simp]
    exact (memLp_two_iff_integrable_sq hgm).2 hg
  have := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0) hfL hgL
  simp only [Real.rpow_two, one_div] at this
  simpa [Real.sqrt_eq_rpow, one_div] using this

variable {B binv : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)}

lemma B_adj_binv (hBs : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y)) (hbB : ∀ y, binv (B y) = y)
    (e : EuclideanSpace ℝ (Fin p)) : B (ContinuousLinearMap.adjoint binv e) = e := by
  apply ext_inner_right ℝ
  intro w
  rw [hBs, adj_inner, hbB, real_inner_comm]

lemma MomMatch.integral_norm_sq_binv {κ : ℝ} {μ : Measure (EuclideanSpace ℝ (Fin p))}
    [IsProbabilityMeasure μ] (h : MomMatch B κ μ)
    (hBs : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y)) (hbB : ∀ y, binv (B y) = y) :
    ∫ y, ‖binv y‖ ^ 2 ∂μ = κ * p := by
  rw [h.integral_norm_N_sq]
  simp_rw [B_adj_binv hBs hbB]
  simp

lemma integral_nuS_binv_sq (hbB : ∀ y, binv (B y) = y) (s : ℝ) :
    ∫ z, ‖binv z‖ ^ 2 ∂(nuS B s) = s ^ 2 * p := by
  rw [integral_nuS s (by fun_prop)]
  have e : ∀ u : EuclideanSpace ℝ (Fin p), ‖binv (s • B u)‖ ^ 2 = s ^ 2 * ‖u‖ ^ 2 := fun u => by
    rw [map_smul, hbB, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp_rw [e]
  rw [integral_const_mul, integral_norm_sq_gam]

lemma integral_nuS_binv_pow4_le (hbB : ∀ y, binv (B y) = y) (s : ℝ) :
    ∫ z, ‖binv z‖ ^ 4 ∂(nuS B s) ≤ 3 * s ^ 4 * (p : ℝ) ^ 2 := by
  rw [integral_nuS s (by fun_prop)]
  have e : ∀ u : EuclideanSpace ℝ (Fin p), ‖binv (s • B u)‖ ^ 4 = s ^ 4 * ‖u‖ ^ 4 := fun u => by
    rw [map_smul, hbB, norm_smul, mul_pow, Real.norm_eq_abs]
    rw [show |s| ^ 4 = s ^ 4 by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]]
  simp_rw [e]
  rw [integral_const_mul]
  have := integral_norm_pow4_gam_le (p := p)
  nlinarith [pow_nonneg (sq_nonneg s) 2]

lemma gaussian_term_lip (hbB : ∀ y, binv (B y) = y) (s : ℝ) :
    ∫ z, ‖z‖ * ‖binv z‖ ^ 2 ∂(nuS B s) ≤
      Real.sqrt (∫ z, ‖z‖ ^ 2 ∂(nuS B s)) * (Real.sqrt 3 * s ^ 2 * p) := by
  have h4 := HRS.EdgeAux.gaussian_integrable_pow (isCenteredGaussian_nuS (B := B) s) 4
  have hf := integrable_nuS_norm_sq (B := B) s
  have hg : Integrable (fun z : EuclideanSpace ℝ (Fin p) => (‖binv z‖ ^ 2) ^ 2) (nuS B s) := by
    refine (h4.const_mul (‖binv‖ ^ 4)).mono' (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (‖binv z‖ ^ 2) ^ 2 = ‖binv z‖ ^ 4 := by ring
      _ ≤ (‖binv‖ * ‖z‖) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) (binv.le_opNorm z) 4
      _ = ‖binv‖ ^ 4 * ‖z‖ ^ 4 := by ring
  have := integral_mul_le_sqrt (μ := nuS B s) (f := fun z => ‖z‖) (g := fun z => ‖binv z‖ ^ 2)
    (fun z => norm_nonneg _) (fun z => by positivity) (by fun_prop) (by fun_prop) hf hg
  refine this.trans ?_
  gcongr
  have hb := integral_nuS_binv_pow4_le hbB s
  have e : ∫ z, (‖binv z‖ ^ 2) ^ 2 ∂(nuS B s) = ∫ z, ‖binv z‖ ^ 4 ∂(nuS B s) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    ring
  rw [e]
  calc Real.sqrt (∫ z, ‖binv z‖ ^ 4 ∂(nuS B s)) ≤ Real.sqrt (3 * s ^ 4 * (p : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt hb
    _ = Real.sqrt 3 * s ^ 2 * p := by
        rw [show 3 * s ^ 4 * (p : ℝ) ^ 2 = 3 * (s ^ 2 * p) ^ 2 by ring, Real.sqrt_mul (by norm_num),
          Real.sqrt_sq (by positivity)]
        ring

lemma gaussian_term_C2 (hbB : ∀ y, binv (B y) = y) (s : ℝ) :
    ∫ z, ‖z‖ ^ 2 * ‖binv z‖ ∂(nuS B s) ≤
      Real.sqrt 3 * (∫ z, ‖z‖ ^ 2 ∂(nuS B s)) * (|s| * Real.sqrt p) := by
  have h4 := HRS.EdgeAux.gaussian_integrable_pow (isCenteredGaussian_nuS (B := B) s) 4
  have h2 := integrable_nuS_norm_sq (B := B) s
  have hf : Integrable (fun z : EuclideanSpace ℝ (Fin p) => (‖z‖ ^ 2) ^ 2) (nuS B s) :=
    h4.congr (Filter.Eventually.of_forall fun z => by ring)
  have hg : Integrable (fun z : EuclideanSpace ℝ (Fin p) => ‖binv z‖ ^ 2) (nuS B s) := by
    refine (h2.const_mul (‖binv‖ ^ 2)).mono' (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖binv z‖ ^ 2 ≤ (‖binv‖ * ‖z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (binv.le_opNorm z) 2
      _ = ‖binv‖ ^ 2 * ‖z‖ ^ 2 := by ring
  have := integral_mul_le_sqrt (μ := nuS B s) (f := fun z => ‖z‖ ^ 2) (g := fun z => ‖binv z‖)
    (fun z => by positivity) (fun z => norm_nonneg _) (by fun_prop) (by fun_prop) hf hg
  refine this.trans ?_
  have hm4 := HRS.EdgeAux.gaussian_fourth_le (isCenteredGaussian_nuS (B := B) s)
  have e1 : ∫ z, (‖z‖ ^ 2) ^ 2 ∂(nuS B s) = ∫ z, ‖z‖ ^ 4 ∂(nuS B s) :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
  have e2 : ∫ z, ‖binv z‖ ^ 2 ∂(nuS B s) = s ^ 2 * p := integral_nuS_binv_sq hbB s
  have hm0 : 0 ≤ ∫ z, ‖z‖ ^ 2 ∂(nuS B s) := integral_nonneg fun z => by positivity
  rw [e1, e2]
  calc Real.sqrt (∫ z, ‖z‖ ^ 4 ∂(nuS B s)) * Real.sqrt (s ^ 2 * p)
      ≤ Real.sqrt (3 * (∫ z, ‖z‖ ^ 2 ∂(nuS B s)) ^ 2) * Real.sqrt (s ^ 2 * p) := by
        gcongr
    _ = Real.sqrt 3 * (∫ z, ‖z‖ ^ 2 ∂(nuS B s)) * (|s| * Real.sqrt p) := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hm0, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

end Moments2

section MuTerms

variable {p : ℕ} {B binv : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)} {κ : ℝ}
  {μ : Measure (EuclideanSpace ℝ (Fin p))} [IsProbabilityMeasure μ]

lemma MomMatch.integrable_norm_binv_sq (h : MomMatch B κ μ)
    (binv : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)) :
    Integrable (fun y => ‖binv y‖ ^ 2) μ := by
  refine (h.int2.const_mul (‖binv‖ ^ 2)).mono' (by fun_prop) (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖binv y‖ ^ 2 ≤ (‖binv‖ * ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (binv.le_opNorm y) 2
    _ = ‖binv‖ ^ 2 * ‖y‖ ^ 2 := by ring

lemma MomMatch.integrable_norm_binv (h : MomMatch B κ μ)
    (binv : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)) :
    Integrable (fun y => ‖binv y‖) μ := by
  refine (h.integrable_norm.const_mul ‖binv‖).mono' (by fun_prop) (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact binv.le_opNorm y

lemma mu_term_lip (h : MomMatch B κ μ) (hBs : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (hbB : ∀ y, binv (B y) = y) {b : ℝ} (hb0 : 0 ≤ b) (hb : ∀ᵐ y ∂μ, ‖y‖ ≤ b) :
    ∫ y, ‖y‖ * ‖binv y‖ ^ 2 ∂μ ≤ b * (κ * p) := by
  have hi := h.integrable_norm_binv_sq binv
  rw [← h.integral_norm_sq_binv hBs hbB, ← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => by positivity)
    (hi.const_mul b) (hb.mono fun y hy => ?_)
  exact mul_le_mul_of_nonneg_right hy (by positivity)

lemma mu_term_C2 (h : MomMatch B κ μ) (hBs : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    (hbB : ∀ y, binv (B y) = y) {b : ℝ} (hb0 : 0 ≤ b) (hb : ∀ᵐ y ∂μ, ‖y‖ ≤ b) (hκ : 0 ≤ κ) :
    ∫ y, ‖y‖ ^ 2 * ‖binv y‖ ∂μ ≤ b ^ 2 * Real.sqrt (κ * p) := by
  have hi1 := h.integrable_norm_binv binv
  have hi2 := h.integrable_norm_binv_sq binv
  have hmem : MemLp (fun y => ‖binv y‖) 2 μ :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 hi2
  have hcs := sq_integral_le μ hmem
  rw [h.integral_norm_sq_binv hBs hbB] at hcs
  have h1 : ∫ y, ‖binv y‖ ∂μ ≤ Real.sqrt (κ * p) := by
    refine Real.le_sqrt_of_sq_le ?_
    simpa using hcs
  calc ∫ y, ‖y‖ ^ 2 * ‖binv y‖ ∂μ ≤ ∫ y, b ^ 2 * ‖binv y‖ ∂μ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => by positivity)
          (hi1.const_mul _) (hb.mono fun y hy => ?_)
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hy 2) (norm_nonneg _)
    _ = b ^ 2 * ∫ y, ‖binv y‖ ∂μ := integral_const_mul _ _
    _ ≤ b ^ 2 * Real.sqrt (κ * p) := mul_le_mul_of_nonneg_left h1 (by positivity)

lemma MomMatch.integral_norm_sq_eq {κ : ℝ} {B : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)}
    {μ₁ μ₂ : Measure (EuclideanSpace ℝ (Fin p))} [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h₁ : MomMatch B κ μ₁) (h₂ : MomMatch B κ μ₂) :
    ∫ y, ‖y‖ ^ 2 ∂μ₁ = ∫ y, ‖y‖ ^ 2 ∂μ₂ := by
  have := h₁.integral_norm_N_sq (ContinuousLinearMap.id ℝ _)
  have := h₂.integral_norm_N_sq (ContinuousLinearMap.id ℝ _)
  simp only [ContinuousLinearMap.id_apply] at *
  linarith

end MuTerms

section StepBounds

variable {p : ℕ} {B binv : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)}

lemma smooth_eq_cpow (hBs : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y)) {κ : ℝ} (hκ : 0 < κ)
    {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : Continuous f) (m : ℕ) :
    (fun v => ∫ w, f (v + w) ∂(cpow (nuS B (Real.sqrt κ)) m)) = smoothF B (m * κ) f := by
  funext v
  rw [cpow_nuS hBs, integral_nuS _ (by fun_prop)]
  unfold smoothF
  rw [Real.sqrt_mul (Nat.cast_nonneg m)]

lemma norm_Nmap_sq {t : ℝ} (ht : 0 < t) (y : EuclideanSpace ℝ (Fin p)) :
    ‖Nmap binv t y‖ ^ 2 = ‖binv y‖ ^ 2 / t := by
  simp only [Nmap, ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs]
  rw [mul_pow, abs_inv, abs_of_pos (Real.sqrt_pos.2 ht), inv_pow, Real.sq_sqrt ht.le]
  ring

lemma norm_Nmap {t : ℝ} (ht : 0 < t) (y : EuclideanSpace ℝ (Fin p)) :
    ‖Nmap binv t y‖ = ‖binv y‖ / Real.sqrt t := by
  simp only [Nmap, ContinuousLinearMap.smul_apply, norm_smul, Real.norm_eq_abs]
  rw [abs_inv, abs_of_pos (Real.sqrt_pos.2 ht)]
  ring

lemma step_lip (hBs : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y)) (hBb : ∀ y, B (binv y) = y)
    (hbB : ∀ y, binv (B y) = y) {κ : ℝ} (hκ : 0 < κ)
    {μ : Measure (EuclideanSpace ℝ (Fin p))} [IsProbabilityMeasure μ] (hμ : MomMatch B κ μ)
    {b : ℝ} (hb0 : 0 ≤ b) (hb : ∀ᵐ y ∂μ, ‖y‖ ≤ b)
    {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : LipschitzWith 1 f) {R : ℝ} (hR : ∀ z, |f z| ≤ R)
    {m : ℕ} (hm : 1 ≤ m) (x : EuclideanSpace ℝ (Fin p)) :
    |∫ y, (fun v => ∫ w, f (v + w) ∂(cpow (nuS B (Real.sqrt κ)) m)) (x + y) ∂μ -
        ∫ z, (fun v => ∫ w, f (v + w) ∂(cpow (nuS B (Real.sqrt κ)) m)) (x + z) ∂(nuS B (Real.sqrt κ))| ≤
      b * p / m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  set s := Real.sqrt κ with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hκ
  have hs2 : s ^ 2 = κ := Real.sq_sqrt hκ.le
  set ν := nuS B s with hν
  have hνm : MomMatch B κ ν := by
    have := nuS_momMatch (B := B) hBs s
    rwa [hs2] at this
  set t : ℝ := m * κ with ht
  have htpos : 0 < t := by positivity
  rw [smooth_eq_cpow hBs hκ hf.continuous m]
  set g := smoothF B t f with hg
  have hgm : Measurable g := by
    have := measurable_smooth hf.continuous.measurable (cpow ν m)
    have e : g = fun v => ∫ w, f (v + w) ∂(cpow ν m) := (smooth_eq_cpow hBs hκ hf.continuous m).symm
    rw [e]; exact this
  have hgR : ∀ v, |g v| ≤ R := fun v => by
    have := norm_integral_le_of_norm_le_const (μ := gam p) (f := fun u => f (v + Real.sqrt t • B u))
      (C := R) (Filter.Eventually.of_forall fun u => by simpa [Real.norm_eq_abs] using hR _)
    simpa [hg, smoothF, Real.norm_eq_abs] using this
  set q : EuclideanSpace ℝ (Fin p) → ℝ := fun u => f (x + Real.sqrt t • B u) with hq
  have hqc : Continuous q := hf.continuous.comp (by fun_prop)
  have hqW : ∀ u, |q u| ≤ R := fun u => hR _
  set c : ℝ := Real.sqrt 2 / (6 * t) with hc
  have hc0 : 0 ≤ c := by positivity
  set Rm : EuclideanSpace ℝ (Fin p) → ℝ := fun y => c * (‖y‖ * ‖binv y‖ ^ 2) with hRm
  have hRμ : Integrable Rm μ := by
    have hi := hμ.integrable_norm_binv_sq binv
    refine (hi.const_mul (c * b)).mono' (by fun_prop) (hb.mono fun y hy => ?_)
    simp only [hRm]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc c * (‖y‖ * ‖binv y‖ ^ 2) ≤ c * (b * ‖binv y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hy (by positivity)) hc0
      _ = c * b * ‖binv y‖ ^ 2 := by ring
  have hRν : Integrable Rm ν := by
    have h3 := HRS.EdgeAux.gaussian_integrable_pow (isCenteredGaussian_nuS (B := B) s) 3
    refine (h3.const_mul (c * ‖binv‖ ^ 2)).mono' (by fun_prop) (Filter.Eventually.of_forall fun y => ?_)
    simp only [hRm]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc c * (‖y‖ * ‖binv y‖ ^ 2) ≤ c * (‖y‖ * (‖binv‖ * ‖y‖) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (binv.le_opNorm y) 2) (norm_nonneg _)) hc0
      _ = c * ‖binv‖ ^ 2 * ‖y‖ ^ 3 := by ring
  have hrem : ∀ y, |g (x + y) - g x - Tform (Nmap binv t) q y| ≤ Rm y := fun y => by
    have := smooth_taylor_lip hBb htpos hf hR x y
    refine this.trans (le_of_eq ?_)
    rw [norm_Nmap_sq htpos]
    simp only [hRm, hc]
    field_simp
  have key := step_abs hμ hνm g hgm hgR hqc hqW (Nmap binv t) x Rm hRμ hRν hrem
  refine key.trans ?_
  -- bound the two integrals
  have e1 : ∫ y, Rm y ∂μ = c * ∫ y, ‖y‖ * ‖binv y‖ ^ 2 ∂μ := integral_const_mul _ _
  have e2 : ∫ y, Rm y ∂ν = c * ∫ y, ‖y‖ * ‖binv y‖ ^ 2 ∂ν := integral_const_mul _ _
  rw [e1, e2, ← mul_add]
  have hA := mu_term_lip hμ hBs hbB hb0 hb (binv := binv)
  have hm2 : ∫ y, ‖y‖ ^ 2 ∂ν = ∫ y, ‖y‖ ^ 2 ∂μ := hνm.integral_norm_sq_eq hμ
  have hm2b : ∫ y, ‖y‖ ^ 2 ∂μ ≤ b ^ 2 := by
    have := integral_mono_ae (μ := μ) (f := fun y => ‖y‖ ^ 2) (g := fun _ => b ^ 2) hμ.int2
      (integrable_const _) (hb.mono fun y hy => pow_le_pow_left₀ (norm_nonneg _) hy 2)
    simpa using this
  have hB' := gaussian_term_lip (B := B) (binv := binv) hbB s
  have hsq : Real.sqrt (∫ z, ‖z‖ ^ 2 ∂ν) ≤ b := by
    rw [hm2]
    exact Real.sqrt_le_iff.2 ⟨hb0, hm2b⟩
  have hB'' : ∫ z, ‖z‖ * ‖binv z‖ ^ 2 ∂ν ≤ b * (Real.sqrt 3 * κ * p) := by
    refine hB'.trans ?_
    rw [hs2]
    exact mul_le_mul hsq le_rfl (by positivity) hb0
  have hsum : ∫ y, ‖y‖ * ‖binv y‖ ^ 2 ∂μ + ∫ y, ‖y‖ * ‖binv y‖ ^ 2 ∂ν ≤
      b * κ * p * (1 + Real.sqrt 3) := by nlinarith [hA, hB'']
  have h2 : Real.sqrt 2 ≤ 3 / 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have h3 : Real.sqrt 3 ≤ 7 / 4 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have h2' := Real.sqrt_nonneg 2
  have h3' := Real.sqrt_nonneg 3
  have hbk : 0 ≤ b * κ * p := by positivity
  calc c * (∫ y, ‖y‖ * ‖binv y‖ ^ 2 ∂μ + ∫ y, ‖y‖ * ‖binv y‖ ^ 2 ∂ν)
      ≤ c * (b * κ * p * (1 + Real.sqrt 3)) := mul_le_mul_of_nonneg_left hsum hc0
    _ = Real.sqrt 2 * (1 + Real.sqrt 3) / 6 * (b * p / m) := by
        simp only [hc, ht]
        field_simp
    _ ≤ 1 * (b * p / m) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        nlinarith
    _ = b * p / m := one_mul _

lemma step_C2 (hBs : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y)) (hBb : ∀ y, B (binv y) = y)
    (hbB : ∀ y, binv (B y) = y) {κ : ℝ} (hκ : 0 < κ)
    {μ : Measure (EuclideanSpace ℝ (Fin p))} [IsProbabilityMeasure μ] (hμ : MomMatch B κ μ)
    {b : ℝ} (hb0 : 0 ≤ b) (hb : ∀ᵐ y ∂μ, ‖y‖ ≤ b)
    {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : ContDiff ℝ 2 f) {M0 M1 M2 : ℝ}
    (h0 : ∀ z, |f z| ≤ M0) (h1 : ∀ z, ‖fderiv ℝ f z‖ ≤ M1)
    (h2 : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ M2)
    {m : ℕ} (hm : 1 ≤ m) (x : EuclideanSpace ℝ (Fin p)) :
    |∫ y, (fun v => ∫ w, f (v + w) ∂(cpow (nuS B (Real.sqrt κ)) m)) (x + y) ∂μ -
        ∫ z, (fun v => ∫ w, f (v + w) ∂(cpow (nuS B (Real.sqrt κ)) m)) (x + z) ∂(nuS B (Real.sqrt κ))| ≤
      M2 * b ^ 2 * Real.sqrt p / Real.sqrt m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hM2 : 0 ≤ M2 := (norm_nonneg (fderiv ℝ (fderiv ℝ f) 0)).trans (h2 0)
  set s := Real.sqrt κ with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hκ
  have hs2 : s ^ 2 = κ := Real.sq_sqrt hκ.le
  set ν := nuS B s with hν
  have hνm : MomMatch B κ ν := by
    have := nuS_momMatch (B := B) hBs s
    rwa [hs2] at this
  set t : ℝ := m * κ with ht
  have htpos : 0 < t := by positivity
  have hfc : Continuous f := hf.continuous
  rw [smooth_eq_cpow hBs hκ hfc m]
  set g := smoothF B t f with hg
  have hgm : Measurable g := by
    have := measurable_smooth hfc.measurable (cpow ν m)
    have e : g = fun v => ∫ w, f (v + w) ∂(cpow ν m) := (smooth_eq_cpow hBs hκ hfc m).symm
    rw [e]; exact this
  have hgR : ∀ v, |g v| ≤ M0 := fun v => by
    have := norm_integral_le_of_norm_le_const (μ := gam p) (f := fun u => f (v + Real.sqrt t • B u))
      (C := M0) (Filter.Eventually.of_forall fun u => by simpa [Real.norm_eq_abs] using h0 _)
    simpa [hg, smoothF, Real.norm_eq_abs] using this
  set q : EuclideanSpace ℝ (Fin p) → ℝ := fun u => f (x + Real.sqrt t • B u) with hq
  have hqc : Continuous q := hfc.comp (by fun_prop)
  have hqW : ∀ u, |q u| ≤ M0 := fun u => h0 _
  set c : ℝ := M2 / (3 * Real.sqrt t) with hc
  have hsqt : 0 < Real.sqrt t := Real.sqrt_pos.2 htpos
  have hc0 : 0 ≤ c := by positivity
  set Rm : EuclideanSpace ℝ (Fin p) → ℝ := fun y => c * (‖y‖ ^ 2 * ‖binv y‖) with hRm
  have hRμ : Integrable Rm μ := by
    have hi := hμ.integrable_norm_binv binv
    refine (hi.const_mul (c * b ^ 2)).mono' (by fun_prop) (hb.mono fun y hy => ?_)
    simp only [hRm]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc c * (‖y‖ ^ 2 * ‖binv y‖) ≤ c * (b ^ 2 * ‖binv y‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (norm_nonneg _) hy 2) (norm_nonneg _)) hc0
      _ = c * b ^ 2 * ‖binv y‖ := by ring
  have hRν : Integrable Rm ν := by
    have h3 := HRS.EdgeAux.gaussian_integrable_pow (isCenteredGaussian_nuS (B := B) s) 3
    refine (h3.const_mul (c * ‖binv‖)).mono' (by fun_prop) (Filter.Eventually.of_forall fun y => ?_)
    simp only [hRm]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc c * (‖y‖ ^ 2 * ‖binv y‖) ≤ c * (‖y‖ ^ 2 * (‖binv‖ * ‖y‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (binv.le_opNorm y) (by positivity)) hc0
      _ = c * ‖binv‖ * ‖y‖ ^ 3 := by ring
  have hrem : ∀ y, |g (x + y) - g x - Tform (Nmap binv t) q y| ≤ Rm y := fun y => by
    have := smooth_taylor_C2 hBb htpos hf h0 h1 h2 x y
    refine this.trans (le_of_eq ?_)
    rw [norm_Nmap htpos]
    simp only [hRm, hc]
    field_simp
    ring
  have key := step_abs hμ hνm g hgm hgR hqc hqW (Nmap binv t) x Rm hRμ hRν hrem
  refine key.trans ?_
  have e1 : ∫ y, Rm y ∂μ = c * ∫ y, ‖y‖ ^ 2 * ‖binv y‖ ∂μ := integral_const_mul _ _
  have e2 : ∫ y, Rm y ∂ν = c * ∫ y, ‖y‖ ^ 2 * ‖binv y‖ ∂ν := integral_const_mul _ _
  rw [e1, e2, ← mul_add]
  have hA := mu_term_C2 hμ hBs hbB hb0 hb hκ.le (binv := binv)
  have hm2 : ∫ y, ‖y‖ ^ 2 ∂ν = ∫ y, ‖y‖ ^ 2 ∂μ := hνm.integral_norm_sq_eq hμ
  have hm2b : ∫ y, ‖y‖ ^ 2 ∂μ ≤ b ^ 2 := by
    have := integral_mono_ae (μ := μ) (f := fun y => ‖y‖ ^ 2) (g := fun _ => b ^ 2) hμ.int2
      (integrable_const _) (hb.mono fun y hy => pow_le_pow_left₀ (norm_nonneg _) hy 2)
    simpa using this
  have hB' := gaussian_term_C2 (B := B) (binv := binv) hbB s
  have hB'' : ∫ z, ‖z‖ ^ 2 * ‖binv z‖ ∂ν ≤ Real.sqrt 3 * b ^ 2 * (s * Real.sqrt p) := by
    refine hB'.trans ?_
    rw [hm2, abs_of_pos hs0]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hm2b (Real.sqrt_nonneg _)) le_rfl (by positivity)
      (by positivity)
  have hκp : Real.sqrt (κ * p) = s * Real.sqrt p := by
    rw [Real.sqrt_mul hκ.le]
  rw [hκp] at hA
  have hsum : ∫ y, ‖y‖ ^ 2 * ‖binv y‖ ∂μ + ∫ y, ‖y‖ ^ 2 * ‖binv y‖ ∂ν ≤
      b ^ 2 * (s * Real.sqrt p) * (1 + Real.sqrt 3) := by nlinarith [hA, hB'']
  have h3 : Real.sqrt 3 ≤ 7 / 4 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have h3' := Real.sqrt_nonneg 3
  have hsqm : Real.sqrt t = Real.sqrt m * s := by
    rw [ht, Real.sqrt_mul (Nat.cast_nonneg m)]
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hmpos
  calc c * (∫ y, ‖y‖ ^ 2 * ‖binv y‖ ∂μ + ∫ y, ‖y‖ ^ 2 * ‖binv y‖ ∂ν)
      ≤ c * (b ^ 2 * (s * Real.sqrt p) * (1 + Real.sqrt 3)) := mul_le_mul_of_nonneg_left hsum hc0
    _ = (1 + Real.sqrt 3) / 3 * (M2 * b ^ 2 * Real.sqrt p / Real.sqrt m) := by
        simp only [hc, hsqm]
        field_simp
    _ ≤ 1 * (M2 * b ^ 2 * Real.sqrt p / Real.sqrt m) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        nlinarith
    _ = _ := one_mul _

lemma MomMatch.integrable_clm {κ : ℝ} {μ : Measure (EuclideanSpace ℝ (Fin p))}
    [IsProbabilityMeasure μ] (h : MomMatch B κ μ) (L : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ) :
    Integrable (fun y => L y) μ := by
  have := h.integrable_inner ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin p))).symm L)
  refine this.congr (Filter.Eventually.of_forall fun y => ?_)
  simp [InnerProductSpace.toDual_symm_apply]

lemma MomMatch.integral_clm {κ : ℝ} {μ : Measure (EuclideanSpace ℝ (Fin p))}
    [IsProbabilityMeasure μ] (h : MomMatch B κ μ) (L : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ) :
    ∫ y, L y ∂μ = 0 := by
  have := h.mean ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin p))).symm L)
  simpa [InnerProductSpace.toDual_symm_apply] using this

lemma integral_norm_le_sqrt {κ : ℝ} {μ : Measure (EuclideanSpace ℝ (Fin p))}
    [IsProbabilityMeasure μ] (h : MomMatch B κ μ) :
    ∫ y, ‖y‖ ∂μ ≤ Real.sqrt (∫ y, ‖y‖ ^ 2 ∂μ) := by
  have hmem : MemLp (fun y : EuclideanSpace ℝ (Fin p) => ‖y‖) 2 μ :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 h.int2
  exact Real.le_sqrt_of_sq_le (sq_integral_le μ hmem)

lemma lip_dev {κ : ℝ} {μ : Measure (EuclideanSpace ℝ (Fin p))} [IsProbabilityMeasure μ]
    (h : MomMatch B κ μ) {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : LipschitzWith 1 f) {R : ℝ}
    (hR : ∀ z, |f z| ≤ R) (x : EuclideanSpace ℝ (Fin p)) :
    |∫ y, f (x + y) ∂μ - f x| ≤ ∫ y, ‖y‖ ∂μ := by
  have hfm : Measurable f := hf.continuous.measurable
  have hi : Integrable (fun y => f (x + y)) μ :=
    Integrable.of_bound ((hfm.comp (by fun_prop)).aestronglyMeasurable) R
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hR _)
  have h1 : ∫ y, f (x + y) ∂μ - f x = ∫ y, (f (x + y) - f x) ∂μ := by
    rw [integral_sub hi (integrable_const _)]; simp
  rw [h1]
  have := norm_integral_le_of_norm_le (f := fun y => f (x + y) - f x) h.integrable_norm
    (Filter.Eventually.of_forall fun y => by
      have := hf.dist_le_mul (x + y) x
      rw [Real.dist_eq, dist_eq_norm] at this
      simpa [Real.norm_eq_abs] using this)
  simpa [Real.norm_eq_abs] using this

lemma final_lip {κ : ℝ} (hκ : 0 < κ) (hBs : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    {μ : Measure (EuclideanSpace ℝ (Fin p))} [IsProbabilityMeasure μ] (hμ : MomMatch B κ μ)
    {b : ℝ} (hb0 : 0 ≤ b) (hb : ∀ᵐ y ∂μ, ‖y‖ ≤ b)
    {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : LipschitzWith 1 f) {R : ℝ} (hR : ∀ z, |f z| ≤ R)
    (x : EuclideanSpace ℝ (Fin p)) :
    |∫ y, (fun v => ∫ w, f (v + w) ∂(cpow (nuS B (Real.sqrt κ)) 0)) (x + y) ∂μ -
        ∫ z, (fun v => ∫ w, f (v + w) ∂(cpow (nuS B (Real.sqrt κ)) 0)) (x + z) ∂(nuS B (Real.sqrt κ))| ≤
      2 * b := by
  set s := Real.sqrt κ with hs
  have hs2 : s ^ 2 = κ := Real.sq_sqrt hκ.le
  set ν := nuS B s with hν
  have hνm : MomMatch B κ ν := by
    have := nuS_momMatch (B := B) hBs s
    rwa [hs2] at this
  have e : (fun v => ∫ w, f (v + w) ∂(cpow ν 0)) = f := by
    funext v
    simp only [cpow]
    have hm : StronglyMeasurable (fun w : EuclideanSpace ℝ (Fin p) => f (v + w)) :=
      (hf.continuous.comp (continuous_const.add continuous_id)).stronglyMeasurable
    rw [integral_dirac' (fun w => f (v + w)) 0 hm]
    simp
  rw [e]
  have hmu := lip_dev hμ hf hR x
  have hnu := lip_dev hνm hf hR x
  have h1 : ∫ y, ‖y‖ ∂μ ≤ b := by
    have := integral_mono_ae (μ := μ) (f := fun y => ‖y‖) (g := fun _ => b) hμ.integrable_norm
      (integrable_const _) hb
    simpa using this
  have hm2 : ∫ y, ‖y‖ ^ 2 ∂ν = ∫ y, ‖y‖ ^ 2 ∂μ := hνm.integral_norm_sq_eq hμ
  have hm2b : ∫ y, ‖y‖ ^ 2 ∂μ ≤ b ^ 2 := by
    have := integral_mono_ae (μ := μ) (f := fun y => ‖y‖ ^ 2) (g := fun _ => b ^ 2) hμ.int2
      (integrable_const _) (hb.mono fun y hy => pow_le_pow_left₀ (norm_nonneg _) hy 2)
    simpa using this
  have h2 : ∫ y, ‖y‖ ∂ν ≤ b := by
    refine (integral_norm_le_sqrt hνm).trans ?_
    rw [hm2]
    exact Real.sqrt_le_iff.2 ⟨hb0, hm2b⟩
  calc |∫ y, f (x + y) ∂μ - ∫ z, f (x + z) ∂ν|
      = |(∫ y, f (x + y) ∂μ - f x) - (∫ z, f (x + z) ∂ν - f x)| := by ring_nf
    _ ≤ |∫ y, f (x + y) ∂μ - f x| + |∫ z, f (x + z) ∂ν - f x| := abs_sub _ _
    _ ≤ b + b := add_le_add (hmu.trans h1) (hnu.trans h2)
    _ = 2 * b := by ring

lemma C2_dev {κ : ℝ} {μ : Measure (EuclideanSpace ℝ (Fin p))} [IsProbabilityMeasure μ]
    (h : MomMatch B κ μ) {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : ContDiff ℝ 2 f) {M0 M2 : ℝ}
    (h0 : ∀ z, |f z| ≤ M0) (hM : ∀ z, ‖iteratedFDeriv ℝ 2 f z‖ ≤ M2) (x : EuclideanSpace ℝ (Fin p)) :
    |∫ y, f (x + y) ∂μ - f x| ≤ M2 / 2 * ∫ y, ‖y‖ ^ 2 ∂μ := by
  have hfm : Measurable f := hf.continuous.measurable
  have hi : Integrable (fun y => f (x + y)) μ :=
    Integrable.of_bound ((hfm.comp (by fun_prop)).aestronglyMeasurable) M0
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using h0 _)
  have hL := h.integrable_clm (fderiv ℝ f x)
  have h1 : ∫ y, f (x + y) ∂μ - f x = ∫ y, (f (x + y) - f x - fderiv ℝ f x y) ∂μ := by
    have hA : Integrable (fun y => f (x + y) - f x) μ := hi.sub (integrable_const _)
    rw [integral_sub hA hL, integral_sub hi (integrable_const _), h.integral_clm]
    simp
  rw [h1]
  have := norm_integral_le_of_norm_le (f := fun y => f (x + y) - f x - fderiv ℝ f x y)
    (h.int2.const_mul (M2 / 2))
    (Filter.Eventually.of_forall fun y => by
      have := taylor_two_bound hf hM x y
      simpa [Real.norm_eq_abs] using this)
  rw [integral_const_mul] at this
  simpa [Real.norm_eq_abs] using this

lemma final_C2 {κ : ℝ} (hκ : 0 < κ) (hBs : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y))
    {μ : Measure (EuclideanSpace ℝ (Fin p))} [IsProbabilityMeasure μ] (hμ : MomMatch B κ μ)
    {b : ℝ} (hb0 : 0 ≤ b) (hb : ∀ᵐ y ∂μ, ‖y‖ ≤ b)
    {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : ContDiff ℝ 2 f) {M0 M2 : ℝ}
    (h0 : ∀ z, |f z| ≤ M0) (hM : ∀ z, ‖iteratedFDeriv ℝ 2 f z‖ ≤ M2)
    (x : EuclideanSpace ℝ (Fin p)) :
    |∫ y, (fun v => ∫ w, f (v + w) ∂(cpow (nuS B (Real.sqrt κ)) 0)) (x + y) ∂μ -
        ∫ z, (fun v => ∫ w, f (v + w) ∂(cpow (nuS B (Real.sqrt κ)) 0)) (x + z) ∂(nuS B (Real.sqrt κ))| ≤
      M2 * b ^ 2 := by
  set s := Real.sqrt κ with hs
  have hs2 : s ^ 2 = κ := Real.sq_sqrt hκ.le
  set ν := nuS B s with hν
  have hνm : MomMatch B κ ν := by
    have := nuS_momMatch (B := B) hBs s
    rwa [hs2] at this
  have hfc : Continuous f := hf.continuous
  have e : (fun v => ∫ w, f (v + w) ∂(cpow ν 0)) = f := by
    funext v
    simp only [cpow]
    have hm : StronglyMeasurable (fun w : EuclideanSpace ℝ (Fin p) => f (v + w)) :=
      (hfc.comp (continuous_const.add continuous_id)).stronglyMeasurable
    rw [integral_dirac' (fun w => f (v + w)) 0 hm]
    simp
  rw [e]
  have hmu := C2_dev hμ hf h0 hM x
  have hnu := C2_dev hνm hf h0 hM x
  have hm2 : ∫ y, ‖y‖ ^ 2 ∂ν = ∫ y, ‖y‖ ^ 2 ∂μ := hνm.integral_norm_sq_eq hμ
  have hm2b : ∫ y, ‖y‖ ^ 2 ∂μ ≤ b ^ 2 := by
    have := integral_mono_ae (μ := μ) (f := fun y => ‖y‖ ^ 2) (g := fun _ => b ^ 2) hμ.int2
      (integrable_const _) (hb.mono fun y hy => pow_le_pow_left₀ (norm_nonneg _) hy 2)
    simpa using this
  have hM2 : 0 ≤ M2 := (norm_nonneg (iteratedFDeriv ℝ 2 f 0)).trans (hM 0)
  rw [hm2] at hnu
  calc |∫ y, f (x + y) ∂μ - ∫ z, f (x + z) ∂ν|
      = |(∫ y, f (x + y) ∂μ - f x) - (∫ z, f (x + z) ∂ν - f x)| := by ring_nf
    _ ≤ |∫ y, f (x + y) ∂μ - f x| + |∫ z, f (x + z) ∂ν - f x| := abs_sub _ _
    _ ≤ M2 / 2 * ∫ y, ‖y‖ ^ 2 ∂μ + M2 / 2 * ∫ y, ‖y‖ ^ 2 ∂μ := add_le_add hmu hnu
    _ ≤ M2 / 2 * b ^ 2 + M2 / 2 * b ^ 2 := by gcongr
    _ = M2 * b ^ 2 := by ring

end StepBounds

section Sums

lemma sum_inv_le_log (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Finset.range N, (1 : ℝ) / ((N - (k + 1) : ℕ) : ℝ) ≤ Real.log (Real.exp 1 * N) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hr := Finset.sum_range_reflect (fun j : ℕ => (1 : ℝ) / (j : ℝ)) (n + 1)
  have e : ∀ k ∈ Finset.range (n + 1), (1 : ℝ) / ((n + 1 - (k + 1) : ℕ) : ℝ) =
      (fun j : ℕ => (1 : ℝ) / (j : ℝ)) (n + 1 - 1 - k) := fun k _ => by
    simp only [Nat.sub_sub, Nat.add_sub_cancel_left]
    congr 3; omega
  rw [Finset.sum_congr rfl e, hr, Finset.sum_range_succ']
  simp only [Nat.cast_zero, div_zero, add_zero]
  have hh := harmonic_le_one_add_log n
  have e2 : ∑ j ∈ Finset.range n, (1 : ℝ) / ((j + 1 : ℕ) : ℝ) = (harmonic n : ℝ) := by
    simp [harmonic]
  rw [e2]
  have hlog : Real.log (Real.exp 1 * ((n + 1 : ℕ) : ℝ)) = 1 + Real.log ((n + 1 : ℕ) : ℝ) := by
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
  rw [hlog]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp at hh ⊢
  · have : Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast hn) (by push_cast; linarith)
    linarith

lemma sum_inv_sqrt_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Finset.range N, (1 : ℝ) / Real.sqrt ((N - (k + 1) : ℕ) : ℝ) ≤ 2 * Real.sqrt N := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hr := Finset.sum_range_reflect (fun j : ℕ => (1 : ℝ) / Real.sqrt (j : ℝ)) (n + 1)
  have e : ∀ k ∈ Finset.range (n + 1), (1 : ℝ) / Real.sqrt ((n + 1 - (k + 1) : ℕ) : ℝ) =
      (fun j : ℕ => (1 : ℝ) / Real.sqrt (j : ℝ)) (n + 1 - 1 - k) := fun k _ => by
    simp only [Nat.sub_sub, Nat.add_sub_cancel_left]
    congr 4; omega
  rw [Finset.sum_congr rfl e, hr, Finset.sum_range_succ']
  simp only [Nat.cast_zero, Real.sqrt_zero, div_zero, add_zero]
  have key : ∀ m : ℕ, ∑ j ∈ Finset.range m, (1 : ℝ) / Real.sqrt ((j + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have h1 : (1 : ℝ) / Real.sqrt ((m + 1 : ℕ) : ℝ) ≤ 2 * (Real.sqrt ((m + 1 : ℕ) : ℝ) - Real.sqrt m) := by
        have hpos : 0 < Real.sqrt ((m + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
        have hm0 := Real.sqrt_nonneg (m : ℝ)
        have hle : Real.sqrt (m : ℝ) ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) :=
          Real.sqrt_le_sqrt (by push_cast; linarith)
        have hsq : Real.sqrt ((m + 1 : ℕ) : ℝ) ^ 2 - Real.sqrt (m : ℝ) ^ 2 = 1 := by
          rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]; push_cast; ring
        rw [div_le_iff₀ hpos]
        nlinarith [mul_nonneg hm0 (sub_nonneg.2 hle)]
      calc _ ≤ 2 * Real.sqrt m + 2 * (Real.sqrt ((m + 1 : ℕ) : ℝ) - Real.sqrt m) := add_le_add ih h1
        _ = 2 * Real.sqrt ((m + 1 : ℕ) : ℝ) := by ring
  have := key n
  have hle : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_le_sqrt (by push_cast; linarith)
  linarith

end Sums

section FD

variable {p : ℕ} {B binv : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)}

lemma cpow_nuS_N (hBs : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y)) (N : ℕ) (hN : 1 ≤ N) :
    cpow (nuS B (Real.sqrt (N : ℝ)⁻¹)) N = nuS B 1 := by
  rw [cpow_nuS hBs]
  congr 1
  rw [← Real.sqrt_mul (Nat.cast_nonneg N), mul_inv_cancel₀ (by positivity), Real.sqrt_one]

/-- Finite-dimensional Lindeberg bound for 1-Lipschitz bounded tests. -/
theorem fd_lip (hBs : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y)) (hBb : ∀ y, B (binv y) = y)
    (hbB : ∀ y, binv (B y) = y) {N : ℕ} (hN : 1 ≤ N)
    {μ : Measure (EuclideanSpace ℝ (Fin p))} [IsProbabilityMeasure μ]
    (hμ : MomMatch B (N : ℝ)⁻¹ μ) {b : ℝ} (hb0 : 0 ≤ b) (hb : ∀ᵐ y ∂μ, ‖y‖ ≤ b)
    {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : LipschitzWith 1 f) {R : ℝ} (hR : ∀ z, |f z| ≤ R) :
    |∫ z, f z ∂(cpow μ N) - ∫ z, f z ∂(nuS B 1)| ≤
      b * (p * Real.log (Real.exp 1 * N) + 2) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hκ : 0 < (N : ℝ)⁻¹ := by positivity
  set κ : ℝ := (N : ℝ)⁻¹ with hκdef
  set ν := nuS B (Real.sqrt κ) with hν
  rw [← cpow_nuS_N hBs N hN]
  have hT := telescope_abs μ ν hf.continuous.measurable hR N
    (fun k => b * p / ((N - (k + 1) : ℕ) : ℝ) + if k + 1 = N then 2 * b else 0) (by
      intro k hk x
      rcases Nat.lt_or_ge (k + 1) N with hlt | hge
      · have hm : 1 ≤ N - (k + 1) := by omega
        have := step_lip hBs hBb hbB hκ hμ hb0 hb hf hR hm x
        have hne : ¬ (k + 1 = N) := by omega
        rw [if_neg hne, add_zero]
        exact this
      · have hkN : k + 1 = N := by omega
        have h0 : N - (k + 1) = 0 := by omega
        have := final_lip hκ hBs hμ hb0 hb hf hR x
        rw [h0, if_pos hkN, Nat.cast_zero, div_zero, zero_add]
        exact this)
  refine hT.trans ?_
  rw [Finset.sum_add_distrib]
  have hsum2 : ∑ k ∈ Finset.range N, (if k + 1 = N then 2 * b else 0) = 2 * b := by
    rw [Finset.sum_eq_single (N - 1)]
    · simp [show N - 1 + 1 = N by omega]
    · intro k _ hk
      have : ¬ (k + 1 = N) := by omega
      simp [this]
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  rw [hsum2]
  have hl := sum_inv_le_log N hN
  have e : ∑ k ∈ Finset.range N, b * p / ((N - (k + 1) : ℕ) : ℝ) =
      b * p * ∑ k ∈ Finset.range N, (1 : ℝ) / ((N - (k + 1) : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [e]
  have hbp : 0 ≤ b * p := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hl hbp]

/-- Finite-dimensional Lindeberg bound for `C²` tests with bounded Hessian. -/
theorem fd_C2 (hBs : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y)) (hBb : ∀ y, B (binv y) = y)
    (hbB : ∀ y, binv (B y) = y) {N : ℕ} (hN : 1 ≤ N)
    {μ : Measure (EuclideanSpace ℝ (Fin p))} [IsProbabilityMeasure μ]
    (hμ : MomMatch B (N : ℝ)⁻¹ μ) {b : ℝ} (hb0 : 0 ≤ b) (hb : ∀ᵐ y ∂μ, ‖y‖ ≤ b)
    {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : ContDiff ℝ 2 f) {M0 M1 M2 : ℝ}
    (h0 : ∀ z, |f z| ≤ M0) (h1 : ∀ z, ‖fderiv ℝ f z‖ ≤ M1)
    (h2 : ∀ z, ‖iteratedFDeriv ℝ 2 f z‖ ≤ M2) :
    |∫ z, f z ∂(cpow μ N) - ∫ z, f z ∂(nuS B 1)| ≤
      M2 * b ^ 2 * (2 * Real.sqrt p * Real.sqrt N + 1) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hκ : 0 < (N : ℝ)⁻¹ := by positivity
  set κ : ℝ := (N : ℝ)⁻¹ with hκdef
  set ν := nuS B (Real.sqrt κ) with hν
  have hM2 : 0 ≤ M2 := (norm_nonneg (iteratedFDeriv ℝ 2 f 0)).trans (h2 0)
  have h2' : ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ M2 := fun z => by
    have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (x := z) (n := 1)
    rw [norm_iteratedFDeriv_one] at this
    rw [this]; exact h2 z
  rw [← cpow_nuS_N hBs N hN]
  have hT := telescope_abs μ ν hf.continuous.measurable h0 N
    (fun k => M2 * b ^ 2 * Real.sqrt p / Real.sqrt ((N - (k + 1) : ℕ) : ℝ) +
      if k + 1 = N then M2 * b ^ 2 else 0) (by
      intro k hk x
      rcases Nat.lt_or_ge (k + 1) N with hlt | hge
      · have hm : 1 ≤ N - (k + 1) := by omega
        have := step_C2 hBs hBb hbB hκ hμ hb0 hb hf h0 h1 h2' hm x
        have hne : ¬ (k + 1 = N) := by omega
        rw [if_neg hne, add_zero]
        exact this
      · have hkN : k + 1 = N := by omega
        have h0' : N - (k + 1) = 0 := by omega
        have := final_C2 hκ hBs hμ hb0 hb hf h0 h2 x
        rw [h0', if_pos hkN, Nat.cast_zero, Real.sqrt_zero, div_zero, zero_add]
        exact this)
  refine hT.trans ?_
  rw [Finset.sum_add_distrib]
  have hsum2 : ∑ k ∈ Finset.range N, (if k + 1 = N then M2 * b ^ 2 else 0) = M2 * b ^ 2 := by
    rw [Finset.sum_eq_single (N - 1)]
    · simp [show N - 1 + 1 = N by omega]
    · intro k _ hk
      have : ¬ (k + 1 = N) := by omega
      simp [this]
    · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
  rw [hsum2]
  have hl := sum_inv_sqrt_le N hN
  have e : ∑ k ∈ Finset.range N, M2 * b ^ 2 * Real.sqrt p / Real.sqrt ((N - (k + 1) : ℕ) : ℝ) =
      M2 * b ^ 2 * Real.sqrt p * ∑ k ∈ Finset.range N, (1 : ℝ) / Real.sqrt ((N - (k + 1) : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [e]
  have hbp : 0 ≤ M2 * b ^ 2 * Real.sqrt p := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hl hbp]

end FD

end HRS.IID
