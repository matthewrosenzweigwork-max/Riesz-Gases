import Mathlib

/-!
# Packet PI-D (`s7_PID_gauss_scalar`, `s7_PID_gauss_vector`): Gaussian core

Sorry-free Mathlib-level helpers for the finite Gaussian families of `HRS/MC/S7PIDPlan.lean`:

* moments of the real Gaussian law (`gaussianReal`) of orders 2 and 4 (integration by parts on `exp (-b x²)`);
* the Gram matrix `S7PIDG_gram I f` of a finite family in `L²(I)`, which is positive semidefinite, with the
  quadratic form `c ⬝ G c = ∫_I (∑ c_i f_i)²`;
* the multivariate Gaussian `multivariateGaussian 0 G` (Mathlib) with covariance `G`: every linear form has the law
  `gaussianReal 0 (c ⬝ G c)`, and the cross moments are `G`;
* generic moment lemmas (integrability of `X²Y²`, the bound `E X²Y² ≤ 3ab` from fourth moments, and the sum bound
  `E (∑ D_a²)² ≤ 3 (∑ s_a)²`).
-/

open MeasureTheory ProbabilityTheory Matrix Real
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.Sec7.S7PIDG


lemma S7PIDG_int_pow_exp {b : ℝ} (hb : 0 < b) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n * Real.exp (-b * x ^ 2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq hb (s := (n : ℝ))
    (by have := (Nat.cast_nonneg n : (0:ℝ) ≤ n); linarith)
  simpa [Real.rpow_natCast] using h

lemma S7PIDG_ibp {b : ℝ} (hb : 0 < b) (k : ℕ) :
    ∫ x : ℝ, x ^ (k + 2) * Real.exp (-b * x ^ 2)
      = ((k + 1 : ℝ) / (2 * b)) * ∫ x : ℝ, x ^ k * Real.exp (-b * x ^ 2) := by
  have hu : ∀ x : ℝ, HasDerivAt (fun x : ℝ => x ^ (k + 1)) (((k + 1 : ℕ) : ℝ) * x ^ k) x := by
    intro x
    simpa using hasDerivAt_pow (k + 1) x
  have hv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => -(1 / (2 * b)) * Real.exp (-b * x ^ 2))
      (x * Real.exp (-b * x ^ 2)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => -b * x ^ 2) (-b * (2 * x)) x := by
      simpa using ((hasDerivAt_pow 2 x).const_mul (-b))
    have h2 := (h1.exp).const_mul (-(1 / (2 * b)))
    convert h2 using 1
    field_simp
  have hi1 : Integrable (fun x : ℝ => x ^ (k + 2) * Real.exp (-b * x ^ 2)) :=
    S7PIDG_int_pow_exp hb (k + 2)
  have huv' : Integrable (fun x : ℝ => x ^ (k + 1) * (x * Real.exp (-b * x ^ 2))) := by
    convert hi1 using 1
    ext x
    ring
  have hu'v : Integrable (fun x : ℝ => (((k + 1 : ℕ) : ℝ) * x ^ k) *
      (-(1 / (2 * b)) * Real.exp (-b * x ^ 2))) := by
    convert ((S7PIDG_int_pow_exp hb k).const_mul (-(((k + 1 : ℕ) : ℝ) * (1 / (2 * b))))) using 1
    ext x
    ring
  have huv : Integrable (fun x : ℝ => x ^ (k + 1) *
      (-(1 / (2 * b)) * Real.exp (-b * x ^ 2))) := by
    convert ((S7PIDG_int_pow_exp hb (k + 1)).const_mul (-(1 / (2 * b)))) using 1
    ext x
    ring
  have key : ∫ x : ℝ, x ^ (k + 1) * (x * Real.exp (-b * x ^ 2))
      = -∫ x : ℝ, (((k + 1 : ℕ) : ℝ) * x ^ k) * (-(1 / (2 * b)) * Real.exp (-b * x ^ 2)) :=
    integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hu x) (fun x _ => hv x)
      huv' hu'v huv
  have e1 : ∫ x : ℝ, x ^ (k + 2) * Real.exp (-b * x ^ 2)
      = ∫ x : ℝ, x ^ (k + 1) * (x * Real.exp (-b * x ^ 2)) := by
    congr 1
    funext x
    ring
  have e2 : ∫ x : ℝ, (((k + 1 : ℕ) : ℝ) * x ^ k) * (-(1 / (2 * b)) * Real.exp (-b * x ^ 2))
      = (-(((k + 1 : ℕ) : ℝ) * (1 / (2 * b)))) * ∫ x : ℝ, x ^ k * Real.exp (-b * x ^ 2) := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [e1, key, e2]
  push_cast
  ring

lemma S7PIDG_J0 {b : ℝ} :
    ∫ x : ℝ, x ^ 0 * Real.exp (-b * x ^ 2) = √(π / b) := by
  simp only [pow_zero, one_mul]
  exact integral_gaussian b

lemma S7PIDG_J2 {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, x ^ 2 * Real.exp (-b * x ^ 2) = (1 / (2 * b)) * √(π / b) := by
  have h : ∫ x : ℝ, x ^ 2 * Real.exp (-b * x ^ 2)
      = ((((0 : ℕ) : ℝ) + 1) / (2 * b)) * ∫ x : ℝ, x ^ 0 * Real.exp (-b * x ^ 2) :=
    S7PIDG_ibp hb 0
  rw [h, S7PIDG_J0]
  push_cast
  ring

lemma S7PIDG_J4 {b : ℝ} (hb : 0 < b) :
    ∫ x : ℝ, x ^ 4 * Real.exp (-b * x ^ 2) = (3 / (4 * b ^ 2)) * √(π / b) := by
  have h : ∫ x : ℝ, x ^ 4 * Real.exp (-b * x ^ 2)
      = ((((2 : ℕ) : ℝ) + 1) / (2 * b)) * ∫ x : ℝ, x ^ 2 * Real.exp (-b * x ^ 2) :=
    S7PIDG_ibp hb 2
  rw [h, S7PIDG_J2 hb]
  push_cast
  field_simp
  ring

lemma S7PIDG_gauss_pdf_eq (s : ℝ≥0) :
    ∀ x : ℝ, gaussianPDFReal 0 s x = (√(2 * π * (s : ℝ)))⁻¹ *
      Real.exp (-(1 / (2 * (s : ℝ))) * x ^ 2) := by
  intro x
  rw [gaussianPDFReal_def]
  dsimp only
  rw [show -(x - 0) ^ 2 / (2 * (s : ℝ)) = -(1 / (2 * (s : ℝ))) * x ^ 2 by ring]

lemma S7PIDG_mom2 (s : ℝ≥0) (hs : s ≠ 0) :
    ∫ x, x ^ 2 ∂(gaussianReal 0 s) = (s : ℝ) := by
  have hsr : (0 : ℝ) < s := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hs)
  have hb : 0 < 1 / (2 * (s : ℝ)) := by positivity
  have e : ∀ x : ℝ, gaussianPDFReal 0 s x * x ^ 2
      = (√(2 * π * (s : ℝ)))⁻¹ * (x ^ 2 * Real.exp (-(1 / (2 * (s : ℝ))) * x ^ 2)) := by
    intro x
    rw [S7PIDG_gauss_pdf_eq s x]
    ring
  have h1 : 1 / (2 * (1 / (2 * (s : ℝ)))) = (s : ℝ) := by field_simp
  have h2 : π / (1 / (2 * (s : ℝ))) = 2 * π * (s : ℝ) := by field_simp
  have hsq : √(2 * π * (s : ℝ)) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos (mul_pos two_pos Real.pi_pos) hsr)).ne'
  rw [integral_gaussianReal_eq_integral_smul hs]
  simp only [smul_eq_mul]
  simp_rw [e]
  rw [integral_const_mul, S7PIDG_J2 hb, h1, h2]
  field_simp

lemma S7PIDG_mom4 (s : ℝ≥0) (hs : s ≠ 0) :
    ∫ x, x ^ 4 ∂(gaussianReal 0 s) = 3 * (s : ℝ) ^ 2 := by
  have hsr : (0 : ℝ) < s := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hs)
  have hb : 0 < 1 / (2 * (s : ℝ)) := by positivity
  have e : ∀ x : ℝ, gaussianPDFReal 0 s x * x ^ 4
      = (√(2 * π * (s : ℝ)))⁻¹ * (x ^ 4 * Real.exp (-(1 / (2 * (s : ℝ))) * x ^ 2)) := by
    intro x
    rw [S7PIDG_gauss_pdf_eq s x]
    ring
  have h1 : 3 / (4 * (1 / (2 * (s : ℝ))) ^ 2) = 3 * (s : ℝ) ^ 2 := by field_simp; norm_num
  have h2 : π / (1 / (2 * (s : ℝ))) = 2 * π * (s : ℝ) := by field_simp
  have hsq : √(2 * π * (s : ℝ)) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos (mul_pos two_pos Real.pi_pos) hsr)).ne'
  rw [integral_gaussianReal_eq_integral_smul hs]
  simp only [smul_eq_mul]
  simp_rw [e]
  rw [integral_const_mul, S7PIDG_J4 hb, h1, h2]
  field_simp



section Core

variable {ι : Type} [Fintype ι]

/-- Gram matrix of a finite family of functions in `L²(I)`. -/
noncomputable def S7PIDG_gram (I : Set ℝ) (f : ι → ℝ → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => ∫ u in I, f i u * f j u

lemma S7PIDG_gram_quad (I : Set ℝ) (f : ι → ℝ → ℝ) (hf : ∀ i, MemLp (f i) 2 (volume.restrict I))
    (c : ι → ℝ) :
    c ⬝ᵥ (S7PIDG_gram I f *ᵥ c) = ∫ u in I, (∑ i, c i * f i u) ^ 2 := by
  have hint : ∀ i j, Integrable (fun u => f i u * f j u) (volume.restrict I) :=
    fun i j => (hf i).integrable_mul (hf j)
  have hsq : ∀ u, (∑ i, c i * f i u) ^ 2 = ∑ i, ∑ j, c i * c j * (f i u * f j u) := by
    intro u
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hsq]
  rw [integral_finsetSum]
  · simp_rw [integral_finsetSum _ (fun j _ => (hint _ j).const_mul _)]
    simp only [integral_const_mul]
    simp only [dotProduct, mulVec, S7PIDG_gram, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · intro i _
    exact integrable_finsetSum _ fun j _ => (hint i j).const_mul _

lemma S7PIDG_gram_psd (I : Set ℝ) (f : ι → ℝ → ℝ) (hf : ∀ i, MemLp (f i) 2 (volume.restrict I)) :
    (S7PIDG_gram I f).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext i j
    simp [S7PIDG_gram, Matrix.conjTranspose_apply, mul_comm]
  · rw [star_trivial, S7PIDG_gram_quad I f hf x]
    exact integral_nonneg fun u => sq_nonneg _

/-- The law of every linear form of the multivariate Gaussian with covariance `G`, and its cross moments. -/
theorem S7PIDG_build [DecidableEq ι] (G : Matrix ι ι ℝ) (hG : G.PosSemidef) :
    (∀ c : ι → ℝ, (multivariateGaussian (0 : EuclideanSpace ℝ ι) G).map
        (fun ω => ∑ i, c i * ω i) = gaussianReal 0 (c ⬝ᵥ (G *ᵥ c)).toNNReal) ∧
    (∀ i j, ∫ ω, ω i * ω j ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) G) = G i j) := by
  set P := multivariateGaussian (0 : EuclideanSpace ℝ ι) G with hP
  have hmean : ∀ L : EuclideanSpace ℝ ι →L[ℝ] ℝ, P[L] = 0 := by
    intro L
    rw [ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id,
      hP, integral_id_multivariateGaussian, map_zero]
  have hlaw : ∀ c : ι → ℝ, P.map (fun ω => ∑ i, c i * ω i)
      = gaussianReal 0 (c ⬝ᵥ (G *ᵥ c)).toNNReal := by
    intro c
    set v : EuclideanSpace ℝ ι := WithLp.toLp 2 c with hv
    have hfun : (fun ω : EuclideanSpace ℝ ι => ∑ i, c i * ω i) = fun ω => inner ℝ v ω := by
      funext ω
      simp [hv, PiLp.inner_apply, mul_comm]
    have hcoe : ⇑(innerSL ℝ v) = fun ω => inner ℝ v ω := by
      ext ω
      simp
    have hbil := covarianceBilin_apply_eq_cov (μ := P) IsGaussian.memLp_two_id v v
    rw [covarianceBilin_multivariateGaussian hG, covariance_self (by fun_prop)] at hbil
    rw [hfun, ← hcoe, IsGaussian.map_eq_gaussianReal, hmean, hcoe, ← hbil]
  refine ⟨hlaw, ?_⟩
  have hcoord : ∀ i : ι, MemLp (fun x : EuclideanSpace ℝ ι => x i) 2 P := by
    intro i
    exact (EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).comp_memLp'
      (IsGaussian.memLp_two_id (μ := P))
  have hmeanc : ∀ i : ι, ∫ x, x i ∂P = 0 := by
    intro i
    have := hmean (EuclideanSpace.proj i)
    simpa using this
  intro i j
  have hcov := covariance_eval_multivariateGaussian (μ := 0) hG i j
  rw [← hcov, covariance_eq_sub (hcoord i) (hcoord j), hmeanc i, hmeanc j]
  simp

end Core

lemma S7PIDG_gauss_moment4 (s : ℝ≥0) : ∫ x, x ^ 4 ∂(gaussianReal 0 s) = 3 * (s : ℝ) ^ 2 := by
  by_cases hs : s = 0
  · subst hs
    simp [gaussianReal_zero_var]
  · exact S7PIDG_mom4 s hs

lemma S7PIDG_gauss_moment2 (s : ℝ≥0) : ∫ x, x ^ 2 ∂(gaussianReal 0 s) = (s : ℝ) := by
  by_cases hs : s = 0
  · subst hs
    simp [gaussianReal_zero_var]
  · exact S7PIDG_mom2 s hs

section Generic

lemma S7PIDG_gauss_int4 (s : ℝ≥0) : Integrable (fun y : ℝ => y ^ 4) (gaussianReal 0 s) := by
  have hf : MemLp id ((4 : ℕ) : ℝ≥0∞) (gaussianReal 0 s) := by
    simpa using memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := s) (4 : ℝ≥0∞) (by norm_num)
  have h := hf.integrable_norm_pow' (μ := gaussianReal 0 s)
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  show ‖y‖ ^ 4 = y ^ 4
  rw [Real.norm_eq_abs]
  exact Even.pow_abs (by decide) y

lemma S7PIDG_gauss_int2 (s : ℝ≥0) : Integrable (fun y : ℝ => y ^ 2) (gaussianReal 0 s) := by
  have hf : MemLp id ((2 : ℕ) : ℝ≥0∞) (gaussianReal 0 s) := by
    simpa using memLp_id_gaussianReal' (μ := (0 : ℝ)) (v := s) (2 : ℝ≥0∞) (by norm_num)
  have h := hf.integrable_norm_pow' (μ := gaussianReal 0 s)
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  show ‖y‖ ^ 2 = y ^ 2
  rw [Real.norm_eq_abs]
  exact Even.pow_abs (by decide) y

/-- Transport of the moments of a real Gaussian law along a measurable map. -/
lemma S7PIDG_law_moments {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {s : ℝ≥0}
    (hX : Measurable X) (hlaw : P.map X = gaussianReal 0 s) :
    (Integrable (fun ω => X ω ^ 4) P ∧ ∫ ω, X ω ^ 4 ∂P = 3 * (s : ℝ) ^ 2) ∧
    (Integrable (fun ω => X ω ^ 2) P ∧ ∫ ω, X ω ^ 2 ∂P = (s : ℝ)) := by
  have hm4 : Measurable (fun y : ℝ => y ^ 4) := by fun_prop
  have hm2 : Measurable (fun y : ℝ => y ^ 2) := by fun_prop
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have := (integrable_map_measure hm4.aestronglyMeasurable hX.aemeasurable).1
      (by rw [hlaw]; exact S7PIDG_gauss_int4 s)
    exact this
  · have h := integral_map (μ := P) hX.aemeasurable hm4.aestronglyMeasurable
    rw [hlaw, S7PIDG_gauss_moment4] at h
    exact h.symm
  · have := (integrable_map_measure hm2.aestronglyMeasurable hX.aemeasurable).1
      (by rw [hlaw]; exact S7PIDG_gauss_int2 s)
    exact this
  · have h := integral_map (μ := P) hX.aemeasurable hm2.aestronglyMeasurable
    rw [hlaw, S7PIDG_gauss_moment2] at h
    exact h.symm

/-- `∫ X² Y²` is finite and bounded by `3ab` when `X⁴`, `Y⁴` have moments `3a²`, `3b²`. -/
lemma S7PIDG_sq_int {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → ℝ}
    (hX4 : Integrable (fun ω => X ω ^ 4) P) (hY4 : Integrable (fun ω => Y ω ^ 4) P)
    (hXm : AEStronglyMeasurable X P) (hYm : AEStronglyMeasurable Y P) :
    Integrable (fun ω => X ω ^ 2 * Y ω ^ 2) P := by
  refine Integrable.mono' ((hX4.add hY4).const_mul (1 / 2)) ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact ((hXm.pow 2).mul (hYm.pow 2))
  · simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (X ω ^ 2 - Y ω ^ 2)]

lemma S7PIDG_cross_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hX4 : Integrable (fun ω => X ω ^ 4) P) (hY4 : Integrable (fun ω => Y ω ^ 4) P)
    (hXm : ∫ ω, X ω ^ 4 ∂P = 3 * a ^ 2) (hYm : ∫ ω, Y ω ^ 4 ∂P = 3 * b ^ 2) :
    ∫ ω, X ω ^ 2 * Y ω ^ 2 ∂P ≤ 3 * a * b := by
  have hXY := S7PIDG_sq_int hX4 hY4 hX.aestronglyMeasurable hY.aestronglyMeasurable
  set C := ∫ ω, X ω ^ 2 * Y ω ^ 2 ∂P with hC
  have hdisc : ∀ t : ℝ, 0 ≤ (3 * a ^ 2) * (t * t) + (-2 * C) * t + 3 * b ^ 2 := by
    intro t
    have hexp : ∀ ω, (t * X ω ^ 2 - Y ω ^ 2) ^ 2
        = t ^ 2 * X ω ^ 4 - 2 * t * (X ω ^ 2 * Y ω ^ 2) + Y ω ^ 4 := by
      intro ω; ring
    have hint : ∫ ω, (t * X ω ^ 2 - Y ω ^ 2) ^ 2 ∂P
        = t ^ 2 * (3 * a ^ 2) - 2 * t * C + 3 * b ^ 2 := by
      simp_rw [hexp]
      rw [integral_add, integral_sub, integral_const_mul, integral_const_mul, hXm, hYm]
      · exact (hX4.const_mul _)
      · exact (hXY.const_mul _)
      · exact (hX4.const_mul _).sub (hXY.const_mul _)
      · exact hY4
    have hnn : 0 ≤ ∫ ω, (t * X ω ^ 2 - Y ω ^ 2) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
    nlinarith [hint, hnn]
  have hd := discrim_le_zero hdisc
  unfold discrim at hd
  have hab : 0 ≤ 3 * a * b := by positivity
  nlinarith [hd, hab, sq_nonneg (C - 3 * a * b)]

lemma S7PIDG_sum_sq_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : Type*} [Fintype κ]
    (D : κ → Ω → ℝ) (s : κ → ℝ) (hs : ∀ a, 0 ≤ s a) (hD : ∀ a, Measurable (D a))
    (hD4 : ∀ a, Integrable (fun ω => D a ω ^ 4) P)
    (hm4 : ∀ a, ∫ ω, D a ω ^ 4 ∂P = 3 * s a ^ 2) :
    ∫ ω, (∑ a, D a ω ^ 2) ^ 2 ∂P ≤ 3 * (∑ a, s a) ^ 2 := by
  have hexp : ∀ ω, (∑ a, D a ω ^ 2) ^ 2 = ∑ a, ∑ b, D a ω ^ 2 * D b ω ^ 2 := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
  have hint : ∀ a b, Integrable (fun ω => D a ω ^ 2 * D b ω ^ 2) P := fun a b =>
    S7PIDG_sq_int (hD4 a) (hD4 b) (hD a).aestronglyMeasurable (hD b).aestronglyMeasurable
  simp_rw [hexp]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => hint a b)]
  have hle : ∑ a, ∫ ω, ∑ b, D a ω ^ 2 * D b ω ^ 2 ∂P ≤ ∑ a, ∑ b, 3 * s a * s b := by
    refine Finset.sum_le_sum fun a _ => ?_
    rw [integral_finsetSum _ (fun b _ => hint a b)]
    refine Finset.sum_le_sum fun b _ => ?_
    exact S7PIDG_cross_le (hD a) (hD b) (hs a) (hs b) (hD4 a) (hD4 b) (hm4 a) (hm4 b)
  refine hle.trans (le_of_eq ?_)
  rw [sq, Finset.sum_mul_sum]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end Generic

section Lin

variable {ι : Type} [Fintype ι]

lemma S7PIDG_lin_measurable (c : ι → ℝ) :
    Measurable (fun ω : EuclideanSpace ℝ ι => ∑ i, c i * ω i) := by
  fun_prop

lemma S7PIDG_coord_memLp [DecidableEq ι] (S : Matrix ι ι ℝ) (i : ι) :
    MemLp (fun ω : EuclideanSpace ℝ ι => ω i) 2 (multivariateGaussian (0 : EuclideanSpace ℝ ι) S) :=
  (EuclideanSpace.proj i : EuclideanSpace ℝ ι →L[ℝ] ℝ).comp_memLp' IsGaussian.memLp_two_id

/-- Integrability and the moments of the fourth and second power of a linear form of the Gaussian
vector with covariance `G`: `E (c·X)⁴ = 3 (c⬝Gc)²` and `E (c·X)² = c⬝Gc`. -/
lemma S7PIDG_lin_law_moments [DecidableEq ι] (G : Matrix ι ι ℝ) (hG : G.PosSemidef) (c : ι → ℝ) :
    (Integrable (fun ω : EuclideanSpace ℝ ι => (∑ i, c i * ω i) ^ 4)
        (multivariateGaussian (0 : EuclideanSpace ℝ ι) G) ∧
      ∫ ω, (∑ i, c i * ω i) ^ 4 ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) G)
        = 3 * (c ⬝ᵥ (G *ᵥ c)) ^ 2) ∧
    (Integrable (fun ω : EuclideanSpace ℝ ι => (∑ i, c i * ω i) ^ 2)
        (multivariateGaussian (0 : EuclideanSpace ℝ ι) G) ∧
      ∫ ω, (∑ i, c i * ω i) ^ 2 ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) G)
        = c ⬝ᵥ (G *ᵥ c)) := by
  have hq : 0 ≤ c ⬝ᵥ (G *ᵥ c) := by
    have := (posSemidef_iff_dotProduct_mulVec.1 hG).2 c
    simpa using this
  have h := S7PIDG_law_moments (S7PIDG_lin_measurable c) ((S7PIDG_build G hG).1 c)
  rw [Real.coe_toNNReal _ hq] at h
  exact h

end Lin

end HRS.MC.Sec7.S7PIDG

end
