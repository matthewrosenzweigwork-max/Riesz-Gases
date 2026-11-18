import HRS.Equilibrium.PairCorrection
import HRS.Stochastic.Particle
import HRS.Prob.Gaussian
import Mathlib

open MeasureTheory Filter Topology ProbabilityTheory Set Matrix Metric
open scoped Pointwise

noncomputable section

namespace HRS.LocalDivAux

variable {d : ℕ}

/-- The cube `(-1/2, 1/2]^d`. -/
def cube (d : ℕ) : Set (Euc d) := {w | ∀ i, w i ∈ Ioc (-1/2 : ℝ) (-1/2 + 1)}

theorem measurableSet_cube : MeasurableSet (cube d) := by
  have : cube d = (fun w : Euc d => w.ofLp) ⁻¹' (Set.pi univ fun _ : Fin d => Ioc (-1/2 : ℝ) (-1/2 + 1)) := by
    ext w; simp [cube]
  rw [this]
  exact (MeasurableSet.pi countable_univ fun _ _ => measurableSet_Ioc).preimage
    (PiLp.volume_preserving_ofLp (Fin d)).measurable

theorem mk_measurePreserving :
    MeasurePreserving (Torus.mk : Euc d → Torus d) (volume.restrict (cube d)) volume := by
  have h1 := measurePreserving_pi (fun _ : Fin d => (volume : Measure ℝ).restrict (Ioc (-1/2 : ℝ) (-1/2 + 1)))
    (fun _ : Fin d => (volume : Measure UnitAddCircle))
    (f := fun _ => ((↑) : ℝ → UnitAddCircle)) (fun _ => UnitAddCircle.measurePreserving_mk (-1/2))
  rw [← Measure.restrict_pi_pi] at h1
  have h2 := (PiLp.volume_preserving_ofLp (Fin d)).restrict_preimage
    (s := Set.pi univ fun _ : Fin d => Ioc (-1/2 : ℝ) (-1/2 + 1))
    (MeasurableSet.pi countable_univ fun _ _ => measurableSet_Ioc)
  have e : (Set.pi univ fun _ : Fin d => Ioc (-1/2 : ℝ) (-1/2 + 1)) = (Set.pi univ fun _ : Fin d => Ioc (-1/2 : ℝ) (-1/2 + 1)) := rfl
  have hc : (fun w : Euc d => w.ofLp) ⁻¹' (Set.pi univ fun _ : Fin d => Ioc (-1/2 : ℝ) (-1/2 + 1)) = cube d := by
    ext w; simp [cube]
  rw [hc] at h2
  exact h1.comp h2

theorem eucDist_mk_zero {w : Euc d} (hw : w ∈ cube d) : Torus.eucDist (Torus.mk w) 0 = ‖w‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold Torus.eucDist
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := hw i
  have h2 : ‖((Torus.mk w : Torus d) i - (0 : Torus d) i)‖ = |w i| := by
    have : ((Torus.mk w : Torus d) i - (0 : Torus d) i) = ((w i : ℝ) : UnitAddCircle) := by
      simp [Torus.mk]
    rw [this]
    refine (AddCircle.norm_coe_eq_abs_iff (p := (1:ℝ)) one_ne_zero).2 ?_
    have h3 := h1.1
    have h4 := h1.2
    rw [abs_one, abs_le]
    constructor <;> linarith
  rw [h2, Real.norm_eq_abs]

theorem ball_subset_cube {δ : ℝ} (hδ : δ ≤ 1/2) : Metric.ball (0 : Euc d) δ ⊆ cube d := by
  intro w hw i
  have h1 : |w i| ≤ ‖w‖ := by
    have := PiLp.norm_apply_le w i
    simpa [Real.norm_eq_abs] using this
  have h2 : ‖w‖ < δ := by simpa using hw
  have := abs_lt.1 (lt_of_le_of_lt h1 (h2.trans_le hδ))
  constructor <;> linarith [this.1, this.2]

theorem integral_torus_local {δ : ℝ} (hδ : δ ≤ 1/2) (G : Torus d → ℝ) (hG : Measurable G)
    (hsupp : ∀ z, δ ≤ Torus.eucDist z 0 → G z = 0) :
    ∫ z, G z = ∫ w in Metric.ball (0 : Euc d) δ, G (Torus.mk w) := by
  have hmp := mk_measurePreserving (d := d)
  have h1 : ∫ z, G z = ∫ w in cube d, G (Torus.mk w) := by
    rw [← hmp.map_eq]
    exact integral_map hmp.measurable.aemeasurable hG.aestronglyMeasurable
  rw [h1]
  refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (f := fun w : Euc d => G (Torus.mk w))
    measurableSet_cube (ball_subset_cube hδ) ?_)
  intro w hw
  apply hsupp
  rw [eucDist_mk_zero hw.1]
  by_contra h
  exact hw.2 (by simpa using not_le.1 h)


section Polar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] (μ : Measure E) [μ.IsAddHaarMeasure]

open Module in
theorem integral_polar (q : E → ℝ) (hq : ∀ t : ℝ, 0 < t → ∀ w, q (t • w) = t ^ 4 * q w)
    (f : ℝ → ℝ) :
    ∫ w, q w * f ‖w‖ ∂μ =
      (∫ ω : sphere (0 : E) 1, q ω ∂μ.toSphere) *
        ∫ r in Ioi (0 : ℝ), r ^ (finrank ℝ E - 1 + 4) * f r := by
  calc ∫ w, q w * f ‖w‖ ∂μ
      = ∫ x : ({(0)}ᶜ : Set E), q x.1 * f ‖x.1‖ ∂(μ.comap (↑)) := by
        rw [integral_subtype_comap (measurableSet_singleton _).compl fun x => q x * f ‖x‖,
          restrict_compl_singleton]
    _ = ∫ p : sphere (0 : E) 1 × Ioi (0 : ℝ), q p.1 * (p.2.1 ^ 4 * f p.2.1)
          ∂(μ.toSphere.prod (Measure.volumeIoiPow (finrank ℝ E - 1))) := by
        have := μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
          (Homeomorph.measurableEmbedding _)
          (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => q p.1 * (p.2.1 ^ 4 * f p.2.1))
        rw [← this]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [homeomorphUnitSphereProd_apply_snd_coe]
        have hn : 0 < ‖x.1‖ := norm_pos_iff.2 x.2
        have h1 : q x.1 = ‖x.1‖ ^ 4 * q ((‖x.1‖⁻¹) • x.1) := by
          rw [← hq _ hn, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
        simp only [homeomorphUnitSphereProd_apply_fst_coe]
        rw [h1]; ring
    _ = _ := by
        rw [integral_prod_mul (μ := μ.toSphere) (ν := Measure.volumeIoiPow (finrank ℝ E - 1))
          (fun ω : sphere (0 : E) 1 => q ω) (fun r : Ioi (0 : ℝ) => (r.1) ^ 4 * f r.1)]
        congr 1
        simp only [Measure.volumeIoiPow, ENNReal.ofReal]
        rw [integral_withDensity_eq_integral_smul]
        · rw [integral_subtype_comap measurableSet_Ioi fun a => Real.toNNReal (a ^ (finrank ℝ E - 1)) • (a ^ 4 * f a)]
          refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
          rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hx.out.le _)]
          simp only [smul_eq_mul]; ring
        · exact (measurable_subtype_coe.pow_const _).real_toNNReal
end Polar



abbrev γd (d : ℕ) : Measure (Fin d → ℝ) := Measure.pi (fun _ : Fin d => gaussianReal 0 1)

theorem pi_gauss_eq (d : ℕ) :
    Measure.pi (fun _ : Fin d => gaussianReal 0 1) =
      (volume : Measure (Fin d → ℝ)).withDensity
        (fun x => ∏ i, ENNReal.ofReal (gaussianPDFReal 0 1 (x i))) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.pi countable_univ fun i _ => hs i)]
  set g : Fin d → ℝ → ℝ := fun i y => (s i).indicator (gaussianPDFReal 0 1) y with hg
  have hg0 : ∀ i y, 0 ≤ g i y := fun i y => by
    simp only [hg]; exact indicator_nonneg (fun y _ => gaussianPDFReal_nonneg 0 1 y) y
  have hgi : ∀ i, Integrable (g i) volume := fun i => by
    simp only [hg]; exact (integrable_gaussianPDFReal 0 1).indicator (hs i)
  have h1 : ∀ x : Fin d → ℝ, (Set.pi univ s).indicator
      (fun x => ∏ i, ENNReal.ofReal (gaussianPDFReal 0 1 (x i))) x =
      ENNReal.ofReal (∏ i, g i (x i)) := by
    intro x
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => hg0 i (x i))]
    by_cases hx : x ∈ Set.pi univ s
    · rw [indicator_of_mem hx]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [hg]; rw [indicator_of_mem (hx i (mem_univ i))]
    · rw [indicator_of_notMem hx]
      obtain ⟨i, hi⟩ : ∃ i, x i ∉ s i := by
        by_contra h; push Not at h; exact hx (fun i _ => h i)
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hg, indicator_of_notMem hi])
  rw [← lintegral_indicator (MeasurableSet.pi countable_univ fun i _ => hs i)]
  simp_rw [h1]
  have hint : Integrable (fun x : Fin d → ℝ => ∏ i, g i (x i)) volume := by
    rw [volume_pi]
    exact Integrable.fintype_prod (fun i => hgi i)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x =>
    Finset.prod_nonneg fun i _ => hg0 i (x i))]
  rw [volume_pi, integral_fintype_prod_eq_prod (fun i y => g i y)]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hg0 i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [hg]
  rw [integral_indicator (hs i), gaussianReal_apply_eq_integral 0 one_ne_zero]


theorem gauss_xx_integrable (i j : Fin d) : Integrable (fun x : Fin d → ℝ => x i * x j) (γd d) := by
  have h4 : ∀ k, Integrable (fun x : Fin d → ℝ => (x k) ^ 2) (γd d) := fun k =>
    pi_integrable_eval d (fun t => t ^ 2) (by fun_prop) (gauss_integrable_pow 2) k
  refine Integrable.mono' (((h4 i).add (h4 j))) ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact ((measurable_pi_apply i).mul (measurable_pi_apply j)).aestronglyMeasurable
  · simp only [Real.norm_eq_abs, Pi.add_apply, abs_mul]
    nlinarith [sq_abs (x i), sq_abs (x j), sq_nonneg (|x i| - |x j|), abs_nonneg (x i), abs_nonneg (x j)]

theorem gauss_xx_mean (i j : Fin d) :
    ∫ x : Fin d → ℝ, x i * x j ∂(γd d) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h
    simp only [if_true]
    have := pi_integral_eval d (fun t => t ^ 2) (by fun_prop) i
    simp only [gauss_sq] at this
    simpa [sq] using this
  · simp only [h, if_false]
    have := pi_integral_cross d (fun t => t) (fun t => t) (by fun_prop) (by fun_prop) i j h
    simpa using this

theorem gauss_quad_mean (A : Matrix (Fin d) (Fin d) ℝ) :
    ∫ x : Fin d → ℝ, x ⬝ᵥ (A *ᵥ x) ∂(γd d) = A.trace := by
  set B : Fin d → Fin d → ℝ := fun i j => A i j with hB
  have e : ∀ x : Fin d → ℝ, x ⬝ᵥ (A *ᵥ x) = ∑ i, ∑ j, B i j * (x i * x j) := by
    intro x
    simp only [dotProduct, mulVec, Finset.mul_sum, hB]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e]
  have hi : ∀ i, ∫ x : Fin d → ℝ, ∑ j, B i j * (x i * x j) ∂(γd d) = B i i := by
    intro i
    rw [integral_finsetSum (μ := γd d) (f := fun j x => B i j * (x i * x j)) Finset.univ (fun j _ => (gauss_xx_integrable i j).const_mul _)]
    simp_rw [integral_const_mul, gauss_xx_mean]
    simp
  rw [integral_finsetSum (μ := γd d) (f := fun i x => ∑ j, B i j * (x i * x j)) Finset.univ (fun i _ => integrable_finsetSum _ fun j _ => (gauss_xx_integrable i j).const_mul _)]
  simp_rw [hi]
  rfl

theorem gauss_quad_sq (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian) :
    ∫ x : Fin d → ℝ, (x ⬝ᵥ (A *ᵥ x)) ^ 2 ∂(γd d) = A.trace ^ 2 + 2 * ∑ i, ∑ j, A i j ^ 2 := by
  have hq := quad_L2 d A hA
  rw [vGauss_eq] at hq
  have hmeas : Measurable (fun x : Fin d → ℝ => x ⬝ᵥ (A *ᵥ x)) := by
    simp only [dotProduct, mulVec]
    fun_prop
  by_cases h0 : ∑ i, ∑ j, A i j ^ 2 = 0
  · have hz : ∀ i j, A i j = 0 := by
      intro i j
      have h1 : ∑ i, ∑ j, A i j ^ 2 = 0 := h0
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (A i j))).1 h1 i (Finset.mem_univ _)
      have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (A i j))).1 h2 j (Finset.mem_univ _)
      exact pow_eq_zero_iff (two_ne_zero) |>.1 h3
    have hA0 : A = 0 := by ext i j; exact hz i j
    subst hA0
    simp
  · have hne : ∫ x : Fin d → ℝ, (x ⬝ᵥ (A *ᵥ x) - A.trace) ^ 2 ∂(γd d) ≠ 0 := by
      rw [hq]; exact mul_ne_zero two_ne_zero h0
    have hint : Integrable (fun x : Fin d → ℝ => (x ⬝ᵥ (A *ᵥ x) - A.trace) ^ 2) (γd d) :=
      Integrable.of_integral_ne_zero hne
    have hL2 : MemLp (fun x : Fin d → ℝ => x ⬝ᵥ (A *ᵥ x) - A.trace) 2 (γd d) :=
      (memLp_two_iff_integrable_sq (hmeas.sub measurable_const).aestronglyMeasurable).2 hint
    have hL2' : MemLp (fun x : Fin d → ℝ => x ⬝ᵥ (A *ᵥ x)) 2 (γd d) := by
      have e2 : (fun x : Fin d → ℝ => x ⬝ᵥ (A *ᵥ x)) =
          (fun x : Fin d → ℝ => x ⬝ᵥ (A *ᵥ x) - A.trace) + fun _ => A.trace := by
        ext x; simp
      rw [e2]; exact hL2.add (memLp_const _)
    have hi1 : Integrable (fun x : Fin d → ℝ => x ⬝ᵥ (A *ᵥ x)) (γd d) :=
      hL2'.integrable (by norm_num)
    have hi2 : Integrable (fun x : Fin d → ℝ => (x ⬝ᵥ (A *ᵥ x)) ^ 2) (γd d) := hL2'.integrable_sq
    have e : ∀ x : Fin d → ℝ, (x ⬝ᵥ (A *ᵥ x)) ^ 2 =
        (x ⬝ᵥ (A *ᵥ x) - A.trace) ^ 2 + 2 * A.trace * (x ⬝ᵥ (A *ᵥ x) - A.trace) + A.trace ^ 2 := by
      intro x; ring
    set t := A.trace with ht
    set S := ∑ i, ∑ j, A i j ^ 2 with hS
    have hi3 : Integrable (fun x : Fin d → ℝ => 2 * t * (x ⬝ᵥ (A *ᵥ x) - t)) (γd d) :=
      (hi1.sub (integrable_const _)).const_mul _
    have i1 : ∫ x : Fin d → ℝ, ((x ⬝ᵥ (A *ᵥ x) - t) ^ 2 + 2 * t * (x ⬝ᵥ (A *ᵥ x) - t) + t ^ 2) ∂(γd d)
        = (∫ x : Fin d → ℝ, ((x ⬝ᵥ (A *ᵥ x) - t) ^ 2 + 2 * t * (x ⬝ᵥ (A *ᵥ x) - t)) ∂(γd d)) + t ^ 2 := by
      have hi4 : Integrable (fun x : Fin d → ℝ => (x ⬝ᵥ (A *ᵥ x) - t) ^ 2 + 2 * t * (x ⬝ᵥ (A *ᵥ x) - t)) (γd d) := hint.add hi3
      rw [integral_add hi4 (integrable_const _)]
      simp
    have i2 : ∫ x : Fin d → ℝ, ((x ⬝ᵥ (A *ᵥ x) - t) ^ 2 + 2 * t * (x ⬝ᵥ (A *ᵥ x) - t)) ∂(γd d)
        = (∫ x : Fin d → ℝ, (x ⬝ᵥ (A *ᵥ x) - t) ^ 2 ∂(γd d)) + ∫ x : Fin d → ℝ, 2 * t * (x ⬝ᵥ (A *ᵥ x) - t) ∂(γd d) :=
      integral_add hint hi3
    have i3 : ∫ x : Fin d → ℝ, 2 * t * (x ⬝ᵥ (A *ᵥ x) - t) ∂(γd d) = 0 := by
      rw [integral_const_mul, integral_sub hi1 (integrable_const _), gauss_quad_mean]
      simp [ht]
    simp_rw [e]
    rw [i1, i2, i3, hq]
    ring

theorem lebesgue_gauss (F : EuclideanSpace ℝ (Fin d) → ℝ) :
    ∫ w : EuclideanSpace ℝ (Fin d), F w * Real.exp (-‖w‖ ^ 2 / 2) =
      Real.sqrt (2 * Real.pi) ^ d * ∫ x : Fin d → ℝ, F (WithLp.toLp 2 x) ∂(γd d) := by
  have hmp := PiLp.volume_preserving_toLp (Fin d)
  have h1 : ∫ w : EuclideanSpace ℝ (Fin d), F w * Real.exp (-‖w‖ ^ 2 / 2) =
      ∫ x : Fin d → ℝ, F (WithLp.toLp 2 x) * Real.exp (-(∑ i, x i ^ 2) / 2) := by
    have := hmp.integral_comp (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding
      (fun w : EuclideanSpace ℝ (Fin d) => F w * Real.exp (-‖w‖ ^ 2 / 2))
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [MeasurableEquiv.toLp_apply, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  have hmeas : Measurable (fun x : Fin d → ℝ => ∏ i, ENNReal.ofReal (gaussianPDFReal 0 1 (x i))) :=
    Finset.measurable_prod _ fun i _ => ((measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i)).ennreal_ofReal
  have hlt : ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)), ∏ i, ENNReal.ofReal (gaussianPDFReal 0 1 (x i)) < ⊤ :=
    Filter.Eventually.of_forall fun x => ENNReal.prod_lt_top fun i _ => ENNReal.ofReal_lt_top
  rw [h1]
  show _ = _ * ∫ x : Fin d → ℝ, F (WithLp.toLp 2 x) ∂(Measure.pi (fun _ : Fin d => gaussianReal 0 1))
  rw [pi_gauss_eq d, integral_withDensity_eq_integral_toReal_smul hmeas hlt, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_prod]
  have : ∀ i, (ENNReal.ofReal (gaussianPDFReal 0 1 (x i))).toReal = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x i ^ 2) / 2) := by
    intro i
    rw [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 _)]
    simp [gaussianPDFReal]
  simp_rw [this]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_sum]
  have hs : ∑ i, -(x i ^ 2) / 2 = -(∑ i, x i ^ 2) / 2 := by
    rw [← Finset.sum_div, Finset.sum_neg_distrib]
  rw [hs]
  have hpos : Real.sqrt (2 * Real.pi) ^ d ≠ 0 := by positivity
  simp only [inv_pow]
  field_simp



/-- the quadratic form `w ↦ ∑ H i j w_i w_j` -/
def quadForm (H : Matrix (Fin d) (Fin d) ℝ) (w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, ∑ j, H i j * w i * w j

lemma quadForm_smul (H : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    quadForm H (t • w) = t ^ 2 * quadForm H w := by
  unfold quadForm
  simp only [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma quadForm_toLp (H : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    quadForm H (WithLp.toLp 2 x) = x ⬝ᵥ (H *ᵥ x) := by
  simp only [quadForm, dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem radial_gauss (n : ℕ) :
    ∫ r in Ioi (0 : ℝ), r ^ n * Real.exp (-r ^ 2 / 2) =
      (2 : ℝ) ^ (((n : ℝ) + 1) / 2 - 1) * Real.Gamma (((n : ℝ) + 1) / 2) := by
  set a : ℝ := ((n : ℝ) + 1) / 2 with ha
  have hapos : 0 < a := by positivity
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := a) (r := 1 / 2) hapos (by norm_num)
  rw [← integral_comp_rpow_Ioi_of_pos (g := fun y : ℝ => y ^ (a - 1) * Real.exp (-(1 / 2 * y)))
    (p := 2) two_pos] at h
  have h2 : ∀ x ∈ Ioi (0 : ℝ), ((2 : ℝ) * x ^ ((2 : ℝ) - 1)) •
      ((fun y : ℝ => y ^ (a - 1) * Real.exp (-(1 / 2 * y))) (x ^ (2 : ℝ))) =
      2 * (x ^ n * Real.exp (-x ^ 2 / 2)) := by
    intro x hx
    have hx : 0 < x := hx
    simp only [smul_eq_mul]
    have e1 : x ^ ((2 : ℝ) - 1) = x := by norm_num
    have e2 : (x ^ (2 : ℝ)) ^ (a - 1) = x ^ ((n : ℝ) - 1) := by
      rw [← Real.rpow_mul hx.le]
      congr 1
      rw [ha]; ring
    have e3 : x * x ^ ((n : ℝ) - 1) = x ^ n := by
      rw [Real.rpow_sub_one hx.ne', Real.rpow_natCast]
      field_simp
    have e4 : Real.exp (-(1 / 2 * x ^ (2 : ℝ))) = Real.exp (-x ^ 2 / 2) := by
      congr 1; rw [Real.rpow_two]; ring
    rw [e1, e2, e4]
    rw [← e3]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi h2, integral_const_mul] at h
  have : (1 / (1 / 2 : ℝ)) ^ a = 2 ^ a := by norm_num
  rw [this] at h
  rw [Real.rpow_sub_one (by norm_num)]
  linarith

/-- The Gamma function constant: `√(2π)^d = (sphereArea d /(d(d+2))) * 2^{(d+4)/2 - 1} Γ((d+4)/2)`. -/
theorem sqrt_two_pi_pow (hd : 1 ≤ d) :
    Real.sqrt (2 * Real.pi) ^ d =
      HRS.sphereArea d / (d * (d + 2)) *
        ((2 : ℝ) ^ ((((d + 3 : ℕ) : ℝ) + 1) / 2 - 1) * Real.Gamma ((((d + 3 : ℕ) : ℝ) + 1) / 2)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hg : Real.Gamma (((d : ℝ) + 4) / 2) = ((d : ℝ) + 2) / 2 * ((d : ℝ) / 2 * Real.Gamma ((d : ℝ) / 2)) := by
    have e : ((d : ℝ) + 4) / 2 = ((d : ℝ) / 2 + 1) + 1 := by ring
    rw [e, Real.Gamma_add_one (by positivity), Real.Gamma_add_one (by positivity)]
    ring
  have e1 : (((d + 3 : ℕ) : ℝ) + 1) / 2 = ((d : ℝ) + 4) / 2 := by push_cast; ring
  rw [e1, hg]
  unfold HRS.sphereArea
  have hG : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have e2 : (2 : ℝ) ^ (((d : ℝ) + 4) / 2 - 1) = 2 ^ ((d : ℝ) / 2) * 2 := by
    have : ((d : ℝ) + 4) / 2 - 1 = (d : ℝ) / 2 + 1 := by ring
    rw [this, Real.rpow_add (by norm_num), Real.rpow_one]
  have e3 : Real.sqrt (2 * Real.pi) ^ d = 2 ^ ((d : ℝ) / 2) * Real.pi ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    have e : (1 / 2 : ℝ) * (d : ℝ) = (d : ℝ) / 2 := by ring
    rw [e, Real.mul_rpow (by norm_num) Real.pi_pos.le]
  rw [e2, e3]
  field_simp


open Module in
theorem sphere_const (hd : 1 ≤ d) (H : Matrix (Fin d) (Fin d) ℝ) (hH : H.IsHermitian) :
    ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin d)) 1, quadForm H ω ^ 2
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere =
      HRS.sphereArea d / (d * (d + 2)) *
        (H.trace ^ 2 + 2 * ∑ i, ∑ j, H i j ^ 2) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hq : ∀ t : ℝ, 0 < t → ∀ w : EuclideanSpace ℝ (Fin d),
      quadForm H (t • w) ^ 2 = t ^ 4 * quadForm H w ^ 2 := by
    intro t _ w
    rw [quadForm_smul]; ring
  have hpol := integral_polar (volume : Measure (EuclideanSpace ℝ (Fin d)))
    (fun w => quadForm H w ^ 2) hq (fun r => Real.exp (-r ^ 2 / 2))
  have hL : ∫ w : EuclideanSpace ℝ (Fin d), quadForm H w ^ 2 * Real.exp (-‖w‖ ^ 2 / 2) =
      Real.sqrt (2 * Real.pi) ^ d * (H.trace ^ 2 + 2 * ∑ i, ∑ j, H i j ^ 2) := by
    rw [lebesgue_gauss (fun w => quadForm H w ^ 2)]
    congr 1
    simp_rw [quadForm_toLp]
    exact gauss_quad_sq H hH
  rw [hL] at hpol
  have hfr : finrank ℝ (EuclideanSpace ℝ (Fin d)) - 1 + 4 = d + 3 := by
    rw [finrank_euclideanSpace_fin]; omega
  rw [hfr] at hpol
  have hR := radial_gauss (d + 3)
  rw [hR] at hpol
  rw [sqrt_two_pi_pow hd] at hpol
  have hRpos : 0 < (2 : ℝ) ^ ((((d + 3 : ℕ) : ℝ) + 1) / 2 - 1) * Real.Gamma ((((d + 3 : ℕ) : ℝ) + 1) / 2) := by
    refine mul_pos (by positivity) (Real.Gamma_pos_of_pos (by positivity))
  have h2 : (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin d)) 1, quadForm H ω ^ 2
        ∂(volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere) *
      ((2 : ℝ) ^ ((((d + 3 : ℕ) : ℝ) + 1) / 2 - 1) * Real.Gamma ((((d + 3 : ℕ) : ℝ) + 1) / 2)) =
      (HRS.sphereArea d / (d * (d + 2)) * (H.trace ^ 2 + 2 * ∑ i, ∑ j, H i j ^ 2)) *
      ((2 : ℝ) ^ ((((d + 3 : ℕ) : ℝ) + 1) / 2 - 1) * Real.Gamma ((((d + 3 : ℕ) : ℝ) + 1) / 2)) := by
    exact hpol.symm.trans (by ring)
  exact mul_right_cancel₀ hRpos.ne' h2


open Module in
theorem integral_quad_radial (hd : 1 ≤ d) (H : Matrix (Fin d) (Fin d) ℝ) (hH : H.IsHermitian)
    (f : ℝ → ℝ) :
    ∫ w : EuclideanSpace ℝ (Fin d), quadForm H w ^ 2 * f ‖w‖ =
      HRS.sphereArea d / (d * (d + 2)) * (H.trace ^ 2 + 2 * ∑ i, ∑ j, H i j ^ 2) *
        ∫ r in Ioi (0 : ℝ), r ^ (d + 3) * f r := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hq : ∀ t : ℝ, 0 < t → ∀ w : EuclideanSpace ℝ (Fin d),
      quadForm H (t • w) ^ 2 = t ^ 4 * quadForm H w ^ 2 := by
    intro t _ w
    rw [quadForm_smul]; ring
  have hpol := integral_polar (volume : Measure (EuclideanSpace ℝ (Fin d)))
    (fun w => quadForm H w ^ 2) hq f
  have hfr : finrank ℝ (EuclideanSpace ℝ (Fin d)) - 1 + 4 = d + 3 := by
    rw [finrank_euclideanSpace_fin]; omega
  rw [hfr, sphere_const hd H hH] at hpol
  exact hpol


end HRS.LocalDivAux
