import Mathlib
import HRS.MS.SuppU5Aux1

/-!
# Packet U5 (aux 2): Gaussian images, second moments, independence sums
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace Matrix

noncomputable section

namespace HRS.U5

/-- Linear image of a centered multivariate Gaussian. -/
lemma u5_gauss_map {m k : ℕ} {S₁ : Matrix (Fin m) (Fin m) ℝ} {S₂ : Matrix (Fin k) (Fin k) ℝ}
    (h₂ : S₂.PosSemidef) (M : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (h : ∀ u v, (M.adjoint u) ⬝ᵥ (S₁ *ᵥ (M.adjoint v)) = u ⬝ᵥ (S₂ *ᵥ v))
    (h₁ : S₁.PosSemidef) :
    (multivariateGaussian 0 S₁).map M = multivariateGaussian 0 S₂ := by
  haveI : IsGaussian ((multivariateGaussian 0 S₁).map M) := inferInstance
  refine IsGaussian.ext ?_ ?_
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id]
    simp
  · ext u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id, covarianceBilin_multivariateGaussian h₁,
      covarianceBilin_multivariateGaussian h₂]
    exact h u v


/-! ### Sums of independent centred bounded variables -/

abbrev Ek (k : ℕ) := EuclideanSpace ℝ (Fin k)

lemma u5_ae_pi {N k : ℕ} {ρ : Measure (Ek k)} [IsProbabilityMeasure ρ] {p : Ek k → Prop}
    (h : ∀ᵐ y ∂ρ, p y) : ∀ᵐ ω ∂(Measure.pi fun _ : Fin N => ρ), ∀ i, p (ω i) := by
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval (fun _ : Fin N => ρ) i).quasiMeasurePreserving.ae h

lemma u5_pi_sum_sq_real {N k : ℕ} (ρ : Measure (Ek k)) [IsProbabilityMeasure ρ] (f : Ek k → ℝ)
    (hf : Measurable f) {B : ℝ} (hb : ∀ᵐ y ∂ρ, |f y| ≤ B) (h0 : ∫ y, f y ∂ρ = 0) :
    ∫ ω, (∑ i : Fin N, f (ω i)) ^ 2 ∂(Measure.pi fun _ : Fin N => ρ) =
      N * ∫ y, (f y) ^ 2 ∂ρ := by
  have hL : MemLp f 2 ρ := MemLp.of_bound hf.aestronglyMeasurable B (hb.mono fun y hy => by
    simpa [Real.norm_eq_abs] using hy)
  have h := variance_sum_pi (μ := fun _ : Fin N => ρ) (X := fun _ => f) (fun _ => hL)
  have hm : Measurable (fun ω : Fin N → Ek k => ∑ i : Fin N, f (ω i)) :=
    Finset.measurable_sum _ fun i _ => hf.comp (measurable_pi_apply i)
  have e1 : (∑ i : Fin N, fun ω : Fin N → Ek k => f (ω i)) = fun ω => ∑ i : Fin N, f (ω i) := by
    ext ω; simp
  rw [e1] at h
  have hmean : ∫ ω, (∑ i : Fin N, f (ω i)) ∂(Measure.pi fun _ : Fin N => ρ) = 0 := by
    have hint : ∀ i : Fin N, Integrable (fun ω : Fin N → Ek k => f (ω i)) (Measure.pi fun _ : Fin N => ρ) :=
      fun i => (measurePreserving_eval (fun _ : Fin N => ρ) i).integrable_comp_of_integrable
        (hL.integrable one_le_two)
    rw [integral_finsetSum _ fun i _ => hint i]
    refine Finset.sum_eq_zero fun i _ => ?_
    have := integral_map (μ := Measure.pi fun _ : Fin N => ρ) (φ := fun ω : Fin N → Ek k => ω i)
      (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable
    rw [(measurePreserving_eval (fun _ : Fin N => ρ) i).map_eq] at this
    rw [← this]; exact h0
  rw [variance_of_integral_eq_zero hm.aemeasurable hmean] at h
  rw [h]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 1
  rw [variance_of_integral_eq_zero hf.aemeasurable h0]


lemma u5_pi_sum_sq {N k k' : ℕ} (ρ : Measure (Ek k)) [IsProbabilityMeasure ρ] (v : Ek k → Ek k')
    (hv : Measurable v) {B : ℝ} (hb : ∀ᵐ y ∂ρ, ‖v y‖ ≤ B) (h0 : ∀ c, ∫ y, v y c ∂ρ = 0) :
    ∫ ω, ‖∑ i : Fin N, v (ω i)‖ ^ 2 ∂(Measure.pi fun _ : Fin N => ρ) =
      N * ∫ y, ‖v y‖ ^ 2 ∂ρ := by
  have hc : ∀ c : Fin k', Measurable fun y => v y c := fun c =>
    (EuclideanSpace.proj c : Ek k' →L[ℝ] ℝ).measurable.comp hv
  have hcb : ∀ᵐ y ∂ρ, ∀ c : Fin k', |v y c| ≤ B := hb.mono fun y hy c =>
    (by simpa using PiLp.norm_apply_le (v y) c : |v y c| ≤ ‖v y‖).trans hy
  have hmeasc : ∀ c : Fin k', Measurable fun ω : Fin N → Ek k => ∑ i : Fin N, v (ω i) c := fun c =>
    Finset.measurable_sum _ fun i _ => (hc c).comp (measurable_pi_apply i)
  have e1 : ∀ ω : Fin N → Ek k, ‖∑ i : Fin N, v (ω i)‖ ^ 2 = ∑ c : Fin k', (∑ i : Fin N, v (ω i) c) ^ 2 := by
    intro ω
    rw [EuclideanSpace.real_norm_sq_eq]
    simp
  have e2 : ∀ y, ‖v y‖ ^ 2 = ∑ c : Fin k', (v y c) ^ 2 := fun y => EuclideanSpace.real_norm_sq_eq _
  have hbi : ∀ c : Fin k', Integrable (fun y => (v y c) ^ 2) ρ := fun c =>
    Integrable.of_bound ((hc c).pow_const 2).aestronglyMeasurable (B ^ 2) (hcb.mono fun y hy => by
      rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hy c) 2)
  have hbi2 : ∀ c : Fin k', Integrable (fun ω : Fin N → Ek k => (∑ i : Fin N, v (ω i) c) ^ 2)
      (Measure.pi fun _ : Fin N => ρ) := fun c =>
    Integrable.of_bound ((hmeasc c).pow_const 2).aestronglyMeasurable ((N * B) ^ 2)
      ((u5_ae_pi (N := N) hcb).mono fun ω hω => by
        rw [Real.norm_eq_abs, abs_pow]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
        calc |∑ i : Fin N, v (ω i) c| ≤ ∑ i : Fin N, |v (ω i) c| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin N, B := Finset.sum_le_sum fun i _ => hω i c
          _ = N * B := by simp)
  simp_rw [e1, e2]
  rw [integral_finsetSum _ fun c _ => hbi2 c, integral_finsetSum _ fun c _ => hbi c,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  exact u5_pi_sum_sq_real ρ (fun y => v y c) (hc c) (hcb.mono fun y hy => hy c) (h0 c)


/-! ### Wasserstein distance and contractions -/

/-- A linear contraction does not increase `W_1`. -/
lemma u5_wasserstein_map_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] (f : E →L[ℝ] F) (hf : ‖f‖ ≤ 1) (P Q : Measure E) :
    wassersteinE 1 (P.map f) (Q.map f) ≤ wassersteinE 1 P Q := by
  refine le_iInf fun π => ?_
  have hm : Measurable (Prod.map f f : E × E → F × F) := (f.continuous.prodMap f.continuous).measurable
  have hcpl : IsCoupling (π.1.map (Prod.map f f)) (P.map f) (Q.map f) := by
    obtain ⟨h1, h2⟩ := π.2
    constructor
    · rw [Measure.map_map measurable_fst hm]
      have : (Prod.fst ∘ Prod.map f f : E × E → F) = f ∘ Prod.fst := rfl
      rw [this, ← Measure.map_map f.continuous.measurable measurable_fst, h1]
    · rw [Measure.map_map measurable_snd hm]
      have : (Prod.snd ∘ Prod.map f f : E × E → F) = f ∘ Prod.snd := rfl
      rw [this, ← Measure.map_map f.continuous.measurable measurable_snd, h2]
  refine (wassersteinE_le_cost hcpl).trans ?_
  have hmeas : Measurable fun z : F × F => ENNReal.ofReal (‖z.1 - z.2‖ ^ (1 : ℝ)) :=
    ENNReal.measurable_ofReal.comp ((measurable_fst.sub measurable_snd).norm.pow_const _)
  rw [lintegral_map hmeas hm]
  simp only [Real.rpow_one, div_one, ENNReal.rpow_one]
  refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
  simp only [Prod.map_fst, Prod.map_snd]
  rw [← map_sub]
  exact (f.le_opNorm _).trans (by nlinarith [norm_nonneg (z.1 - z.2)])

/-- Jensen: `(∫ f)² ≤ ∫ f²`. -/
lemma u5_sq_integral_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {f : Ω → ℝ} (hf : MemLp f 2 P) : (∫ ω, f ω ∂P) ^ 2 ≤ ∫ ω, (f ω) ^ 2 ∂P := by
  have h := variance_nonneg f P
  rw [variance_eq_sub hf] at h
  simp only [Pi.pow_apply] at h
  linarith

lemma u5_integral_le_sqrt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {f : Ω → ℝ} (hf : MemLp f 2 P) (h0 : 0 ≤ ∫ ω, f ω ∂P) :
    ∫ ω, f ω ∂P ≤ Real.sqrt (∫ ω, (f ω) ^ 2 ∂P) :=
  Real.le_sqrt_of_sq_le (u5_sq_integral_le P hf)


/-! ### Second moments of Gaussian images -/

lemma u5_int_sq_lin {k : ℕ} (ν : Measure (Ek k)) [IsFiniteMeasure ν]
    (h2 : Integrable (fun y : Ek k => ‖y‖ ^ 2) ν) (L : Ek k →L[ℝ] ℝ) :
    ∫ z, (L z) ^ 2 ∂ν = ∑ a, ∑ b, L (EuclideanSpace.single a 1) * L (EuclideanSpace.single b 1) *
      ∫ z, z a * z b ∂ν := by
  have hI := Yurinskii.integrable_coord_mul h2
  have e : ∀ z : Ek k, (L z) ^ 2 = ∑ a, ∑ b, (L (EuclideanSpace.single a 1) *
      L (EuclideanSpace.single b 1)) * (z a * z b) := fun z => by
    rw [Yurinskii.expand1 L z, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hI a b).const_mul _]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => (hI a b).const_mul _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul]

lemma u5_gauss_sq_eq {k k' : ℕ} (ρ : Measure (Ek k)) [IsProbabilityMeasure ρ]
    (h2 : Integrable (fun y : Ek k => ‖y‖ ^ 2) ρ) (F : Ek k →L[ℝ] Ek k') :
    ∫ z, ‖F z‖ ^ 2 ∂(multivariateGaussian (0 : Ek k) (Yurinskii.momentMatrix ρ)) =
      ∫ y, ‖F y‖ ^ 2 ∂ρ := by
  set Q := Yurinskii.momentMatrix ρ with hQ
  have hQp : Q.PosSemidef := Yurinskii.momentMatrix_posSemidef ρ h2
  set γ := multivariateGaussian (0 : Ek k) Q with hγ
  have h2γ : Integrable (fun y : Ek k => ‖y‖ ^ 2) γ := Yurinskii.integrable_norm_pow_gauss 2 (by norm_num)
  have hsq : ∀ (ν : Measure (Ek k)) [IsFiniteMeasure ν], Integrable (fun y : Ek k => ‖y‖ ^ 2) ν →
      ∫ z, ‖F z‖ ^ 2 ∂ν = ∑ c : Fin k', ∑ a, ∑ b,
        (EuclideanSpace.proj c : Ek k' →L[ℝ] ℝ) (F (EuclideanSpace.single a 1)) *
        (EuclideanSpace.proj c : Ek k' →L[ℝ] ℝ) (F (EuclideanSpace.single b 1)) *
          ∫ z, z a * z b ∂ν := by
    intro ν _ hν
    have hLi : ∀ c : Fin k', Integrable (fun z => ((EuclideanSpace.proj c : Ek k' →L[ℝ] ℝ).comp F z) ^ 2) ν := by
      intro c
      refine (hν.const_mul (‖(EuclideanSpace.proj c : Ek k' →L[ℝ] ℝ).comp F‖ ^ 2)).mono'
        (((EuclideanSpace.proj c : Ek k' →L[ℝ] ℝ).comp F).continuous.measurable.pow_const 2).aestronglyMeasurable
        (ae_of_all _ fun z => ?_)
      rw [Real.norm_eq_abs, abs_pow, ← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using ((EuclideanSpace.proj c : Ek k' →L[ℝ] ℝ).comp F).le_opNorm z) 2
    have e : ∀ z, ‖F z‖ ^ 2 = ∑ c : Fin k', (((EuclideanSpace.proj c : Ek k' →L[ℝ] ℝ).comp F) z) ^ 2 :=
      fun z => EuclideanSpace.real_norm_sq_eq _
    simp_rw [e]
    rw [integral_finsetSum _ fun c _ => hLi c]
    refine Finset.sum_congr rfl fun c _ => ?_
    exact u5_int_sq_lin ν hν ((EuclideanSpace.proj c : Ek k' →L[ℝ] ℝ).comp F)
  rw [hsq γ h2γ, hsq ρ h2]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Yurinskii.integral_coord_mul hQp]
  rfl

end HRS.U5
