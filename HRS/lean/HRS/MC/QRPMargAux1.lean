import Mathlib

/-!
# QRPMarg, helper 1: abstract Gaussian bookkeeping

Generic facts (no repository vocabulary): a family of linear functionals of two independent centred Gaussian
vectors `Y, Ys` and of a centred Gaussian vector `G` independent of `(Y, Ys)` is jointly Gaussian with mean zero.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace HRS.MC.QRSpec.Marg

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A (a.e.-measurable) random variable whose pushforward is a Gaussian measure has a Gaussian law. -/
theorem qm_hasGaussianLaw_of_map {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {X : Ω → E} {μ : Measure E} [IsGaussian μ]
    (hm : AEMeasurable X P) (h : P.map X = μ) : HasGaussianLaw X P := by
  refine ⟨hm, ?_⟩
  rw [h]; infer_instance

/-- Centred-ness of the law gives mean zero of every continuous linear functional of the variable. -/
theorem qm_integral_dual_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {X : Ω → E} (hX : HasGaussianLaw X P)
    (h0 : ∀ L : StrongDual ℝ E, ∫ z, L z ∂(P.map X) = 0) (L : StrongDual ℝ E) :
    ∫ ω, L (X ω) ∂P = 0 := by
  rw [← integral_map hX.aemeasurable L.continuous.aestronglyMeasurable]
  exact h0 L

/-- A centred multivariate Gaussian law: every linear functional has mean zero. -/
theorem qm_mvg_dual_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (Cv : Matrix ι ι ℝ) {G : Ω → EuclideanSpace ℝ ι}
    (hm : AEMeasurable G P) (h : P.map G = multivariateGaussian 0 Cv)
    (g : StrongDual ℝ (EuclideanSpace ℝ ι)) : ∫ ω, g (G ω) ∂P = 0 := by
  rw [← integral_map hm g.continuous.aestronglyMeasurable, h]
  have := IsGaussian.integral_dual (μ := multivariateGaussian 0 Cv) g
  rw [this, integral_id_multivariateGaussian]
  simp

/-- The core: joint Gaussianity and mean zero of linear functionals of `(Y, Ys, G)`. -/
theorem qm_core {H E : Type*}
    [NormedAddCommGroup H] [NormedSpace ℝ H] [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
    [SecondCountableTopology H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [SecondCountableTopology E]
    {Y Ys : Ω → H} {G : Ω → E} (hY : HasGaussianLaw Y P) (hYs : HasGaussianLaw Ys P)
    (hG : HasGaussianLaw G P) (hind : IndepFun Y Ys P)
    (hind2 : IndepFun (fun ω => (Y ω, Ys ω)) G P)
    (m0 : ∀ a : StrongDual ℝ H, ∫ ω, a (Y ω) ∂P = 0)
    (m1 : ∀ a : StrongDual ℝ H, ∫ ω, a (Ys ω) ∂P = 0)
    (m2 : ∀ g : StrongDual ℝ E, ∫ ω, g (G ω) ∂P = 0)
    {ι : Type*} [Fintype ι] (a b : ι → StrongDual ℝ H) (g : ι → StrongDual ℝ E) :
    HasGaussianLaw (fun ω i => a i (Y ω) + b i (Ys ω) + g i (G ω)) P ∧
      ∀ i, ∫ ω, (a i (Y ω) + b i (Ys ω) + g i (G ω)) ∂P = 0 := by
  have hW : HasGaussianLaw (fun ω => (Y ω, Ys ω)) P := hind.hasGaussianLaw hY hYs
  have hX : HasGaussianLaw (fun ω => ((Y ω, Ys ω), G ω)) P := hind2.hasGaussianLaw hW hG
  refine ⟨?_, fun i => ?_⟩
  · let L : ((H × H) × E) →L[ℝ] (ι → ℝ) := ContinuousLinearMap.pi fun i =>
      ((a i).comp ((ContinuousLinearMap.fst ℝ H H).comp (ContinuousLinearMap.fst ℝ (H × H) E)) +
        (b i).comp ((ContinuousLinearMap.snd ℝ H H).comp (ContinuousLinearMap.fst ℝ (H × H) E))) +
        (g i).comp (ContinuousLinearMap.snd ℝ (H × H) E)
    have := hX.map_fun L
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    funext i
    simp [L]
  · have i1 : Integrable (fun ω => a i (Y ω)) P := (hY.map_fun (a i)).integrable
    have i2 : Integrable (fun ω => b i (Ys ω)) P := (hYs.map_fun (b i)).integrable
    have i3 : Integrable (fun ω => g i (G ω)) P := (hG.map_fun (g i)).integrable
    have i12 : Integrable (fun ω => a i (Y ω) + b i (Ys ω)) P := i1.add i2
    rw [integral_add i12 i3, integral_add i1 i2]
    rw [m0 (a i), m1 (b i), m2 (g i)]
    simp

end HRS.MC.QRSpec.Marg

end
