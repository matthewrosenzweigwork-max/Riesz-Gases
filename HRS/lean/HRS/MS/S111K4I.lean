import HRS.MS.S111K4H

/-!
# S11.1 / T01 (S11K4), part I: Bessel for an `L²` kernel, Gaussian families, and `wick_difference_L2` (Pro S11.1 `T01`)
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MS.S111K4

open HRS (Euc)

/-- Bessel inequality for the Wick coefficients of a kernel which is merely a.e.-measurable and in `L²(μ ⊗ μ)`. -/
theorem k4_bessel {d : ℕ} (mu : Measure (Euc d)) [IsProbabilityMeasure mu] (a : ℕ → Euc d → ℝ)
    (ha : HRS.Whole.IsR2ZeroMeanONB mu a) (k : Euc d → Euc d → ℝ)
    (hk : MemLp (Function.uncurry k) 2 (mu.prod mu)) (F : Finset (ℕ × ℕ)) :
    ∑ p ∈ F, (HRS.Whole.r2WickCoeff mu a k p.1 p.2) ^ 2 ≤ ∫ q, (k q.1 q.2) ^ 2 ∂(mu.prod mu) := by
  set k' : Euc d → Euc d → ℝ := fun x y => hk.aestronglyMeasurable.mk (Function.uncurry k) (x, y) with hk'
  have hmk : Function.uncurry k =ᵐ[mu.prod mu] hk.aestronglyMeasurable.mk (Function.uncurry k) := hk.aestronglyMeasurable.ae_eq_mk
  have hk'm : Measurable fun q : Euc d × Euc d => k' q.1 q.2 := hk.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hk'2 : MemLp (fun q : Euc d × Euc d => k' q.1 q.2) 2 (mu.prod mu) := hk.ae_eq hmk
  have hcoef : ∀ i j, HRS.Whole.r2WickCoeff mu a k i j = HRS.Whole.r2WickCoeff mu a k' i j := by
    intro i j
    have h := Measure.ae_ae_of_ae_prod hmk
    unfold HRS.Whole.r2WickCoeff
    refine integral_congr_ae ?_
    filter_upwards [h] with x hx
    refine integral_congr_ae ?_
    filter_upwards [hx] with y hy
    simp only [Function.uncurry_apply_pair] at hy
    simp only [hk', hy]
  have hsq : ∫ q, (k q.1 q.2) ^ 2 ∂(mu.prod mu) = ∫ q, (k' q.1 q.2) ^ 2 ∂(mu.prod mu) := by
    refine integral_congr_ae ?_
    filter_upwards [hmk] with q hq
    simp only [Function.uncurry] at hq
    simp only [hk', hq]
  rw [hsq]
  simp_rw [hcoef]
  exact HRS.MS.R2Chaos.s94_bessel ha.1 ha.2.1 hk'm hk'2 F

/-- The coordinates `(X (c, i))_i` of a centered Gaussian vector form a jointly Gaussian family. -/
theorem k4_gfam {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (m : ℕ)
    (X : Ω → (Fin 2 × Fin m) → ℝ) (hX : AEMeasurable X P) (hG : HRS.IsCenteredGaussian (P.map X))
    (c : Fin 2) :
    HRS.MS.R2Chaos.S94GFam P (fun i : Fin m => fun ω => X ω (c, i)) := by
  have hGa : IsGaussian (P.map X) := hG.1
  refine ⟨fun i => (measurable_pi_apply (c, i)).comp_aemeasurable hX, fun α => ?_⟩
  set L : StrongDual ℝ (Fin 2 × Fin m → ℝ) :=
    ∑ i, α i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 × Fin m => ℝ) (c, i) with hL
  have hLx : ∀ x, L x = ∑ i, α i * x (c, i) := fun x => by simp [hL]
  have h1 := IsGaussian.map_eq_gaussianReal (μ := P.map X) L
  have h0 : (P.map X)[L] = 0 := hG.2 L
  rw [h0] at h1
  refine ⟨(ProbabilityTheory.variance L (P.map X)).toNNReal, ?_⟩
  have h2 : P.map (fun ζ => ∑ i, α i * X ζ (c, i)) = (P.map X).map L := by
    rw [AEMeasurable.map_map_of_aemeasurable L.continuous.measurable.aemeasurable hX]
    congr 1
    ext ζ
    simp [hLx]
  rw [h2, h1]

end HRS.MS.S111K4
