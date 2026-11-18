import HRS.Main.ThermLin2Fu5

/-!
# THERMLIN2 Fu6: the orthogonality argument (abstract) and a jointly measurable modification of `Zw`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.Uniform.Q54c HRS.Uniform.Q45 Classical

section Orth

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Abstract orthogonality: if `X` is orthogonal to each `Fp r` with the same covariances as `∫ Fp r dr`, then
`X = ∫ Fp r dr` a.s. -/
theorem tl2fu_orth {t : ℝ} (Fp : ℝ → Ω → ℝ) (hFp : Measurable fun q : ℝ × Ω => Fp q.1 q.2)
    (M : ℝ) (hL2 : ∀ r ∈ Set.Icc (0 : ℝ) t, MemLp (Fp r) 2 P)
    (hM : ∀ r ∈ Set.Icc (0 : ℝ) t, ∫ ω, Fp r ω ^ 2 ∂P ≤ M)
    (X : Ω → ℝ) (hX : MemLp X 2 P) (hXm : Measurable X)
    (h1 : ∀ r ∈ Set.Icc (0 : ℝ) t,
      ∫ r' in Set.Icc (0 : ℝ) t, ∫ ω, Fp r' ω * Fp r ω ∂P = ∫ ω, X ω * Fp r ω ∂P)
    (h2 : ∫ ω, X ω * X ω ∂P = ∫ r in Set.Icc (0 : ℝ) t, ∫ ω, X ω * Fp r ω ∂P) :
    X =ᵐ[P] fun ω => ∫ r in Set.Icc (0 : ℝ) t, Fp r ω := by
  have hsq := tl2fu_Fp_sq_integrable (P := P) Fp hFp M hL2 hM
  have hBL := tl2fu_Bp_memLp (P := P) Fp hFp hsq
  have hBm : Measurable (fun ω => ∫ r in Set.Icc (0 : ℝ) t, Fp r ω) :=
    (hFp.stronglyMeasurable.integral_prod_left' (μ := volume.restrict (Set.Icc 0 t))).measurable
  set Bp : Ω → ℝ := fun ω => ∫ r in Set.Icc (0 : ℝ) t, Fp r ω with hBp
  have pXB : ∫ ω, Bp ω * X ω ∂P = ∫ r in Set.Icc (0 : ℝ) t, ∫ ω, X ω * Fp r ω ∂P := by
    rw [tl2fu_Bp_pair Fp hFp hsq X hX hXm]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [mul_comm]
  have pBB : ∫ ω, Bp ω * Bp ω ∂P = ∫ r in Set.Icc (0 : ℝ) t, ∫ ω, X ω * Fp r ω ∂P := by
    rw [tl2fu_Bp_pair Fp hFp hsq Bp hBL hBm]
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    have hFm : Measurable (Fp r) := hFp.comp measurable_prodMk_left
    have := tl2fu_Bp_pair Fp hFp hsq (Fp r) (hL2 r hr) hFm
    have e : ∫ ω, Fp r ω * Bp ω ∂P = ∫ ω, Bp ω * Fp r ω ∂P :=
      integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
    rw [e, this, ← h1 r hr]
  have hXB : Integrable (fun ω => X ω * Bp ω) P := hX.integrable_mul hBL
  have hXX : Integrable (fun ω => X ω * X ω) P := hX.integrable_mul hX
  have hBB : Integrable (fun ω => Bp ω * Bp ω) P := hBL.integrable_mul hBL
  have hz : ∫ ω, (X ω - Bp ω) ^ 2 ∂P = 0 := by
    have e : ∀ ω, (X ω - Bp ω) ^ 2 = X ω * X ω - 2 * (Bp ω * X ω) + Bp ω * Bp ω := fun ω => by ring
    have hBX : Integrable (fun ω => Bp ω * X ω) P := hBL.integrable_mul hX
    simp_rw [e]
    rw [integral_add (f := fun ω => X ω * X ω - 2 * (Bp ω * X ω)) (g := fun ω => Bp ω * Bp ω)
      (hXX.sub (hBX.const_mul 2)) hBB,
      integral_sub (f := fun ω => X ω * X ω) (g := fun ω => 2 * (Bp ω * X ω)) hXX (hBX.const_mul 2),
      integral_const_mul, pXB, pBB, h2]
    ring
  have hint : Integrable (fun ω => (X ω - Bp ω) ^ 2) P := (hX.sub hBL).integrable_sq
  have h0 := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hint).1 hz
  filter_upwards [h0] with ω hω
  have : (X ω - Bp ω) ^ 2 = 0 := hω
  exact sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 this)

end Orth

end HRS.ThermLin.Plan2
