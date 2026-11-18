import HRS.MS.Fp81S21GaussianQuadraticHilbert

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal BigOperators
open HRS HRS.MC.E213U13 HRS.MS.R26T6
namespace HRS.Fp81.S21

/-- The supplied coefficient field has finite polynomial approximants on the
same retained Gaussian sequence, at each nonnegative time. -/
theorem fp81s21_wick_coeff_L4_polynomials
    {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i))
    (T : ℝ → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P)
    (W : ℝ → Lp ℝ 2 (μ.prod μ) →L[ℝ] Lp ℝ 2 P)
    (k : ℕ → Lp ℝ 2 (μ.prod μ)) (q : ℝ → Ω → r26t6_Coeff)
    (K : ℝ)
    (hW : ∀ u, 0 ≤ u → ∃ hL : ‖T u‖ ≤ K,
      ∃ hJoint : ∀ r (v : Fin r → Lp ℝ 2 μ),
        IsCenteredGaussian (P.map fun ω => fun i => (T u (v i)) ω),
        W u = fp81s21_wickG_operator (T u) K hL hJoint)
    (hsrc : ∀ u, 0 ≤ u → ∀ f, InFirstChaos P ξ 2 (fun ω => T u f ω))
    (hq : ∀ u, 0 ≤ u → MemLp (q u) 2 P ∧
      ∀ j, (fun ω => q u ω j) =ᵐ[P] (fun ω => W u (k j) ω)) :
    ∀ u, 0 ≤ u → ∃ (N : ℕ → ℕ → ℕ) (c : ℕ → ℕ → ℕ → ℕ → ℝ),
      Tendsto (fun n => eLpNorm (fun ω =>
        (∑ j ∈ Finset.range n, quadSum (c n j) ξ (N n j) ω • fp81s21_coeffBasis j) - q u ω)
        4 P) atTop (𝓝 0) := by
  intro u hu
  obtain ⟨hL, hJoint, hWu⟩ := hW u hu
  obtain ⟨hqu, heq⟩ := hq u hu
  apply fp81s21_InQ2_coeff_L4_polynomials hξ (q u) hqu
  intro j
  apply InQ2.congr_ae (heq j).symm
  rw [hWu]
  exact fp81s21_wick_operator_InQ2 hξ hm (T u) K hL hJoint (hsrc u hu) (k j)

#print axioms fp81s21_wick_coeff_L4_polynomials
end HRS.Fp81.S21
end
