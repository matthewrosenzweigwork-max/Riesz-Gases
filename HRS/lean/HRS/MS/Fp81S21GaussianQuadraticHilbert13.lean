import HRS.MS.Fp81S21GaussianQuadraticHilbert12

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal BigOperators RealInnerProductSpace
open HRS HRS.MC.E213U13 HRS.MS.R26T6
namespace HRS.Fp81.S21

local instance fp81s21_GaussianQuadraticHilbert13_inst1 (H : ℝ) : MeasurableSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := borel _
local instance fp81s21_GaussianQuadraticHilbert13_inst2 (H : ℝ) : BorelSpace
    (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- Conditional same-source quadratic lift for the supplied Wick operator,
its specified coefficient field, and its specified finite-horizon histories. -/
theorem fp81s21_wick_history_uniform_L4_polynomials
    {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i))
    (T : ℝ → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P)
    (W : ℝ → Lp ℝ 2 (μ.prod μ) →L[ℝ] Lp ℝ 2 P)
    (k : ℕ → Lp ℝ 2 (μ.prod μ)) (q : ℝ → Ω → r26t6_Coeff)
    (K M H : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (U : ℝ → Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)))
    (hW : ∀ u, 0 ≤ u → ∃ hL : ‖T u‖ ≤ K,
      ∃ hJoint : ∀ r (v : Fin r → Lp ℝ 2 μ),
        IsCenteredGaussian (P.map fun ω => fun i => (T u (v i)) ω),
        W u = fp81s21_wickG_operator (T u) K hL hJoint)
    (hsrc : ∀ u, 0 ≤ u → ∀ f, InFirstChaos P ξ 2 (fun ω => T u f ω))
    (hq : ∀ u, 0 ≤ u → MemLp (q u) 2 P ∧
      (∫ ω, ‖q u ω‖ ^ 2 ∂P) ≤ M ∧
      ∀ j, (fun ω => q u ω j) =ᵐ[P] (fun ω => W u (k j) ω))
    (hqmeas : Measurable (Function.uncurry q))
    (hrep : ∀ a, 0 ≤ a → fp81s21_TimeL2Rep P q M a H (U a)) :
    ∃ Cq CH : ℝ, 0 ≤ Cq ∧ 0 ≤ CH ∧ ∀ a, 0 ≤ a →
      MemLp (q a) 4 P ∧ (∫ ω, ‖q a ω‖ ^ 4 ∂P) ≤ Cq ∧
      MemLp (U a) 4 P ∧ (∫ ω, ‖U a ω‖ ^ 4 ∂P) ≤ CH ∧
      ∃ (ι : Type) (b : HilbertBasis ι ℝ
          (Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H))))
        (S : ℕ → Finset ι) (N : ℕ → ι → ℕ) (c : ℕ → ι → ℕ → ℕ → ℝ),
        Tendsto (fun n => eLpNorm (fun ω =>
          (∑ s ∈ S n, quadSum (c n s) ξ (N n s) ω • b s) - U a ω) 4 P)
          atTop (𝓝 0) := by
  have hcoord : ∀ u, 0 ≤ u → MemLp (q u) 2 P ∧
      ∀ j, InQ2 hξ (fun ω => q u ω j) := by
    intro u hu
    obtain ⟨hL, hJoint, hWu⟩ := hW u hu
    obtain ⟨hqu, _, heq⟩ := hq u hu
    refine ⟨hqu, ?_⟩
    intro j
    apply InQ2.congr_ae (heq j).symm
    rw [hWu]
    exact fp81s21_wick_operator_InQ2 hξ hm (T u) K hL hJoint (hsrc u hu) (k j)
  obtain ⟨Cq, hCq, hq4⟩ := fp81s21_wick_coeff_uniform_fourth hξ hm T W k q K M hM hW hsrc hq
  obtain ⟨CH, hCH, hU4⟩ := fp81s21_TimeL2Rep_uniform_L4_polynomials hξ q M H hM hH U hqmeas hrep hcoord
  refine ⟨Cq, CH, hCq, hCH, ?_⟩
  intro a ha
  obtain ⟨hqmem, hqb⟩ := hq4 a ha
  obtain ⟨hUmem, hUb, hp⟩ := hU4 a ha
  exact ⟨hqmem, hqb, hUmem, hUb, hp⟩

#print axioms fp81s21_wick_history_uniform_L4_polynomials
end HRS.Fp81.S21
end
