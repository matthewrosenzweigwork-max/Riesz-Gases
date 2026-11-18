import HRS.MS.Fp81S21ErrorEnvelope

/-! Quantitative plumbing for the actual error supremum, with zero adjoined.
The proposed headers are expanded with explicit realization and test types.
The supplied O1 (and hence its Kb) is retained before all start/test binders;
no new Gaussian source or physical O1 package is selected here. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS.Whole HRS.MS.R26T3

/-- Every realization error in the quantitative expansion belongs to the set
whose supremum defines the envelope. O1 supplies its boundedness. -/
theorem fp81s21_errorEnvelope_quantitative
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (O1 : fp81s21_O1_gaussian_wick p.d p.s p.a p.β p.γ p.T R.ρ) :
    S21eExpBound p.d p.s p.a p.β p.γ R.ρ p.T (fp81s21_O1_kappa O1)
      (fp81s21_errorEnvelope p R (fp81s21_O1_kappa O1)) := by
  intro N hN Ω mΩ P hP X₀ W X hBr hInd hlaw hstrong Ω' mΩ' P' hP' Z hZ b hb Φ hΦ
  let A : Particle R N := {
    Ω := Ω
    mΩ := mΩ
    P := P
    prob := hP
    X₀ := X₀
    W := W
    X := X
    brownian := hBr
    independent := hInd
    initial := hlaw
    strong := hstrong }
  let G : GaussianRealization R := {
    Ω := Ω'
    mΩ := mΩ'
    P := P'
    prob := hP'
    Z := Z
    evolution := hZ }
  change r26t3_error (fp81s21_O1_kappa O1) A G b Φ ≤
    fp81s21_errorEnvelope p R (fp81s21_O1_kappa O1) N
  have hbd := fp81s21_errorValues_bddAbove p R O1 N hN
  apply le_csSup (hbd.insert 0)
  exact Set.mem_insert_of_mem 0 ⟨A, G, b, hb, Φ, hΦ, rfl⟩

/-- A uniform nonnegative bound for all actual errors bounds their envelope,
including the inserted zero. The bound precedes all realizations and tests. -/
theorem fp81s21_errorEnvelope_le_of_pointwise
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (O1 : fp81s21_O1_gaussian_wick p.d p.s p.a p.β p.γ p.T R.ρ)
    (N : ℕ) (_hN : 2 ≤ N) (B₀ : ℝ) (hB : 0 ≤ B₀)
    (hpoint : ∀ (A : Particle R N) (G : GaussianRealization R)
      (b : ℝ), 0 ≤ b → ∀ (Φ : Window p → ℝ),
      Φ ∈ CbUnitBall (Window p) 5 →
      r26t3_error (fp81s21_O1_kappa O1) A G b Φ ≤ B₀) :
    fp81s21_errorEnvelope p R (fp81s21_O1_kappa O1) N ≤ B₀ := by
  unfold fp81s21_errorEnvelope
  apply csSup_le
  · exact ⟨0, Set.mem_insert 0 _⟩
  · intro e he
    rcases he with rfl | he
    · exact hB
    · rcases he with ⟨A, G, b, hb, Φ, hΦ, rfl⟩
      exact hpoint A G b hb Φ hΦ

end HRS.Fp81.S21

end

#print axioms HRS.Fp81.S21.fp81s21_errorEnvelope_quantitative
#print axioms HRS.Fp81.S21.fp81s21_errorEnvelope_le_of_pointwise
