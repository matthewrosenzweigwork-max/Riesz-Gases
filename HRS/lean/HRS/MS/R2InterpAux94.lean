import HRS.MS.R2InterpAux93

/-!
# S10.2 (worker S10R), part 94 (packet F5i): the diffusion coefficient `Φc` of the Itô representation is progressive and bounded
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}

/-- The orbit of the `i`-th observation. -/
def s102_orb (C : WholeCoeff d) (m : ℝ) {T : ℝ} (hT : 0 < T) (L : ℕ) (i : Fin (s102_q d L)) : ℝ → Euc d → ℝ :=
  fun r => propagatorW C r (s102_tk hT L i) (oscTestFun m (s102_alk L i))

/-- The diffusion coefficient of the Itô representation, as an `E`-valued integrand. -/
def s102_PhicE (C : WholeCoeff d) (m : ℝ) {T : ℝ} (hT : 0 < T) (L : ℕ) {N : ℕ} {Ω : Type}
    (X : ℝ≥0 → Ω → EucConfig d N) : ℝ → Ω → (Fin N × Fin d) → EuclideanSpace ℝ (Fin (s102_q d L)) :=
  fun u ζ k => (EuclideanSpace.equiv (Fin (s102_q d L)) ℝ).symm fun i =>
    (Real.sqrt N * (Real.sqrt (2 * C.ν) / N)) * s102_Ig (s102_orb C m hT L i) (s102_tk hT L i) X u ζ k

theorem s102_PhicE_apply (C : WholeCoeff d) (m : ℝ) {T : ℝ} (hT : 0 < T) (L : ℕ) {N : ℕ} {Ω : Type}
    (X : ℝ≥0 → Ω → EucConfig d N) (u : ℝ) (ζ : Ω) (k : Fin N × Fin d) (i : Fin (s102_q d L)) :
    s102_PhicE C m hT L X u ζ k i = (Real.sqrt N * (Real.sqrt (2 * C.ν) / N)) *
      s102_Ig (s102_orb C m hT L i) (s102_tk hT L i) X u ζ k := rfl

theorem s102_PhicE_form (C : WholeCoeff d) (m : ℝ) {T : ℝ} (hT : 0 < T) (L : ℕ) {N : ℕ} {Ω : Type}
    (X : ℝ≥0 → Ω → EucConfig d N) (u : ℝ) (hu : 0 ≤ u) (ζ : Ω) (k : Fin N × Fin d) (i : Fin (s102_q d L)) :
    s102_PhicE C m hT L X u ζ k i = s102_Phic C m hT L X u ζ k i := by
  rw [s102_PhicE_apply]
  unfold s102_Phic s102_Ig s102_ot s102_orb
  by_cases h : u ≤ (s102_tauk hT L i : ℝ)
  · have h' : u ∈ Icc (0 : ℝ) (s102_tk hT L i) := ⟨hu, h⟩
    rw [if_pos h', if_pos h]
    simp only [gradComp, s102_tk]
    ring
  · have h' : u ∉ Icc (0 : ℝ) (s102_tk hT L i) := fun hh => h hh.2
    rw [if_neg h', if_neg h, s102_gradient_zero]
    simp

theorem s102_eucl_norm_le {q : ℕ} {B : ℝ} (hB : 0 ≤ B) (x : EuclideanSpace ℝ (Fin q)) (hx : ∀ i, |x i| ≤ B) :
    ‖x‖ ≤ Real.sqrt q * B := by
  rw [EuclideanSpace.norm_eq]
  calc Real.sqrt (∑ i, ‖x i‖ ^ 2) ≤ Real.sqrt (∑ _i : Fin q, B ^ 2) := by
        refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hx i) 2
    _ = Real.sqrt q * B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Real.sqrt_mul (Nat.cast_nonneg _),
          Real.sqrt_sq hB]

end HRS.MS.R2Interp

end
