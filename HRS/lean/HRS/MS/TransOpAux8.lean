import HRS.MS.TransOpAux7

/-!
# S611 packet P2a: the translation operator on `Σ^m` (sequence model) from the `L²` translation

`s611_U c` is the unitary `F ↦ F(· + c)` of `L²(ℝ^d)` (`Lp.compMeasurePreservingₗᵢ`).  For `m ≥ 1` the operator
`s611_O m c : OscSpace d m →L[ℝ] OscSpace d m` has weighted coordinates `λ_β^{m/2} ⟨U_c F_w, h_β⟩` (`F_w` the `L²` class with Hermite
coefficients `hermiteCoeff w`); it is bounded by `s611_K m c` (`s611_U_bound`, from the function-level bound of `TransOpAux7`) and
intertwines with `φ ↦ φ(· + c)` on `Σ^m` functions (`s611_O_ofFun`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.TransOp

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

/-- A fixed Hermite Hilbert basis of `L²(ℝ^d)`. -/
def s611_basis (d : ℕ) : HilbertBasis (MultiIndex d) ℝ (Lp ℝ 2 (volume : Measure (Euc d))) :=
  (exists_hermiteHilbertBasisD (d := d)).choose

theorem s611_basis_apply (α : MultiIndex d) : s611_basis d α = hermiteLpD α :=
  (exists_hermiteHilbertBasisD (d := d)).choose_spec α

/-- The unitary translation `F ↦ F(· + c)` of `L²(ℝ^d)`. -/
def s611_U (c : Euc d) :
    Lp ℝ 2 (volume : Measure (Euc d)) →ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure (Euc d)) :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x => x + c) (measurePreserving_add_right volume c)

theorem s611_U_toLp {g : Euc d → ℝ} (hg : MemLp g 2 (volume : Measure (Euc d))) (c : Euc d) :
    s611_U c (hg.toLp g) = (s611_memLp_translate hg c).toLp (fun x => g (x + c)) := rfl

theorem s611_inner_toLp {g : Euc d → ℝ} (hg : MemLp g 2 (volume : Measure (Euc d))) (α : MultiIndex d) :
    inner ℝ (hermiteLpD α) (hg.toLp g) = hermiteCoeff g α :=
  OscSpace.inner_hermiteLpD_toLp g hg α

/-- Coefficients of a translated `L²` class. -/
theorem s611_inner_U (F : Lp ℝ 2 (volume : Measure (Euc d))) (c : Euc d) (α : MultiIndex d) :
    inner ℝ (hermiteLpD α) (s611_U c F) = hermiteCoeff (fun x => (F : Euc d → ℝ) (x + c)) α := by
  have h1 : F = (Lp.memLp F).toLp (F : Euc d → ℝ) := (Lp.toLp_coeFn F (Lp.memLp F)).symm
  rw [h1, s611_U_toLp, s611_inner_toLp]
  simp

theorem s611_inner_coe (F : Lp ℝ 2 (volume : Measure (Euc d))) (α : MultiIndex d) :
    inner ℝ (hermiteLpD α) F = hermiteCoeff (F : Euc d → ℝ) α := by
  have h1 : F = (Lp.memLp F).toLp (F : Euc d → ℝ) := (Lp.toLp_coeFn F (Lp.memLp F)).symm
  conv_lhs => rw [h1]
  exact s611_inner_toLp _ α

/-- The `Σ^m` bound for translated `L²` classes. -/
theorem s611_U_bound (m : ℕ) (hm : 1 ≤ m) (c : Euc d) (F : Lp ℝ 2 (volume : Measure (Euc d)))
    (hS : Summable (fun α => s611_w d m α * (inner ℝ (hermiteLpD α) F) ^ 2)) :
    Summable (fun α => s611_w d m α * (inner ℝ (hermiteLpD α) (s611_U c F)) ^ 2) ∧
      ∑' α, s611_w d m α * (inner ℝ (hermiteLpD α) (s611_U c F)) ^ 2 ≤
        s611_K m c ^ 2 * ∑' α, s611_w d m α * (inner ℝ (hermiteLpD α) F) ^ 2 := by
  simp only [s611_inner_U] at ⊢
  simp only [s611_inner_coe] at hS ⊢
  obtain ⟨h1, h2⟩ := s611_translate_sum_bound m hm c Finset.univ (Lp.memLp F) hS
  rw [s611_sum_e c] at h1 h2
  refine ⟨h1, h2.trans (le_of_eq ?_)⟩
  unfold s611_K
  rw [sq, ← Real.exp_add]
  congr 2
  ring

end HRS.MS.TransOp

end
