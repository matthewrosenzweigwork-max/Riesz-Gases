import HRS.MS.S21G2_S11a

/-!
# S21H2, packet R26-T3.S10 (part A): the Hilbert space of a coercive symmetric form

For a Hilbert space `H` and a bounded symmetric operator `A` with `⟪x, A x⟫ ≥ c‖x‖²` (`c > 0`), the form `b(x,y) = ⟪x, A y⟫` makes the SAME vector space an inner product space `HB`
with an equivalent norm; it is complete and (for separable `H`) second countable.  `HB` is the Cameron-Martin space on which the isonormal field with covariance `b` lives
(no square root of `A` is needed).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.R26T3

universe u

structure S21H2Form (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  A : H →L[ℝ] H
  symm : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y)
  c : ℝ
  cpos : 0 < c
  coer : ∀ x, c * ‖x‖ ^ 2 ≤ inner ℝ x (A x)

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The same vector space with the inner product `b`. -/
def S21H2Form.HB (_F : S21H2Form H) : Type u := H

namespace S21H2Form

variable (F : S21H2Form H)

@[reducible] def toH (x : F.HB) : H := x

instance : AddCommGroup F.HB := inferInstanceAs (AddCommGroup H)
instance : Module ℝ F.HB := inferInstanceAs (Module ℝ H)

theorem toH_add (x y : F.HB) : F.toH (x + y) = F.toH x + F.toH y := rfl

theorem toH_smul (r : ℝ) (x : F.HB) : F.toH (r • x) = r • F.toH x := rfl

@[instance_reducible] def core : InnerProductSpace.Core ℝ F.HB where
  inner x y := inner ℝ (F.toH x) (F.A (F.toH y))
  conj_inner_symm x y := by
    show inner ℝ (F.toH y) (F.A (F.toH x)) = inner ℝ (F.toH x) (F.A (F.toH y))
    rw [real_inner_comm, F.symm]
  re_inner_nonneg x := by
    show 0 ≤ inner ℝ (F.toH x) (F.A (F.toH x))
    exact le_trans (by have := F.cpos; positivity) (F.coer _)
  add_left x y z := by
    show inner ℝ (F.toH (x + y)) (F.A (F.toH z)) = _
    rw [F.toH_add, inner_add_left]
  smul_left x y r := by
    show inner ℝ ((r : ℝ) • (F.toH x)) (F.A (F.toH y)) = _
    rw [real_inner_smul_left]; rfl
  definite x hx := by
    have h0 : inner ℝ (F.toH x) (F.A (F.toH x)) = 0 := hx
    have h1 := F.coer (F.toH x)
    rw [h0] at h1
    have hn : ‖(F.toH x)‖ ^ 2 ≤ 0 := by
      by_contra hn
      push Not at hn
      have := mul_pos F.cpos hn
      linarith
    have : ‖(F.toH x)‖ = 0 := by nlinarith [norm_nonneg (F.toH x)]
    exact norm_eq_zero.1 this

instance : NormedAddCommGroup F.HB := F.core.toNormedAddCommGroup
instance : InnerProductSpace ℝ F.HB := InnerProductSpace.ofCore F.core.toCore

theorem norm_sq (x : F.HB) : ‖x‖ ^ 2 = inner ℝ (F.toH x) (F.A (F.toH x)) := by
  rw [← real_inner_self_eq_norm_sq]; rfl

theorem inner_eq (x y : F.HB) : inner ℝ x y = inner ℝ (F.toH x) (F.A (F.toH y)) := rfl

/-- The identity `H → HB`. -/
@[reducible] def toB (x : H) : F.HB := x

theorem norm_toB_le (x : H) : ‖F.toB x‖ ≤ Real.sqrt ‖F.A‖ * ‖x‖ := by
  have h1 : ‖F.toB x‖ ^ 2 ≤ (Real.sqrt ‖F.A‖ * ‖x‖) ^ 2 := by
    rw [F.norm_sq, mul_pow, Real.sq_sqrt (norm_nonneg _)]
    calc inner ℝ x (F.A x) ≤ ‖x‖ * ‖F.A x‖ := real_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖F.A‖ * ‖x‖) := mul_le_mul_of_nonneg_left (F.A.le_opNorm x) (norm_nonneg _)
      _ = ‖F.A‖ * ‖x‖ ^ 2 := by ring
  exact (abs_le_of_sq_le_sq h1 (by positivity)).trans' (le_abs_self _)

theorem norm_le_toB (x : H) : Real.sqrt F.c * ‖x‖ ≤ ‖F.toB x‖ := by
  have h1 : (Real.sqrt F.c * ‖x‖) ^ 2 ≤ ‖F.toB x‖ ^ 2 := by
    rw [F.norm_sq, mul_pow, Real.sq_sqrt F.cpos.le]
    exact F.coer x
  exact (abs_le_of_sq_le_sq h1 (norm_nonneg _)).trans' (le_abs_self _)

theorem lipschitz_toB : LipschitzWith (Real.sqrt ‖F.A‖).toNNReal F.toB := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  exact F.norm_toB_le (x - y)

theorem antilipschitz_toB : AntilipschitzWith (Real.sqrt F.c)⁻¹.toNNReal F.toB := by
  have hs : 0 < Real.sqrt F.c := Real.sqrt_pos.2 F.cpos
  refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (inv_nonneg.2 hs.le)]
  have := F.norm_le_toB (x - y)
  have e : F.toB x - F.toB y = F.toB (x - y) := rfl
  rw [e, inv_mul_eq_div, le_div_iff₀ hs, mul_comm]
  exact this

variable [CompleteSpace H] [SecondCountableTopology H]

instance : CompleteSpace F.HB := by
  refine completeSpace_of_isComplete_univ ?_
  have h := (F.antilipschitz_toB).isComplete_range F.lipschitz_toB.uniformContinuous
  have hr : Set.range F.toB = Set.univ := Set.range_eq_univ.2 fun x => ⟨x, rfl⟩
  rwa [hr] at h

instance : SecondCountableTopology F.HB := by
  have : TopologicalSpace.SeparableSpace H := inferInstance
  have : TopologicalSpace.SeparableSpace F.HB :=
    DenseRange.separableSpace (f := F.toB) (Function.Surjective.denseRange fun x => ⟨x, rfl⟩)
      F.lipschitz_toB.continuous
  exact UniformSpace.secondCountable_of_separable _

end S21H2Form

end HRS.MS.R26T3
