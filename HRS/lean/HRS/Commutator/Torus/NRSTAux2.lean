import HRS.Commutator.Torus.NRSTAux1

/-!
# NRS-T, part 2: evaluation of trigonometric polynomials as functions on `𝕋^d`

`ev f (x) = ∑_k f(k) e_k(x)` is a ring homomorphism `ℂ[ℤ^d] → C(𝕋^d, ℂ)`, `∫ ev f = f(0)`, Parseval for
polynomials, and `∂_a` corresponds to differentiation of the periodic lift.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace HRS.Commutator.TorusNote.NRST

open HRS

variable {d : ℕ}

/-- The function on the torus represented by a trigonometric polynomial. -/
def ev (f : TPA d) (x : Torus d) : ℂ := f.coeff.sum fun k c => c * Torus.mode k x

lemma ev_add (f g : TPA d) : ev (f + g) = ev f + ev g := by
  funext x
  unfold ev
  rw [AddMonoidAlgebra.coeff_add]
  exact Finsupp.sum_add_index' (fun k => by simp) (fun k a b => by ring)

lemma ev_zero : ev (0 : TPA d) = 0 := by
  funext x; simp [ev]

lemma ev_single (k : Lattice d) (c : ℂ) (x : Torus d) :
    ev (AddMonoidAlgebra.single k c) x = c * Torus.mode k x := by
  unfold ev
  rw [AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index (by simp)]

lemma ev_mul (f g : TPA d) : ev (f * g) = ev f * ev g := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp [ev_zero]
  | add f1 f2 h1 h2 => rw [add_mul, ev_add, ev_add, h1, h2, add_mul]
  | single k x =>
    induction g using AddMonoidAlgebra.induction_linear with
    | zero => simp [ev_zero]
    | add g1 g2 h1 h2 => rw [mul_add, ev_add, ev_add, h1, h2, mul_add]
    | single l y =>
      funext z
      rw [AddMonoidAlgebra.single_mul_single, ev_single, Pi.mul_apply, ev_single, ev_single,
        Torus.mode_add]
      ring

lemma ev_sum {ι : Type*} (s : Finset ι) (F : ι → TPA d) : ev (∑ i ∈ s, F i) = ∑ i ∈ s, ev (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ev_zero]
  | insert x s hx ih => rw [Finset.sum_insert hx, ev_add, ih, Finset.sum_insert hx]

lemma ev_apply_sum (f : TPA d) (x : Torus d) :
    ev f x = ∑ k ∈ f.coeff.support, f.coeff k * Torus.mode k x := rfl

lemma continuous_ev (f : TPA d) : Continuous (ev f) := by
  have : ev f = fun x => ∑ k ∈ f.coeff.support, f.coeff k * Torus.mode k x := rfl
  rw [this]
  exact continuous_finset_sum _ fun k _ => continuous_const.mul (Torus.continuous_mode k)

lemma integral_ev (f : TPA d) : ∫ x, ev f x = f.coeff 0 := by
  have : ev f = fun x => ∑ k ∈ f.coeff.support, f.coeff k * Torus.mode k x := rfl
  rw [this, integral_finset_sum _ fun k _ => (Torus.integrable_mode k).const_mul _]
  simp_rw [integral_const_mul, Torus.integral_mode]
  simp [Finset.sum_ite_eq', Finsupp.mem_support_iff]
  intro h; simp [h]

lemma ev_coeff (f : TPA d) (k : Lattice d) :
    ∫ x, Torus.mode (-k) x * ev f x = f.coeff k := by
  have h := integral_ev (AddMonoidAlgebra.single (-k) 1 * f)
  rw [ev_mul] at h
  simp_rw [Pi.mul_apply, ev_single, one_mul] at h
  rw [h, AddMonoidAlgebra.coeff_single_mul_apply]
  simp

/-- Parseval for trigonometric polynomials. -/
lemma integral_ev_mul_conj (f : TPA d) :
    ∫ x, ‖ev f x‖ ^ 2 = ∑ k ∈ f.coeff.support, ‖f.coeff k‖ ^ 2 := by
  classical
  set S := f.coeff.support with hS
  have h : ∀ x : Torus d, (((‖ev f x‖ ^ 2 : ℝ)) : ℂ) =
      ∑ k ∈ S, ∑ l ∈ S, (f.coeff k * (starRingEnd ℂ) (f.coeff l)) * (Torus.mode k x * Torus.mode (-l) x) := by
    intro x
    rw [show (((‖ev f x‖ ^ 2 : ℝ)) : ℂ) = ev f x * (starRingEnd ℂ) (ev f x) by
      rw [Complex.mul_conj']; push_cast; ring]
    rw [ev_apply_sum, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, Torus.mode_neg]
    ring
  have h2 : (((∫ x, ‖ev f x‖ ^ 2 : ℝ)) : ℂ) = ((∑ k ∈ S, ‖f.coeff k‖ ^ 2 : ℝ) : ℂ) := by
    have h0 := integral_complex_ofReal (μ := (volume : Measure (Torus d)))
      (f := fun x : Torus d => ‖ev f x‖ ^ 2)
    rw [← h0]
    simp_rw [h]
    rw [integral_finset_sum _ fun k _ => integrable_finset_sum _ fun l _ =>
      (Torus.integrable_mode_mul k (-l)).const_mul _]
    have : ∀ k ∈ S, ∫ x : Torus d, ∑ l ∈ S, (f.coeff k * (starRingEnd ℂ) (f.coeff l)) *
        (Torus.mode k x * Torus.mode (-l) x) = ((‖f.coeff k‖ ^ 2 : ℝ) : ℂ) := by
      intro k hk
      rw [integral_finset_sum _ fun l _ => (Torus.integrable_mode_mul k (-l)).const_mul _]
      simp_rw [integral_const_mul, Torus.integral_mode_mul]
      have : ∀ l ∈ S, (f.coeff k * (starRingEnd ℂ) (f.coeff l)) * (if k + -l = 0 then (1:ℂ) else 0) =
          if l = k then f.coeff k * (starRingEnd ℂ) (f.coeff k) else 0 := by
        intro l _
        by_cases hl : l = k
        · subst hl; simp
        · have h3 : k + -l ≠ 0 := fun h => hl (add_neg_eq_zero.1 h).symm
          simp [h3, hl]
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' S k, if_pos hk, Complex.mul_conj']
      push_cast; ring
    rw [Finset.sum_congr rfl this]
    push_cast; rfl
  exact_mod_cast h2

end HRS.Commutator.TorusNote.NRST
