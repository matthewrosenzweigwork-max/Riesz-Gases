import HRS.MS.Fp81S21WickG5

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace HRS.Fp81.S21

/-- Second moment of a finite half-Wick sum from its centered product
covariances.  The order of the four dummy binders follows the two nested
finite sums produced by expanding the square. -/
theorem fp81s21_wickG_finite_weighted_second_moment
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (q : Fin n → Fin n → Ω → ℝ)
    (hq : ∀ i j, MemLp (q i j) 2 P)
    (C : Fin n → Fin n → ℝ)
    (hpair : ∀ i j k l, ∫ ω, q i j ω * q k l ω ∂P =
      C i k * C j l + C i l * C j k)
    (d : Fin n → Fin n → ℝ) :
    ∫ ω, ((1 / 2 : ℝ) * ∑ i, ∑ j, d i j * q i j ω) ^ 2 ∂P =
      (1 / 4 : ℝ) * ∑ i, ∑ k, ∑ j, ∑ l,
        (d i j * d k l) * (C i k * C j l + C i l * C j k) := by
  classical
  let S : Ω → ℝ := fun ω => ∑ i, ∑ j, d i j * q i j ω
  have hSrow : ∀ i, MemLp (fun ω => ∑ j, d i j * q i j ω) 2 P := by
    intro i
    exact memLp_finsetSum (f := fun j ω => d i j * q i j ω) Finset.univ
      fun j _ => (hq i j).const_mul (d i j)
  have hS : MemLp S 2 P := by
    exact memLp_finsetSum (f := fun i ω => ∑ j, d i j * q i j ω) Finset.univ
      fun i _ => hSrow i
  have hSsq : Integrable (fun ω => S ω ^ 2) P := hS.integrable_sq
  have hpairInt : ∀ i j k l, Integrable (fun ω => q i j ω * q k l ω) P := by
    intro i j k l
    exact (hq i j).integrable_mul (hq k l)
  have hcoeffInt : ∀ i k j l, Integrable
      (fun ω => (d i j * d k l) * (q i j ω * q k l ω)) P := by
    intro i k j l
    exact (hpairInt i j k l).const_mul (d i j * d k l)
  have hsquare : ∀ ω, S ω ^ 2 =
      ∑ i, ∑ k, ∑ j, ∑ l,
        (d i j * d k l) * (q i j ω * q k l ω) := by
    intro ω
    dsimp [S]
    rw [sq, Finset.sum_mul_sum]
    simp_rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have hIntExpand : ∫ ω, S ω ^ 2 ∂P =
      ∑ i, ∑ k, ∑ j, ∑ l,
        (d i j * d k l) * (∫ ω, q i j ω * q k l ω ∂P) := by
    rw [integral_congr_ae (ae_of_all _ hsquare)]
    rw [integral_finset_sum _ (fun i _ => integrable_finsetSum _ fun k _ =>
      integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => hcoeffInt i k j l)]
    simp_rw [integral_finset_sum _ (fun k _ => integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun l _ => hcoeffInt _ k j l)]
    simp_rw [integral_finset_sum _ (fun j _ => integrable_finsetSum _ fun l _ => hcoeffInt _ _ j l)]
    simp_rw [integral_finset_sum _ (fun l _ => hcoeffInt _ _ _ l), integral_const_mul]
  have hsumPair :
      (∑ i, ∑ k, ∑ j, ∑ l,
        (d i j * d k l) * (∫ ω, q i j ω * q k l ω ∂P)) =
      ∑ i, ∑ k, ∑ j, ∑ l,
        (d i j * d k l) * (C i k * C j l + C i l * C j k) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hpair i j k l]
  have hfun : (fun ω => ((1 / 2 : ℝ) * S ω) ^ 2) =
      fun ω => (1 / 4 : ℝ) * S ω ^ 2 := by
    funext ω
    ring
  calc
    ∫ ω, ((1 / 2 : ℝ) * ∑ i, ∑ j, d i j * q i j ω) ^ 2 ∂P =
        (1 / 4 : ℝ) * ∫ ω, S ω ^ 2 ∂P := by
          rw [show (fun ω => ((1 / 2 : ℝ) * ∑ i, ∑ j, d i j * q i j ω) ^ 2) =
            fun ω => ((1 / 2 : ℝ) * S ω) ^ 2 from by
              funext ω
              rfl,
            hfun, integral_const_mul]
    _ = (1 / 4 : ℝ) * ∑ i, ∑ k, ∑ j, ∑ l,
        (d i j * d k l) * (∫ ω, q i j ω * q k l ω ∂P) := by rw [hIntExpand]
    _ = (1 / 4 : ℝ) * ∑ i, ∑ k, ∑ j, ∑ l,
        (d i j * d k l) * (C i k * C j l + C i l * C j k) := by rw [hsumPair]

#print axioms fp81s21_wickG_finite_weighted_second_moment

end HRS.Fp81.S21

end
