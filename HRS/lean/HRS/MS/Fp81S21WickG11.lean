import HRS.MS.Fp81S21WickG10
import HRS.MS.S21T4ProdQ

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace HRS.Fp81.S21

private theorem fp81s21_wickG_finite_sum_rearrange
    {m q : ℕ} (c : Fin m → Fin m → ℝ) (M : Fin m → Fin q → ℝ)
    (x : Fin q → Fin q → ℝ) :
    ∑ i, ∑ j, c i j * (∑ a, ∑ b, M i a * M j b * x a b) =
      ∑ a, ∑ b, (∑ i, ∑ j, c i j * M i a * M j b) * x a b := by
  classical
  calc
    ∑ i, ∑ j, c i j * (∑ a, ∑ b, M i a * M j b * x a b) =
        ∑ i, ∑ j, ∑ a, ∑ b, c i j * M i a * M j b * x a b := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          calc
            c i j * (∑ a, ∑ b, M i a * M j b * x a b) =
                ∑ a, c i j * (∑ b, M i a * M j b * x a b) := by
                  rw [Finset.mul_sum]
            _ = ∑ a, ∑ b, c i j * (M i a * M j b * x a b) := by
                  apply Finset.sum_congr rfl
                  intro a ha
                  rw [Finset.mul_sum]
            _ = ∑ a, ∑ b, c i j * M i a * M j b * x a b := by
                  apply Finset.sum_congr rfl
                  intro a ha
                  apply Finset.sum_congr rfl
                  intro b hb
                  ring
    _ =
        ∑ i, ∑ a, ∑ j, ∑ b, c i j * M i a * M j b * x a b := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_comm]
    _ = ∑ a, ∑ i, ∑ j, ∑ b, c i j * M i a * M j b * x a b := by
          rw [Finset.sum_comm]
    _ = ∑ a, ∑ i, ∑ b, ∑ j, c i j * M i a * M j b * x a b := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, ∑ i, ∑ j, c i j * M i a * M j b * x a b := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, (∑ i, ∑ j, c i j * M i a * M j b) * x a b := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          simp only [Finset.sum_mul]

/-- Changing a finite family to orthonormal coordinates preserves its
centered half-Wick polynomial, and the polynomial inherits the orthonormal
family estimate. -/
theorem fp81s21_wickG_finite_coordinate_change
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {m q : ℕ} (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P) (Kstar : ℝ)
    (hL : ‖L‖ ≤ Kstar)
    (hJoint : ∀ r (v : Fin r → Lp ℝ 2 μ),
      HRS.IsCenteredGaussian (P.map fun ω => fun i => (L (v i)) ω))
    (f : Fin m → Lp ℝ 2 μ) (e : Fin q → Lp ℝ 2 μ)
    (M : Fin m → Fin q → ℝ) (hf : Orthonormal ℝ e)
    (hdecomp : ∀ i, f i = ∑ a, M i a • e a)
    (c : Fin m → Fin m → ℝ) :
    let d : Fin q → Fin q → ℝ := fun a b =>
      ∑ i, ∑ j, c i j * M i a * M j b
    (fun ω => (1 / 2 : ℝ) * ∑ i, ∑ j, c i j *
      ((L (f i)) ω * (L (f j)) ω -
        ∫ ω', (L (f i)) ω' * (L (f j)) ω' ∂P)) =ᵐ[P]
      (fun ω => (1 / 2 : ℝ) * ∑ a, ∑ b, d a b *
        ((L (e a)) ω * (L (e b)) ω -
          ∫ ω', (L (e a)) ω' * (L (e b)) ω' ∂P)) ∧
    ∫ ω, ((1 / 2 : ℝ) * ∑ i, ∑ j, c i j *
      ((L (f i)) ω * (L (f j)) ω -
        ∫ ω', (L (f i)) ω' * (L (f j)) ω' ∂P)) ^ 2 ∂P ≤
      (1 / 2 : ℝ) * Kstar ^ 4 * ∑ a, ∑ b,
        (∑ i, ∑ j, c i j * M i a * M j b) ^ 2 := by
  classical
  dsimp
  let d : Fin q → Fin q → ℝ := fun a b =>
    ∑ i, ∑ j, c i j * M i a * M j b
  have hLsumLp : ∀ i, L (f i) = ∑ a, M i a • L (e a) := by
    intro i
    rw [hdecomp i]
    simp only [map_sum, map_smul]
  have hLsum : ∀ i, (L (f i)) =ᵐ[P]
      fun ω => ∑ a, M i a * (L (e a)) ω := by
    intro i
    have hs : (∑ a : Fin q, M i a • L (e a) : Lp ℝ 2 P) =ᵐ[P]
        fun ω => ∑ a, M i a * (L (e a)) ω := by
      have h1 : (∑ a : Fin q, M i a • L (e a) : Lp ℝ 2 P) =ᵐ[P]
          fun ω => ∑ a, (M i a • L (e a) : Lp ℝ 2 P) ω := by
        simpa using HRS.A33.a33_coeFn_sum (P := P) Finset.univ
          (fun a => M i a • L (e a))
      have h2 : ∀ᵐ ω ∂P, ∀ a : Fin q,
          (M i a • L (e a) : Lp ℝ 2 P) ω = M i a * (L (e a)) ω := by
        rw [ae_all_iff]
        intro a
        filter_upwards [Lp.coeFn_smul (M i a) (L (e a))] with ω hω
        simpa [smul_eq_mul] using hω
      filter_upwards [h1, h2] with ω hω hωa
      rw [hω]
      exact Finset.sum_congr rfl fun a _ => hωa a
    have hEq : (L (f i)) =ᵐ[P]
        (∑ a : Fin q, M i a • L (e a) : Lp ℝ 2 P) := by
      filter_upwards [ae_of_all P fun ω =>
        congrFun (congrArg (fun z : Lp ℝ 2 P => (z : Ω → ℝ)) (hLsumLp i)) ω]
        with ω hω
      exact hω
    filter_upwards [hEq, hs] with ω hω hωs
    exact hω.trans hωs
  have hprod : ∀ i j, (fun ω => (L (f i)) ω * (L (f j)) ω) =ᵐ[P]
      fun ω => ∑ a, ∑ b, M i a * M j b *
        ((L (e a)) ω * (L (e b)) ω) := by
    intro i j
    filter_upwards [hLsum i, hLsum j] with ω hi hj
    rw [hi, hj, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => by ring
  have hEprod : ∀ a, MemLp (fun ω => (L (e a)) ω) 2 P := by
    intro a
    exact Lp.memLp (L (e a))
  have hCov : ∀ i j,
      (∫ ω, (L (f i)) ω * (L (f j)) ω ∂P) =
        ∑ a, ∑ b, M i a * M j b *
          (∫ ω, (L (e a)) ω * (L (e b)) ω ∂P) := by
    intro i j
    calc
      ∫ ω, (L (f i)) ω * (L (f j)) ω ∂P =
          ∫ ω, (∑ a, M i a * (L (e a)) ω) *
            (∑ b, M j b * (L (e b)) ω) ∂P := by
              apply integral_congr_ae
              filter_upwards [hLsum i, hLsum j] with ω hi hj
              rw [hi, hj]
      _ = ∑ a, ∑ b, M i a * M j b *
            (∫ ω, (L (e a)) ω * (L (e b)) ω ∂P) := by
              exact HRS.MS.R26T3.s21t4_expand_integral P
                (fun a => (L (e a))) hEprod (M i) (M j)
  have hcenter : ∀ i j, (fun ω => (L (f i)) ω * (L (f j)) ω -
      ∫ ω', (L (f i)) ω' * (L (f j)) ω' ∂P) =ᵐ[P]
      fun ω => ∑ a, ∑ b, M i a * M j b *
        ((L (e a)) ω * (L (e b)) ω -
          ∫ ω', (L (e a)) ω' * (L (e b)) ω' ∂P) := by
    intro i j
    filter_upwards [hprod i j] with ω hω
    rw [hω, hCov i j]
    symm
    calc
      (∑ a, ∑ b, M i a * M j b *
          ((L (e a)) ω * (L (e b)) ω -
            ∫ ω', (L (e a)) ω' * (L (e b)) ω' ∂P)) =
        (∑ a, ∑ b, M i a * M j b * ((L (e a)) ω * (L (e b)) ω)) -
          ∑ a, ∑ b, M i a * M j b *
            (∫ ω', (L (e a)) ω' * (L (e b)) ω' ∂P) := by
              simp_rw [mul_sub, Finset.sum_sub_distrib]
      _ = _ := rfl
  have hW : (fun ω => (1 / 2 : ℝ) * ∑ i, ∑ j, c i j *
      ((L (f i)) ω * (L (f j)) ω -
        ∫ ω', (L (f i)) ω' * (L (f j)) ω' ∂P)) =ᵐ[P]
      fun ω => (1 / 2 : ℝ) * ∑ a, ∑ b, d a b *
        ((L (e a)) ω * (L (e b)) ω -
          ∫ ω', (L (e a)) ω' * (L (e b)) ω' ∂P) := by
    filter_upwards [ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => hcenter i j]
      with ω hω
    calc
      (1 / 2 : ℝ) * ∑ i, ∑ j, c i j *
          ((L (f i)) ω * (L (f j)) ω -
            ∫ ω', (L (f i)) ω' * (L (f j)) ω' ∂P) =
        (1 / 2 : ℝ) * ∑ i, ∑ j, c i j * (∑ a, ∑ b, M i a * M j b *
          ((L (e a)) ω * (L (e b)) ω -
            ∫ ω', (L (e a)) ω' * (L (e b)) ω' ∂P)) := by
              apply congrArg (fun r : ℝ => (1 / 2 : ℝ) * r)
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro j hj
              rw [hω i j]
      _ = (1 / 2 : ℝ) * ∑ a, ∑ b, d a b *
          ((L (e a)) ω * (L (e b)) ω -
            ∫ ω', (L (e a)) ω' * (L (e b)) ω' ∂P) := by
              apply congrArg (fun r : ℝ => (1 / 2 : ℝ) * r)
              simpa [d] using fp81s21_wickG_finite_sum_rearrange c M
                (fun a b => (L (e a)) ω * (L (e b)) ω -
                  ∫ ω', (L (e a)) ω' * (L (e b)) ω' ∂P)
  refine ⟨hW, ?_⟩
  rw [integral_congr_ae (hW.mono fun ω hω => congrArg (fun x : ℝ => x ^ 2) hω)]
  simpa [d] using fp81s21_wickG_orthonormal_family_bound
    L Kstar hL hJoint hf d

#print axioms fp81s21_wickG_finite_coordinate_change

end HRS.Fp81.S21

end
