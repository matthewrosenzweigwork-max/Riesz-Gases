import HRS.MS.Fp81S21WickFam13

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21

local instance fp81s21_wickFam14_fact_one_le_four : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Finite half-Wick polynomials of continuous L⁴ families have continuous
L² classes. -/
theorem fp81s21_wickFam_polynomial_L4_continuous
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Set ℝ) {n : ℕ} (F : Fin n → ℝ → Lp ℝ 4 P)
    (hF : ∀ i, ContinuousOn (F i) S) (c : Fin n → Fin n → ℝ) :
    ∃ W : ℝ → Lp ℝ 2 P, ContinuousOn W S ∧ ∀ u ∈ S,
      (W u : Ω → ℝ) =ᵐ[P] fun ω => (1 / 2 : ℝ) * ∑ i, ∑ j, c i j *
        (F i u ω * F j u ω - ∫ ω', F i u ω' * F j u ω' ∂P) := by
  classical
  let ex (i j : Fin n) := fp81s21_wickFam_centered_product_continuous P S
    (F i) (F j) (hF i) (hF j)
  let Q : Fin n → Fin n → ℝ → Lp ℝ 2 P := fun i j => Classical.choose (ex i j)
  have hQ (i j : Fin n) : ContinuousOn (Q i j) S ∧ ∀ u ∈ S,
      (Q i j u : Ω → ℝ) =ᵐ[P] fun ω => F i u ω * F j u ω -
        ∫ ω', F i u ω' * F j u ω' ∂P := Classical.choose_spec (ex i j)
  let R : Fin n → ℝ → Lp ℝ 2 P := fun i u => ∑ j, c i j • Q i j u
  let W : ℝ → Lp ℝ 2 P := fun u => (1 / 2 : ℝ) • ∑ i, R i u
  have hR (i : Fin n) : ContinuousOn (R i) S := by
    apply continuousOn_finset_sum
    intro j hj
    exact (hQ i j).1.const_smul (c i j)
  have hsum : ContinuousOn (fun u => ∑ i : Fin n, R i u) S :=
    continuousOn_finset_sum Finset.univ (fun i _ => hR i)
  have hW : ContinuousOn W S := by
    change ContinuousOn (fun u => (1 / 2 : ℝ) • ∑ i : Fin n, R i u) S
    exact hsum.const_smul (1 / 2 : ℝ)
  refine ⟨W, hW, ?_⟩
  intro u hu
  have hrow : ∀ᵐ ω ∂P, ∀ i : Fin n, (R i u : Ω → ℝ) ω =
      ∑ j, c i j * (F i u ω * F j u ω - ∫ ω', F i u ω' * F j u ω' ∂P) := by
    rw [ae_all_iff]
    intro i
    have hs : (R i u : Ω → ℝ) =ᵐ[P] fun ω => ∑ j, (c i j • Q i j u : Lp ℝ 2 P) ω := by
      simpa [R] using HRS.A33.a33_coeFn_sum (P := P) Finset.univ (fun j => c i j • Q i j u)
    have hm : ∀ᵐ ω ∂P, ∀ j : Fin n, (c i j • Q i j u : Lp ℝ 2 P) ω =
        c i j * (F i u ω * F j u ω - ∫ ω', F i u ω' * F j u ω' ∂P) := by
      rw [ae_all_iff]
      intro j
      filter_upwards [Lp.coeFn_smul (c i j) (Q i j u), (hQ i j).2 u hu] with ω ha hb
      simpa [smul_eq_mul, hb] using ha
    filter_upwards [hs, hm] with ω ha hb
    rw [ha]
    exact Finset.sum_congr rfl fun j _ => hb j
  have hsum : ((∑ i, R i u : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P]
      fun ω => ∑ i, (R i u : Ω → ℝ) ω := by
    simpa using HRS.A33.a33_coeFn_sum (P := P) Finset.univ (fun i => R i u)
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (∑ i, R i u), hsum, hrow] with ω ha hb hc
  simp only [W, ha, Pi.smul_apply, smul_eq_mul, hb]
  congr 1
  exact Finset.sum_congr rfl fun i _ => hc i

#print axioms fp81s21_wickFam_polynomial_L4_continuous
end HRS.Fp81.S21
end
