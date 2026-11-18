import HRS.MS.Fp81S21WickMomRep3
import HRS.MS.ProClosureS111ChartSections

/-! Finite chart sections agree with the kernel operator. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter
open scoped ENNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- Coordinate agreement implies agreement on every finite chart section.
The kernel is the actual commutator kernel, with the same positive operator
convention as the given coordinates. -/
theorem fp81s21_wick_chartSection_agreement
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (E : r26t6_WeightedChart d r Pw) (s : ℝ)
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Lp ℝ 2 (μ.prod μ) →L[ℝ] Lp ℝ 2 P)
    (hk : ∀ j, MemLp (fun xy : Euc d × Euc d =>
      commutatorKernel d s (gradient (E.test j)) xy.1 xy.2) 2 (μ.prod μ))
    (q : Ω → r26t6_Coeff)
    (hcoord : ∀ j, (fun ω => q ω j) =ᵐ[P]
      (W ((hk j).toLp (fun xy : Euc d × Euc d =>
        commutatorKernel d s (gradient (E.test j)) xy.1 xy.2)) : Ω → ℝ))
    (c : r26t6_Coeff) (n : ℕ)
    (hsection : MemLp (fun xy : Euc d × Euc d =>
      commutatorKernel d s (gradient (chartSection E c n : Euc d → ℝ)) xy.1 xy.2)
      2 (μ.prod μ)) :
    (fun ω => inner ℝ (q ω) (coeffSection c n)) =ᵐ[P]
      (W (hsection.toLp (fun xy : Euc d × Euc d =>
        commutatorKernel d s (gradient (chartSection E c n : Euc d → ℝ)) xy.1 xy.2)) : Ω → ℝ) := by
  let v : ℕ → Lp ℝ 2 (μ.prod μ) := fun j => (hk j).toLp
    (fun xy : Euc d × Euc d => commutatorKernel d s (gradient (E.test j)) xy.1 xy.2)
  let S : Lp ℝ 2 (μ.prod μ) := ∑ j ∈ Finset.range n, c j • v j
  have hS : S = hsection.toLp (fun xy : Euc d × Euc d =>
      commutatorKernel d s (gradient (chartSection E c n : Euc d → ℝ)) xy.1 xy.2) := by
    apply Lp.ext
    have hsum : (S : Euc d × Euc d → ℝ) =ᵐ[μ.prod μ]
        fun xy => ∑ j ∈ Finset.range n, (c j • v j) xy := by
      simpa [S] using HRS.A33.a33_coeFn_sum (P := μ.prod μ)
        (Finset.range n) (fun j => c j • v j)
    have hv : ∀ᵐ xy ∂(μ.prod μ), ∀ j,
        (c j • v j) xy = c j * commutatorKernel d s (gradient (E.test j)) xy.1 xy.2 := by
      rw [ae_all_iff]
      intro j
      filter_upwards [Lp.coeFn_smul (c j) (v j), (hk j).coeFn_toLp] with xy ha hb
      simpa [smul_eq_mul, v, hb] using ha
    filter_upwards [hsum, hv, hsection.coeFn_toLp] with xy ha hb hc
    rw [ha, hc, chartSection_commutator]
    exact Finset.sum_congr rfl fun j _ => hb j
  have hsum : (W S : Ω → ℝ) =ᵐ[P] fun ω =>
      ∑ j ∈ Finset.range n, (c j • W (v j)) ω := by
    simpa [S, map_sum, map_smul] using HRS.A33.a33_coeFn_sum (P := P)
      (Finset.range n) (fun j => c j • W (v j))
  have hterms : ∀ᵐ ω ∂P, ∀ j, (c j • W (v j)) ω = c j * q ω j := by
    rw [ae_all_iff]
    intro j
    filter_upwards [Lp.coeFn_smul (c j) (W (v j)), hcoord j] with ω ha hb
    simpa [smul_eq_mul, v, hb] using ha
  filter_upwards [hsum, hterms] with ω ha hb
  rw [inner_coeffSection, ← hS, ha]
  exact Finset.sum_congr rfl fun j _ => (hb j).symm

#print axioms fp81s21_wick_chartSection_agreement
end HRS.Fp81.S21
end
