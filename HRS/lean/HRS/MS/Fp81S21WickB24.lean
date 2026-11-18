import HRS.MS.Fp81S21WickB23

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open HRS (Euc)
open HRS.Whole

namespace HRS.Fp81.S21

/-- The pointwise symmetric representative obtained by averaging an `L²`
product kernel with its coordinate swap. -/
def fp81s21_wickB24_symmRepresentative {d : ℕ}
    {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    (k : Lp ℝ 2 (μ.prod μ)) (z : Euc d × Euc d) : ℝ :=
  (1 / 2 : ℝ) * (k z + k z.swap)

theorem fp81s21_wickB24_symmRepresentative_memLp {d : ℕ}
    {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    (k : Lp ℝ 2 (μ.prod μ)) :
    MemLp (fp81s21_wickB24_symmRepresentative k) 2 (μ.prod μ) := by
  let hmp : MeasurePreserving (Prod.swap : Euc d × Euc d → Euc d × Euc d)
      (μ.prod μ) (μ.prod μ) :=
    Measure.measurePreserving_swap (μ := μ) (ν := μ)
  have hk : MemLp (fun z : Euc d × Euc d => k z) 2 (μ.prod μ) := Lp.memLp k
  have hswap : MemLp (fun z : Euc d × Euc d => k z.swap) 2 (μ.prod μ) := by
    convert hk.comp_measurePreserving hmp using 1 <;> rfl
  exact (hk.add hswap).const_mul (1 / 2 : ℝ)

theorem fp81s21_wickB24_symmRepresentative_symmetric {d : ℕ}
    {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    (k : Lp ℝ 2 (μ.prod μ)) (x y : Euc d) :
    fp81s21_wickB24_symmRepresentative k (x, y) =
      fp81s21_wickB24_symmRepresentative k (y, x) := by
  simp [fp81s21_wickB24_symmRepresentative, Prod.swap_prod_mk, add_comm]

theorem fp81s21_wickB24_symmRepresentative_toLp_eq_symmetrize {d : ℕ}
    {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    (k : Lp ℝ 2 (μ.prod μ)) :
    (fp81s21_wickB24_symmRepresentative_memLp k).toLp
      (fp81s21_wickB24_symmRepresentative k) =
        fp81s21_wickB23_symmetrize μ k := by
  apply Lp.ext
  have hswap := fp81s21_wickB23_swapLp_ae μ k
  have hadd := Lp.coeFn_add k (fp81s21_wickB23_swapLp μ k)
  have hsmul := Lp.coeFn_smul (1 / 2 : ℝ)
    (k + fp81s21_wickB23_swapLp μ k)
  have hrep := (fp81s21_wickB24_symmRepresentative_memLp k).coeFn_toLp
  filter_upwards [hswap, hadd, hsmul, hrep] with z hswap' hadd' hsmul' hrep'
  rw [hrep']
  change fp81s21_wickB24_symmRepresentative k z =
    fp81s21_wickB23_symmetrize μ k z
  rw [fp81s21_wickB23_symmetrize_apply, hsmul']
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hadd']
  simp only [Pi.add_apply]
  rw [hswap']
  rfl

/-- Symmetric finite-rank kernels are dense on the fixed-point subspace of `S`.
The approximating theorem is precisely PROS13's pointwise-symmetric form;
the canonical representative above turns any fixed `L²` class into such an
input. -/
theorem fp81s21_wickB24_symmetric_range_dense {d : ℕ}
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (k : Lp ℝ 2 (μ.prod μ))
    (hfixed : fp81s21_wickB23_symmetrize μ k = k)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (c : Fin m → Fin m → ℝ) (u : Fin m → Euc d → ℝ),
      IsR2FiniteRankData c u ∧
      eLpNorm
        (fun z : Euc d × Euc d =>
          r2FiniteRankKernel c u z.1 z.2 -
            fp81s21_wickB24_symmRepresentative k z)
        2 (μ.prod μ) ≤ ENNReal.ofReal ε ∧
      (fp81s21_wickB24_symmRepresentative_memLp k).toLp
        (fp81s21_wickB24_symmRepresentative k) = k := by
  let h : Euc d → Euc d → ℝ := fun x y =>
    fp81s21_wickB24_symmRepresentative k (x, y)
  have hh : MemLp (fun z : Euc d × Euc d => h z.1 z.2)
      2 (μ.prod μ) := by
    simpa only [h] using fp81s21_wickB24_symmRepresentative_memLp k
  have hsym : ∀ x y, h x y = h y x := by
    intro x y
    exact fp81s21_wickB24_symmRepresentative_symmetric k x y
  obtain ⟨m, c, u, hdata, happ⟩ :=
    fp81s21_wickB23_symmetric_finite_rank_approx μ h hh hsym ε hε
  refine ⟨m, c, u, hdata, ?_, ?_⟩
  · simpa only [h] using happ
  · rw [fp81s21_wickB24_symmRepresentative_toLp_eq_symmetrize, hfixed]

#print axioms fp81s21_wickB24_symmRepresentative_memLp
#print axioms fp81s21_wickB24_symmRepresentative_toLp_eq_symmetrize
#print axioms fp81s21_wickB24_symmetric_range_dense

end HRS.Fp81.S21

end
