import HRS.MS.TransOpAux5

/-!
# S611 packet P1f: `Σ^m` bound for translations

`s611_memOsc_translate`: for `m ≥ 1` and `c ∈ ℝ^d`, `φ ∈ Σ^m ⇒ φ(· + c) ∈ Σ^m` and
`‖φ(· + c)‖_{Σ^m} ≤ exp(m 3^m ∑_j |c_j|) ‖φ‖_{Σ^m}`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.TransOp

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s611_axis_bound (m : ℕ) (hm : 1 ≤ m) (i : Fin d) {f : Euc d → ℝ}
    (hf : MemLp f 2 (volume : Measure (Euc d)))
    (hS : Summable (fun α => s611_w d m α * hermiteCoeff f α ^ 2)) (t : ℝ) :
    Summable (fun α => s611_w d m α * hermiteCoeff (fun x => f (x - t • s611_e i)) α ^ 2) ∧
      ∑' α, s611_w d m α * hermiteCoeff (fun x => f (x - t • s611_e i)) α ^ 2 ≤
        Real.exp (2 * m * 3 ^ m * |t|) * ∑' α, s611_w d m α * hermiteCoeff f α ^ 2 := by
  have h0 : ∀ α, s611_A f i α 0 = hermiteCoeff f α := fun α => by
    rw [s611_A_eq]; simp
  have hS0 : Summable (fun α => s611_w d m α * s611_A f i α 0 ^ 2) := by
    simpa only [h0] using hS
  have hbd : ∀ N, ∑ α ∈ s611_D d N, s611_w d m α * s611_A f i α t ^ 2 ≤
      Real.exp (2 * m * 3 ^ m * |t|) * ∑' α, s611_w d m α * s611_A f i α 0 ^ 2 := fun N =>
    s611_energy_bound m hm i (s611_A f i) _
      (fun α t => by
        have := s611_hasDerivAt_A hf α i t
        simpa [s611_a, s611_b] using this)
      (fun t => s611_A_hasSum hf i t) hS0 N t
  have hnn : ∀ α, 0 ≤ s611_w d m α * s611_A f i α t ^ 2 := fun α =>
    mul_nonneg (pow_nonneg (oscEv_pos α).le m) (sq_nonneg _)
  have hsum : Summable (fun α => s611_w d m α * s611_A f i α t ^ 2) := by
    refine summable_of_sum_le hnn (c := Real.exp (2 * m * 3 ^ m * |t|) *
      ∑' α, s611_w d m α * s611_A f i α 0 ^ 2) fun u => ?_
    refine le_trans ?_ (hbd (u.sup MultiIndex.degree))
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun α _ _ => hnn α
    intro α hα
    exact s611_mem_D.2 (Finset.le_sup (f := MultiIndex.degree) hα)
  have e : ∀ α, s611_A f i α t = hermiteCoeff (fun x => f (x - t • s611_e i)) α := fun α => s611_A_eq f i α t
  simp only [e, h0] at hsum hbd
  refine ⟨hsum, ?_⟩
  refine hsum.tsum_le_of_sum_le fun u => ?_
  refine le_trans ?_ (hbd (u.sup MultiIndex.degree))
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun α _ _ => mul_nonneg (pow_nonneg (oscEv_pos α).le m) (sq_nonneg _)
  intro α hα
  exact s611_mem_D.2 (Finset.le_sup (f := MultiIndex.degree) hα)

end HRS.MS.TransOp

end
