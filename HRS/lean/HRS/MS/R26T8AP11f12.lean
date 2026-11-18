import HRS.MS.R26T8AP11f11

/-!
# S8.2 T8A P11f (part 12): `Stil ρ Q` is `C^k` off the diagonal
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_f12_Stil_contDiffOn {k : ℕ} {Q : Euc d → Euc d → ℝ}
    (hQ : ContDiffOn ℝ ((k + 2 : ℕ) : WithTop ℕ∞) (Function.uncurry Q) {p | p.1 ≠ p.2})
    {ρ : Euc d → ℝ} (hρ : ContDiff ℝ ∞ ρ) :
    ContDiffOn ℝ (k : WithTop ℕ∞) (Function.uncurry (r26t8a_Stil ρ Q)) {p | p.1 ≠ p.2} := by
  have hQ' : ContDiffOn ℝ (((k + 1) + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry Q) {p | p.1 ≠ p.2} := hQ
  have h1 : ∀ i : Fin d, ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry (r26t8a_dx i Q))
      {p | p.1 ≠ p.2} := fun i => r26t8a_f7_dx_contDiffOn hQ' i
  have h2 : ∀ i : Fin d, ContDiffOn ℝ (k : WithTop ℕ∞) (Function.uncurry (r26t8a_dx i (r26t8a_dx i Q)))
      {p | p.1 ≠ p.2} := fun i => r26t8a_f7_dx_contDiffOn (h1 i) i
  have hρk : ContDiff ℝ (k : WithTop ℕ∞) ρ := hρ.of_le (by exact_mod_cast le_top)
  have hρ1 : ∀ i : Fin d, ContDiff ℝ (k : WithTop ℕ∞) (fun u : Euc d => fderiv ℝ ρ u (EuclideanSpace.single i 1)) :=
    fun i => (hρ.fderiv_right (m := k) (by exact_mod_cast le_top)).clm_apply contDiff_const
  have e : Function.uncurry (r26t8a_Stil ρ Q) = fun p : Euc d × Euc d =>
      ρ p.1 * ∑ i : Fin d, Function.uncurry (r26t8a_dx i (r26t8a_dx i Q)) p +
        ∑ i : Fin d, fderiv ℝ ρ p.1 (EuclideanSpace.single i 1) * Function.uncurry (r26t8a_dx i Q) p := by
    funext p; rfl
  rw [e]
  refine ((hρk.comp contDiff_fst).contDiffOn.mul (ContDiffOn.sum fun i _ => h2 i)).add
    (ContDiffOn.sum fun i _ => ?_)
  exact ((hρ1 i).comp contDiff_fst).contDiffOn.mul ((h1 i).of_le (by exact_mod_cast Nat.le_succ k))

end HRS.MS.R26T8A
