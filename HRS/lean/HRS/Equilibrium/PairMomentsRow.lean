/-
# HRS.Equilibrium.PairMomentsRow -- refined row means via Lemma 4.10 (EQ-01b)
-/
import HRS.Equilibrium.PairMomentsSetting

open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.PairMom

open HRS HRS.External HRS.Quad

variable {d : ℕ} {s : ℝ}

section RowMean

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

/-- **Refined row mean** (`Q:eq:smooth-row-mean`): for a row kernel with `μ[v(x,·)] = 0`, the
conditional mean of `∑_k v(x, y_k)` under the one-pin reference is bounded by
`n ∫ |v(x,y)| (δ + C₁ min{1, (1 + q(y,x))/N}) μ(dy)`. -/
theorem row_mean_refined {V : WeakPotential μ} {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} {δ C1 : ℝ}
    (hRD : RefDens V β n δ C1) {v : Torus d → Torus d → ℝ} (x : Torus d)
    (hfμ : Integrable (v x) μ) (h0 : ∫ y, v x y ∂μ = 0)
    (hfπ : ∀ k : Fin n, Integrable (v x) ((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n
      (pinsWith (fun e : Empty => e.elim) x)).map (fun Y => Y k)))
    {W : ℝ} (hW0 : 0 ≤ W)
    (hW : ∫⁻ y, ENNReal.ofReal (|v x y| * (δ + C1 * min 1 ((1 / ((n + 1 : ℕ) : ℝ)) * (1 + V.q y x))))
      ∂μ ≤ ENNReal.ofReal W) :
    |∑ k : Fin n, ∫ y, v x y ∂((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n
      (pinsWith (fun e : Empty => e.elim) x)).map (fun Y => Y k))| ≤ n * W := by
  have hlam : 0 ≤ β / ((n + 1 : ℕ) : ℝ) := div_nonneg hβ (Nat.cast_nonneg _)
  have h1 : ∀ k : Fin n, |∫ y, v x y ∂((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n
      (pinsWith (fun e : Empty => e.elim) x)).map (fun Y => Y k))| ≤ W := by
    intro k
    haveI : IsProbabilityMeasure (pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n
        (pinsWith (fun e : Empty => e.elim) x)) := isProb_pinnedLaw V hlam n _
    refine abs_integral_marg_le (hRD.ac1 x k) hfμ (hfπ k) h0 ?_ hW0 hW
    filter_upwards [hRD.cmp1 x k, hRD.linf] with y hy1 hy2
    calc |(((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n (pinsWith (fun e : Empty => e.elim) x)).map
            (fun Y => Y k)).rnDeriv μ y).toReal - 1|
        ≤ |(((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n (pinsWith (fun e : Empty => e.elim) x)).map
            (fun Y => Y k)).rnDeriv μ y).toReal - (((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1)
              (fun e : Empty => e.elim)).map (fun Y => Y 0)).rnDeriv μ y).toReal| +
          |(((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)).map
            (fun Y => Y 0)).rnDeriv μ y).toReal - 1| := abs_sub_le _ _ _
      _ ≤ _ := by linarith
  calc |∑ k : Fin n, ∫ y, v x y ∂((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n
        (pinsWith (fun e : Empty => e.elim) x)).map (fun Y => Y k))|
      ≤ ∑ k : Fin n, |∫ y, v x y ∂((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n
        (pinsWith (fun e : Empty => e.elim) x)).map (fun Y => Y k))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, W := Finset.sum_le_sum fun k _ => h1 k
    _ = n * W := by simp

end RowMean

end HRS.PairMom

end
