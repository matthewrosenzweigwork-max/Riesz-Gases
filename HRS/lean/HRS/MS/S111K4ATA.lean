import HRS.MS.S111X1Aux5
import HRS.MS.CovMeasAux22
import HRS.MS.GenPathAux47

/-!
# S11.1 / all-tests boundary (S111K4AT), piece A: Hermite sections of oscillator tests

`k4hs m n φ = ∑_{|α|≤n} λ_α^{m/2} ⟨φ,h_α⟩ φ_α` (Pro `r26t6_hermiteSection`).  It is a finite dual combination, an oscillator
test function, and `OscDual.eval D (k4hs m n φ) → OscDual.eval D φ`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4AT

open HRS HRS.Whole

variable {d : ℕ}

/-- Pro `r26t6_hermiteSection`. -/
def k4hs (m : ℝ) (n : ℕ) (φ : Euc d → ℝ) : Euc d → ℝ := fun x =>
  ∑ α ∈ (multiIndex_sublevel_finite d n).toFinset,
    (oscEigenvalue d α ^ (m / 2) * hermiteCoeff φ α) * oscTestFun m α x

theorem k4hs_combo (m : ℝ) (n : ℕ) (φ : Euc d → ℝ) : IsR2DualCombo m (k4hs m n φ) :=
  ⟨_, fun α => oscEigenvalue d α ^ (m / 2) * hermiteCoeff φ α, rfl⟩

theorem k4hs_osc (m : ℝ) (n : ℕ) (φ : Euc d → ℝ) : IsOscTest m (k4hs m n φ) := by
  have h : k4hs m n φ = ∑ α ∈ (multiIndex_sublevel_finite d n).toFinset,
      (oscEigenvalue d α ^ (m / 2) * hermiteCoeff φ α) • oscTestFun m α := by
    funext x; simp [k4hs, Finset.sum_apply]
  rw [h, ← HRS.MS.S111X1.mem_oscSub]
  exact Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _ (HRS.MS.S111X1.mem_oscSub.2 (HRS.MS.GenPath.s56_isOscTest m α))

theorem k4hs_eval (m : ℝ) (n : ℕ) (φ : Euc d → ℝ) (D : OscDual d m) :
    OscDual.eval D (k4hs m n φ) = ∑ α ∈ (multiIndex_sublevel_finite d n).toFinset,
      (oscEigenvalue d α ^ (m / 2) * hermiteCoeff φ α) * OscDual.coord D α :=
  HRS.MS.CovMeas.s101_eval_combo D _ _

theorem k4_eval_hasSum (m : ℝ) (D : OscDual d m) {φ : Euc d → ℝ} (hφ : MemOsc m φ) :
    HasSum (fun α => (oscEigenvalue d α ^ (m / 2) * hermiteCoeff φ α) * OscDual.coord D α)
      (OscDual.eval D φ) := by
  have hs := lp.summable_inner (𝕜 := ℝ) (G := fun _ : MultiIndex d => ℝ) (show lp (fun _ : MultiIndex d => ℝ) 2 from D)
    (show lp (fun _ : MultiIndex d => ℝ) 2 from OscSpace.ofFun m φ)
  have hc : ∀ α, (oscEigenvalue d α ^ (m / 2) * hermiteCoeff φ α) * OscDual.coord D α =
      inner ℝ ((show lp (fun _ : MultiIndex d => ℝ) 2 from D) α)
        ((show lp (fun _ : MultiIndex d => ℝ) 2 from OscSpace.ofFun m φ) α) := by
    intro α
    have := OscSpace.coord_ofFun_eq hφ α
    simp only [OscSpace.coord] at this
    simp only [OscDual.coord] at *
    rw [this]
    simp [mul_comm]
  have hsum : Summable fun α => (oscEigenvalue d α ^ (m / 2) * hermiteCoeff φ α) * OscDual.coord D α :=
    hs.congr fun α => (hc α).symm
  convert hsum.hasSum using 1
  rw [← OscDual.toDual_ofFun D φ hφ, OscDual.toDual_apply_coord]
  refine tsum_congr fun α => ?_
  have := OscSpace.coord_ofFun_eq hφ α
  simp only [OscSpace.coord] at this ⊢
  rw [this]; ring

theorem k4hs_tendsto (m : ℝ) (D : OscDual d m) {φ : Euc d → ℝ} (hφ : MemOsc m φ) :
    Tendsto (fun n : ℕ => OscDual.eval D (k4hs m n φ)) atTop (𝓝 (OscDual.eval D φ)) := by
  have h1 := k4_eval_hasSum m D hφ
  have h2 : Tendsto (fun n : ℕ => (multiIndex_sublevel_finite d n).toFinset) atTop atTop := by
    refine tendsto_atTop_atTop.2 fun s => ⟨s.sup fun α => α.degree, fun n hn α hα => ?_⟩
    simp only [Set.Finite.mem_toFinset]
    show α.degree ≤ n
    exact (Finset.le_sup (f := fun α : MultiIndex d => α.degree) hα).trans hn
  exact (h1.comp h2).congr fun n => (k4hs_eval m n φ D).symm

end HRS.MS.S111K4AT
