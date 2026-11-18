import HRS.MS.GenPathAux36

/-!
# S5.6 packet P5d: the deterministic covariation density `C̄_r = featureForm(Γ(r), ρ_r dx)`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.GenPath

open HRS.Whole HRS.MP.RdRem

variable {d : ℕ}

/-- Pointwise continuity in time of the mean-field densities (copy of the proof of `s55f_weak_cont_bdd`). -/
theorem s56_rho_pointwise (hd : 1 ≤ d) {T : ℝ} {ρ : ℝ → Euc d → ℝ} (Λ : ℝ)
    (hreg : ∀ t ∈ Set.Icc (0 : ℝ) T, MemCb 3 (ρ t) ∧ weightedSupE 3 ((d : ℝ) + 3) (ρ t) < ⊤ ∧
      HRS.cbNorm 3 (ρ t) + (weightedSupE 3 ((d : ℝ) + 3) (ρ t)).toReal ≤ Λ)
    (hweak : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ContinuousOn (fun r => ∫ x, ψ x * ρ r x) (Set.Icc (0 : ℝ) T)) :
    (∀ r ∈ Set.Icc (0 : ℝ) T, Differentiable ℝ (ρ r)) ∧
      ∀ y, ContinuousOn (fun r => ρ r y) (Set.Icc (0 : ℝ) T) := by
  set A : ℝ := (d : ℝ) ^ 3 * max Λ 0 * 2 ^ ((d : ℝ) + 3) with hAdef
  have hA : 0 ≤ A := by positivity
  have hdec : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.MP.RdGen.RgDecay 3 (fun _ => A) (ρ r) := by
    intro r hr
    have hcb := hreg r hr
    have hcb0 : 0 ≤ HRS.cbNorm 3 (ρ r) :=
      Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
    exact HRS.MP.RdGen.rg_rho_decay hd (r := 3) (Λ := max Λ 0) hcb.1 hcb.2.1
      (by linarith [hcb.2.2, le_max_left Λ 0])
  have hparts := fun r hr => HRS.MP.RdGen.rg_decay_parts (n := 3) (by omega) (a := fun _ => A)
    (fun _ => hA) (hdec r hr)
  have hw : ∀ y : Euc d, (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ 1 := by
    intro y
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y])
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hdiff : ∀ r ∈ Set.Icc (0 : ℝ) T, Differentiable ℝ (ρ r) := fun r hr =>
    ((hparts r hr).1).differentiable (by norm_num)
  have h0 : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ y, ‖ρ r y‖ ≤ A * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) :=
    fun r hr => (hparts r hr).2.1
  have h1' : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ y, ‖fderiv ℝ (ρ r) y‖ ≤ A := fun r hr y =>
    ((hparts r hr).2.2.1 y).trans (by
      calc A * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ A * 1 := mul_le_mul_of_nonneg_left (hw y) hA
        _ = A := mul_one _)
  exact ⟨hdiff, fun y => HRS.MS.Go.s55_pointwise hA hweak hdiff h1' y⟩

end HRS.MS.GenPath
