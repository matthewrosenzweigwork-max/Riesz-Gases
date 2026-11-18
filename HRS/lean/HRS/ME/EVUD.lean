import HRS.PDE.MeanFieldDecayGap
import HRS.PDE.MeanFieldThermalExist

/-!
# V-uniform two-sided thermal bounds (packet EVD of `docs/MAIN_E_EVU_PLAN.md`)

`exists_thermal_bounds_unifV` is a copy of `HRS.PDE.MFDecay.exists_thermal_bounds`
(`HRS/PDE/MeanFieldDecayGap.lean:39`) with `lam, Lam` chosen before the potential `V`: the fixed
data are `d s βm βp` and the bound `Bv`; then for every continuous `V` with `|V| ≤ Bv`, every thermal
density at `β ∈ [βm, βp]` lies in `[lam, Lam]`.

The original takes `lam, Lam` from `MFThermalExist.thermal_exists_of_truncated`, whose bounds are
explicit in `Mv` (a bound for `|V|`), `B` (a lower bound of `periodicRiesz`), `L1` and `Lp`. Here
`Mv := |Bv|` is supplied by the hypothesis `|V| ≤ Bv`, and `B`, `L1` do not depend on `V`. The wrapper
`thermal_exists_of_truncated` is copied as `thermal_exists_of_truncated_unifV` with `Mv` fixed; the
per-`V` qualitative inputs `exists_truncated_thermal`, `thermal_exists_fixed` (as the finite-`N`
limit, bounds explicit in `Mv`) and `thermal_unique'` are used unchanged.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ComplexConjugate

open HRS.PDE

namespace HRS.ME.EVU

variable {d : ℕ}

/-- (A1, V-uniform) Two-sided bounds on every continuous positive thermal density, with `lam, Lam`
chosen before `V` (copy of `HRS.PDE.MFDecay.exists_thermal_bounds`). -/
theorem exists_thermal_bounds_unifV (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (Bv : ℝ) :
    ∃ lam Lam : ℝ, 0 < lam ∧ ∀ V : Torus d → ℝ, Continuous V → (∀ x, |V x| ≤ Bv) →
      ∀ β ∈ Set.Icc βm βp, ∀ ρβ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) V β ρβ → Continuous ρβ → (∀ x, 0 < ρβ x) →
      ∀ x, lam ≤ ρβ x ∧ ρβ x ≤ Lam := by
  have F := MFThermalAssembly.kernelFacts hd s hs0 hsd
  obtain ⟨B0, hB0⟩ := F.bddBelow
  have hB : ∀ x, -|B0| ≤ periodicRiesz d s x := fun x =>
    le_trans (neg_le_neg (le_abs_self B0)) (hB0 x)
  set L1 := ∫ y, |periodicRiesz d s y| with hL1def
  have hL1 : 0 ≤ L1 := integral_nonneg fun y => abs_nonneg _
  set Lp := Real.exp (βp * (2 * |Bv| + |B0|)) with hLp
  refine ⟨Real.exp (-2 * βp * (|Bv| + L1 * Lp)), Lp, Real.exp_pos _, fun V hV hVB β hβ ρβ hρβ hc hp x => ?_⟩
  have hβpos : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hMv : ∀ x, |V x| ≤ |Bv| := fun x => (hVB x).trans (le_abs_self Bv)
  -- the truncated solutions and the limit (per `V`, qualitative)
  have H : ∀ n : ℕ, ∃ ρ, MFThermalExist.TruncSol s V β (n + 1) ρ := fun n => by
    obtain ⟨ρ, hc, hp, hi, he⟩ := MFThermalExist.exists_truncated_thermal hd s hs0 hsd F V hV β
      hβpos (n + 1) (Nat.succ_pos n)
    exact ⟨ρ, ⟨hc, hp, hi, he⟩⟩
  choose ρs hρs using H
  obtain ⟨ρ', hth, hc', hbd⟩ := MFThermalExist.thermal_exists_fixed F hV hMv hB hβpos ρs hρs
  -- bounds, uniform in `β ∈ [βm, βp]`
  have h1 : Real.exp (β * (2 * |Bv| + |B0|)) ≤ Lp :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hβ.2 (by positivity))
  have h2 : |Bv| + L1 * Real.exp (β * (2 * |Bv| + |B0|)) ≤ |Bv| + L1 * Lp := by
    nlinarith [mul_le_mul_of_nonneg_left h1 hL1]
  have h3 : β * (|Bv| + L1 * Real.exp (β * (2 * |Bv| + |B0|))) ≤ βp * (|Bv| + L1 * Lp) :=
    mul_le_mul hβ.2 h2 (by positivity) (hβpos.le.trans hβ.2)
  have hb : ∀ y, Real.exp (-2 * βp * (|Bv| + L1 * Lp)) ≤ ρ' y ∧ ρ' y ≤ Lp := fun y => by
    refine ⟨le_trans (Real.exp_le_exp.mpr ?_) (hbd y).1, (hbd y).2.trans h1⟩
    linarith
  have hpos' : ∀ y, 0 < ρ' y := fun y => lt_of_lt_of_le (Real.exp_pos _) (hb y).1
  have := MFThermalExist.thermal_unique' hd s hs0 hsd F β hβpos V ρβ ρ' hρβ hc hp hth hc' hpos'
  rw [← this]
  exact hb x

end HRS.ME.EVU
