import HRS.MD.EQEvoTimeHom
import HRS.PDE.MeanFieldAdjointSmoothing
import HRS.PDE.MeanFieldAdjointSmoothingLow

/-!
# EQ29 packet P7.5: uniform top decay of the adjoint propagator for a frozen density

The constants `Cp, cp` are chosen before `β`, `V`, `ρβ`. The decay of the projected propagator
from time `u` to time `t` follows from the time-homogeneity `eqevo_timehom` (P7.4) and
`exists_frozen_hj_decay'`.

Statement change relative to the plan: `2 ≤ d` is added (needed by P7.4).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.MD.EQEvoTopDecay

open HRS HRS.PDE HRS.PDE.MFAdjoint HRS.PDE.MFSemigroup HRS.MD.EQEvoTimeHom

theorem eqevo_top_decay {d : ℕ} (hd : 2 ≤ d) (s : ℝ) (j : ℕ) (hj : (d : ℝ) / 2 + 4 < j)
    (νm νp c₀ Λ₀ : ℝ) :
    ∃ Cp cp : ℝ, 0 < Cp ∧ 0 < cp ∧ ∀ (β : ℝ) (V ρβ : Torus d → ℝ)
      (H : FrozenHyp d s (j + mStar d) νm νp c₀ Λ₀ β V ρβ) (φ : Torus d → ℝ),
      Continuous φ → MemSobolev (j : ℝ) φ → ∀ u t : ℝ, 0 ≤ u → u ≤ t →
        MemSobolev (j : ℝ) (projMean (withDensityReal ρβ)
            (propagator (mfData d s H.hs0 H.hsd V β H.hβ) (fun _ => ρβ) u t φ)) ∧
        sobolevNorm (j : ℝ) (projMean (withDensityReal ρβ)
            (propagator (mfData d s H.hs0 H.hsd V β H.hβ) (fun _ => ρβ) u t φ)) ≤
          Cp * Real.exp (-cp * (t - u)) * sobolevNorm (j : ℝ) (projMean (withDensityReal ρβ) φ) := by
  obtain ⟨C, c, hC, hc, hdec⟩ := exists_frozen_hj_decay' (by omega : 1 ≤ d) s j hj νm νp c₀ Λ₀
  refine ⟨C, c, hC, hc, fun β V ρβ H φ hφc hφs u t hu hut => ?_⟩
  have h3 : 3 ≤ mStar d := by unfold mStar; omega
  have hjm : mStar d ≤ j := by
    have h1 : ((⌊(d : ℝ) / 2⌋₊ : ℕ) : ℝ) ≤ (d : ℝ) / 2 := Nat.floor_le (by positivity)
    have h2 : ((mStar d : ℕ) : ℝ) ≤ (j : ℝ) := by
      unfold mStar
      push_cast
      linarith
    exact_mod_cast h2
  have hH' : FrozenHyp d s (mStar d + 3) νm νp c₀ Λ₀ β V ρβ := H.mono (by omega)
  have hφs' : MemSobolev ((mStar d : ℕ) : ℝ) φ := by
    have := memSobolev_mono_idx (m := (j : ℝ)) (m' := ((mStar d : ℕ) : ℝ)) hφs (by exact_mod_cast hjm)
    exact this
  -- time-homogeneity (P7.4) reduces the propagator from `u` to `t` to the one from `0` to `t - u`
  have hkey : propagator (mfData d s H.hs0 H.hsd V β H.hβ) (fun _ => ρβ) u t φ =
      propagator (mfData d s H.hs0 H.hsd V β H.hβ) (fun _ => ρβ) 0 (t - u) φ := by
    rcases eq_or_lt_of_le (hu.trans hut) with ht0 | htpos
    · have hu0 : u = 0 := by linarith
      have ht0' : t = 0 := by linarith
      rw [hu0, ht0', sub_self]
    · have hA := adjointData_frozen_level (mStar d) hH' 0 t htpos
      exact eqevo_timehom hd hA le_rfl hu hut ⟨htpos, le_rfl⟩ hφc hφs'
  rw [hkey]
  exact hdec β V ρβ H φ hφc hφs (t - u) (sub_nonneg.2 hut)

end HRS.MD.EQEvoTopDecay
