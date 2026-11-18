import HRS.Main.A8PAux3

/-!
# Example A.16, lemma L1: `1 ≤ Λ` from `MeanFieldRegularity` alone
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Main.Det16

variable {d : ℕ}

theorem det16_Lam_ge_one {S : MainData d} {r : ℕ} {Λ : ℝ} (hmf : MeanFieldRegularity S r Λ) : 1 ≤ Λ := by
  have hN : 1 ≤ 1 := le_rfl
  have hr : (0 : ℝ) ∈ Set.Icc 0 S.T := ⟨le_rfl, S.hT.le⟩
  have hd := (hmf.solution 1 hN).density 0 hr
  by_contra hlt
  push Not at hlt
  have hle : ∀ x, S.ρ 1 0 x ≤ Λ := fun x => by
    have hreg := ((hmf.regular 1 hN).1 0 hr)
    have h := HRS.GF.gfb2_sup_le_cbNorm hreg.1 x
    exact (le_abs_self _).trans (h.trans hreg.2)
  have : (∫ x, S.ρ 1 0 x) ≤ Λ := by
    calc (∫ x, S.ρ 1 0 x) ≤ ∫ _x : Torus d, Λ := by
          refine integral_mono_of_nonneg (Eventually.of_forall hd.nonneg) (integrable_const _)
            (Eventually.of_forall hle)
      _ = Λ := by simp
  have h1 := hd.integral_one
  linarith

end HRS.Main.Det16
