import HRS.PDE.MeanFieldSemigroup
import HRS.PDE.WellPosed

/-!
# EQ29 packet P7.4: time-homogeneity of the adjoint propagator for a constant density

For a constant density `μ r = ρ`, the propagator from time `r` to time `t` is the propagator
from time `0` to time `t - r`: `U^{r,t} φ = U^{0,t-r} φ`.

Statement change relative to the plan: `2 ≤ d` is kept, and the level `m` must satisfy
`mStar d ≤ m` (the existence theorem `adjoint_torus_classical` needs it), together with
`Continuous φ` and `MemSobolev m φ` (the existence theorem needs them). The start-time
parameter `s` is recovered from `hA.hs`, so it is not an extra hypothesis.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.MD.EQEvoTimeHom

open HRS HRS.PDE HRS.PDE.MFSemigroup

variable {d : ℕ}

theorem eqevo_timehom (hd : 2 ≤ d) {s : ℝ} {m : ℕ} {R : Regime} {MB Λ VB : ℝ} {D : DynData d}
    {ν₀ T : ℝ} {ρ : Torus d → ℝ}
    (hA : AdjointData s m R MB Λ VB D ν₀ T (fun _ => ρ)) (hm : mStar d ≤ m)
    {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (ht : t ∈ Set.Ioc 0 T)
    {φ : Torus d → ℝ} (hφc : Continuous φ) (hφs : MemSobolev (m : ℝ) φ) :
    propagator D (fun _ => ρ) r t φ = propagator D (fun _ => ρ) 0 (t - r) φ := by
  have hs0 : 0 ≤ s := by
    have h := D.hs0
    rw [hA.hs] at h
    exact h
  have hsd : s < d := by
    have h := D.hsd
    rw [hA.hs] at h
    exact h
  have hm1 : 1 ≤ m := by
    have : 1 ≤ mStar d := by unfold mStar; omega
    omega
  have hV1 : Torus.IsCk 1 D.V :=
    ClassicalAux.isCk_of_le (by exact_mod_cast (by omega : 1 ≤ m + 3)) hA.hV.1
  have hμ1 : Torus.IsCk 1 ((fun _ => ρ) 0) :=
    ClassicalAux.isCk_of_le (by exact_mod_cast (by omega : 1 ≤ m + 3))
      (hA.hμ.smooth 0 ⟨le_rfl, hA.hT.le⟩)
  have hK : ClassicalAux.ConvKernelFacts d D.s :=
    ClassicalAux.convKernelFacts_of_two_le hd D.hs0 D.hsd
  -- existence of a classical solution at terminal time `t`
  obtain ⟨_, _, _, _, hmain⟩ := adjoint_torus_classical (by omega) s hs0 hsd m hm R MB Λ VB
  have hex : ∃ f, IsClassicalAdjointSolution D (fun _ => ρ) t φ f :=
    ⟨_, (hmain D ν₀ T (fun _ => ρ) hA t ht φ hφc hφs).1⟩
  have hLHS : ∀ x, propagator D (fun _ => ρ) x t φ = hex.choose x := by
    intro x
    unfold propagator
    rw [dif_pos hex]
  rcases eq_or_lt_of_le hrt with h | h
  · -- `r = t`: both sides are `φ`
    have hφ2 : Torus.IsCk 2 φ := by
      have := hex.choose_spec.c2 t ⟨ht.1.le, le_rfl⟩
      rwa [hex.choose_spec.terminal] at this
    rw [h, sub_self, hLHS, hex.choose_spec.terminal,
      propagator_zero D hK hV1 _ hμ1 hφ2]
  · -- `r < t`: shift the terminal time to `t - r` and use uniqueness at `t - r`
    have hτ : 0 < t - r := by linarith
    have hτT : t - r ≤ t := by linarith
    have hG := shift_classical D ρ hτT hex.choose_spec
    have hex' : ∃ f, IsClassicalAdjointSolution D (fun _ => ρ) (t - r) φ f := ⟨_, hG⟩
    have hu := classical_adjoint_unique_of_two hd s hs0 hsd m hm1 R MB Λ VB D ν₀ T (fun _ => ρ) hA
      (t - r) ⟨hτ, hτT.trans ht.2⟩ φ _ _ hex'.choose_spec hG 0 ⟨le_rfl, hτ.le⟩
    have hR : propagator D (fun _ => ρ) 0 (t - r) φ = hex'.choose 0 := by
      unfold propagator
      rw [dif_pos hex']
    rw [hR, hu, hLHS]
    simp

end HRS.MD.EQEvoTimeHom
