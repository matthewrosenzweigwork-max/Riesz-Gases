import HRS.PDE.MeanFieldSemigroup
import HRS.PDE.WellPosed
import HRS.Sections.Sec7Fields
import HRS.Equilibrium.FieldSingAux

/-!
# Packet e213g (P6): covariance of the adjoint propagator under time shifts

For a general (time-dependent) density path `ρ` on the horizon `b + G`, the propagator of the
shifted path `ρ_b = fun τ => ρ (b + τ)` on the horizon `G` is the shifted propagator:
`U_{ρ_b}^{r,t} φ = U_ρ^{b+r,b+t} φ` for `0 ≤ r ≤ t ≤ G`.  Consequently
`V_{ρ_b}^{t,u} = V_ρ^{b+t,b+u}`.  General-density analogue of `shift_classical`
(`HRS/PDE/MeanFieldSemigroup.lean`) and of `eqevo_timehom` (`HRS/MD/EQEvoTimeHom.lean`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.MC.E213G

open HRS HRS.PDE HRS.PDE.MFSemigroup

variable {d : ℕ}

/-- Restriction to `[b, b+t]` and shift of a classical adjoint solution for a general density path. -/
theorem e213g_shift_classical (D : DynData d) (ρ : ℝ → Torus d → ℝ) {b t : ℝ} (hb : 0 ≤ b)
    (ht : 0 ≤ t) {ψ : Torus d → ℝ} {F : ℝ → Torus d → ℝ}
    (hF : IsClassicalAdjointSolution D ρ (b + t) ψ F) :
    IsClassicalAdjointSolution D (fun τ => ρ (b + τ)) t ψ (fun τ => F (b + τ)) := by
  have hmem : ∀ r ∈ Set.Icc (0 : ℝ) t, b + r ∈ Set.Icc (0 : ℝ) (b + t) := fun r hr =>
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  let φ : Set.Icc (0 : ℝ) t → Set.Icc (0 : ℝ) (b + t) := fun r => ⟨b + r.1, hmem r.1 r.2⟩
  have hφ : Continuous φ := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_const.add continuous_subtype_val
  refine ⟨fun r hr => hF.c2 _ (hmem r hr), fun j hj => ?_, ?_, ?_, ?_⟩
  · exact (hF.cont_c2 j hj).comp (hφ.prodMap continuous_id)
  · exact hF.terminal
  · intro x r hr
    have h1 : b + r ∈ Set.Ioo 0 (b + t) := ⟨by linarith [hr.1], by linarith [hr.2]⟩
    exact (hF.time_deriv x _ h1).comp_const_add b r
  · refine (hF.cont_time_deriv.comp (hφ.prodMap continuous_id)).congr ?_
    intro p
    rfl

/-- **Propagator covariance** (P6): for `0 ≤ b`, `0 ≤ r ≤ t ≤ G`,
`U_{ρ_b}^{r,t} φ = U_ρ^{b+r,b+t} φ` with `ρ_b τ = ρ (b + τ)`.  The bundle hypotheses are those of
`adjoint_torus_classical` for `ρ` on `[0,b+G]` (level `m₁ ≥ mStar d`) and of
`classical_adjoint_unique_of_two` for `ρ_b` on `[0,G]` (level `m₂ ≥ 1`). -/
theorem propagator_shift (hd : 2 ≤ d) {s₁ s₂ : ℝ} {m₁ m₂ : ℕ} {R₁ R₂ : Regime}
    {MB₁ Λ₁ VB₁ MB₂ Λ₂ VB₂ : ℝ} {D : DynData d} {ν₁ ν₂ b G : ℝ} {ρ : ℝ → Torus d → ℝ}
    (hb : 0 ≤ b)
    (hA : AdjointData s₁ m₁ R₁ MB₁ Λ₁ VB₁ D ν₁ (b + G) ρ)
    (hB : AdjointData s₂ m₂ R₂ MB₂ Λ₂ VB₂ D ν₂ G (fun τ => ρ (b + τ)))
    (hm₁ : mStar d ≤ m₁) (hm₂ : 1 ≤ m₂)
    {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (htG : t ≤ G)
    {φ : Torus d → ℝ} (hφc : Continuous φ) (hφs : MemSobolev (m₁ : ℝ) φ) :
    propagator D (fun τ => ρ (b + τ)) r t φ = propagator D ρ (b + r) (b + t) φ := by
  have hs0 : 0 ≤ s₂ := by
    have h := D.hs0
    rw [hB.hs] at h
    exact h
  have hsd : s₂ < d := by
    have h := D.hsd
    rw [hB.hs] at h
    exact h
  have hs0₁ : 0 ≤ s₁ := by
    have h := D.hs0
    rw [hA.hs] at h
    exact h
  have hsd₁ : s₁ < d := by
    have h := D.hsd
    rw [hA.hs] at h
    exact h
  have hm1 : 1 ≤ m₁ := by
    have : 1 ≤ mStar d := by unfold mStar; omega
    omega
  have ht0 : 0 ≤ t := hr.trans hrt
  rcases eq_or_lt_of_le (add_nonneg hb ht0) with hbt | hbt
  · -- `b + t = 0`: everything is at the origin
    have hb0 : b = 0 := by linarith
    have ht0' : t = 0 := by linarith
    have hr0 : r = 0 := le_antisymm (ht0' ▸ hrt) hr
    subst hb0 ht0' hr0
    simp
  · -- existence of the classical solution for `ρ` at terminal time `b + t`
    obtain ⟨_, _, _, _, hmain⟩ := adjoint_torus_classical (by omega) s₁ hs0₁ hsd₁ m₁ hm₁ R₁ MB₁ Λ₁ VB₁
    have hbtG : b + t ∈ Set.Ioc 0 (b + G) := ⟨hbt, by linarith⟩
    have hex := (hmain D ν₁ (b + G) ρ hA (b + t) hbtG φ hφc hφs).1
    set f := (fun r x => toFun (propagatorCoeff D ρ m₁ (b + t) (coeffOf φ) (b + t - r)) x)
      with hf
    have hg := e213g_shift_classical D ρ hb ht0 hex
    have hexB : ∃ g, IsClassicalAdjointSolution D (fun τ => ρ (b + τ)) t φ g := ⟨_, hg⟩
    have hexA : ∃ g, IsClassicalAdjointSolution D ρ (b + t) φ g := ⟨_, hex⟩
    have hLB : ∀ x, propagator D (fun τ => ρ (b + τ)) x t φ = hexB.choose x := by
      intro x
      unfold propagator
      rw [dif_pos hexB]
    have hRA : ∀ x, propagator D ρ x (b + t) φ = hexA.choose x := by
      intro x
      unfold propagator
      rw [dif_pos hexA]
    rcases eq_or_lt_of_le hrt with h | h
    · -- `r = t`: both sides are `φ`
      subst h
      rw [hLB, hRA, hexB.choose_spec.terminal, hexA.choose_spec.terminal]
    · -- `r < t`: uniqueness for the shifted path on the horizon `G`
      have ht' : t ∈ Set.Ioc 0 G := ⟨by linarith, htG⟩
      have hu := classical_adjoint_unique_of_two hd s₂ hs0 hsd m₂ hm₂ R₂ MB₂ Λ₂ VB₂ D ν₂ G
        (fun τ => ρ (b + τ)) hB t ht' φ _ _ hexB.choose_spec hg r ⟨hr, h.le⟩
      -- the unshifted side: uniqueness is not needed, `hexA.choose` is only compared with `f`
      have hu2 := classical_adjoint_unique_of_two hd s₁ hs0₁ hsd₁ m₁ hm1 R₁ MB₁ Λ₁
        VB₁ D ν₁ (b + G) ρ hA (b + t) hbtG φ _ _ hexA.choose_spec hex (b + r)
        ⟨by linarith, by linarith⟩
      rw [hLB, hRA, hu, hu2]

/-- **Propagator covariance for `V`** (P6, consequence): for `0 ≤ u ≤ t ≤ G`,
`V_{ρ_b}^{t,u} = V_ρ^{b+t,b+u}` on `E_m`. -/
theorem vprop_shift (hd : 2 ≤ d) {s₁ s₂ : ℝ} {m₁ m₂ : ℕ} {R₁ R₂ : Regime}
    {MB₁ Λ₁ VB₁ MB₂ Λ₂ VB₂ : ℝ} {D : DynData d} {ν₁ ν₂ b G : ℝ} {ρ : ℝ → Torus d → ℝ}
    (hb : 0 ≤ b)
    (hA : AdjointData s₁ m₁ R₁ MB₁ Λ₁ VB₁ D ν₁ (b + G) ρ)
    (hB : AdjointData s₂ m₂ R₂ MB₂ Λ₂ VB₂ D ν₂ G (fun τ => ρ (b + τ)))
    (hm₁ : mStar d ≤ m₁) (hm₂ : 1 ≤ m₂) (m : ℝ)
    {t u : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (htG : t ≤ G) :
    Sec7.Vprop D (fun τ => ρ (b + τ)) m t u = Sec7.Vprop D ρ m (b + t) (b + u) := by
  funext F
  unfold Sec7.Vprop
  congr 1
  funext k
  have hsm : Torus.IsSmooth (Torus.realMode k : Torus d → ℝ) := FieldSingAux.isSmooth_realMode k
  have hc : Continuous (Torus.realMode k : Torus d → ℝ) :=
    ClassicalAux.continuous_of_isCk (ClassicalAux.isCk_of_le (by exact_mod_cast le_top) hsm)
  rw [propagator_shift hd hb hA hB hm₁ hm₂ hu hut htG hc (memSobolev_of_isSmooth hsm _)]

end HRS.MC.E213G
