import HRS.MC.Q714HIShift
import HRS.MD.EQLawPath4
import HRS.Sections.Sec7Setting

/-!
# Packet HI (row 7.14), part 2: law invariance of the flow under diagonal translations

For the homogeneous gradient dynamics and a translation invariant initial law `Q₀` (a.s. collision free), the law of `X^t`
is invariant under `shiftC θ`.  Route: a strong solution `Xσ` on the canonical space `Σ = Config × C(ℝ≥0, ℝ^{N×d})` with
law `Q₀ ⊗ 𝒲` (existence: `particle_wellposed_proof` for `N ≥ 2`, the explicit solution for `N = 1`); the flow equals
`Xσ ∘ J` a.s. (`eqlaw_flow_compare`, pathwise uniqueness); `Xσ ∘ τ_θ` and `shiftC θ ∘ Xσ` are strong solutions with the same
data, hence a.s. equal (pathwise uniqueness again); `τ_θ` preserves `Q₀ ⊗ 𝒲`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Q714.HI

open HRS HRS.MD.EQLawPath HRS.MD.EQLawFlow

variable {d N : ℕ}

theorem hi_particleDrift_one (D : DynData d) (hV : D.V = fun _ => 0) (X : Config d 1) (i : Fin 1) :
    particleDrift D X i = 0 := by
  unfold particleDrift
  have : Finset.univ.erase i = (∅ : Finset (Fin 1)) := by
    ext j
    simp [Subsingleton.elim j i]
  rw [this, hV, hi_grad_zero]
  simp

/-- Explicit solution for `N = 1`: no interaction, `X_t = X_0 + √(2 invβ) (W_t - W_0)`. -/
theorem hi_exists_canon_one (D : DynData d) (hV : D.V = fun _ => 0) (Q : Measure (Sig d 1)) (T : ℝ) :
    ∃ Xσ : ℝ≥0 → Sig d 1 → Config d 1, IsStrongSolution Q D T Prod.fst (sigW d 1) Xσ := by
  let Y : ℝ≥0 → Sig d 1 → (Fin 1 → Euc d) := fun t σ i =>
    Torus.rep (σ.1 i) + Real.sqrt (2 * D.invβ) • (sigW d 1 t σ i - sigW d 1 0 σ i)
  refine ⟨projectPath Y, ?_⟩
  have hdr : ∀ (s : ℝ) (σ : Sig d 1) (i : Fin 1),
      particleDrift D (projectPath Y (Real.toNNReal s) σ) i = 0 := fun s σ i =>
    hi_particleDrift_one D hV _ i
  have hXe : ∀ (t : ℝ≥0) (σ : Sig d 1) (i : Fin 1), projectPath Y t σ i =
      σ.1 i + Torus.mk (Real.sqrt (2 * D.invβ) • (sigW d 1 t σ i - sigW d 1 0 σ i)) := by
    intro t σ i
    simp [projectPath, Y, Torus.mk_add, Torus.mk_rep]
  have hcs : ∀ (σ : Sig d 1) (i : Fin 1), Continuous fun t : ℝ≥0 => sigW d 1 t σ i := fun σ i =>
    (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp (continuous_pi fun j => continuous_sigW σ i j)
  refine ⟨⟨Y, Filter.Eventually.of_forall fun σ t _ => ⟨fun i => ?_, fun i => ?_⟩, rfl⟩, ?_, ?_, ?_, ?_⟩
  · simp only [hdr]
    exact integrableOn_zero
  · simp only [hdr, integral_zero]
    simp [Y]
  · refine Filter.Eventually.of_forall fun σ => ?_
    funext i
    rw [hXe]
    simp [Torus.mk_zero]
  · refine Filter.Eventually.of_forall fun σ i => ?_
    simp only [hXe]
    have hc : Continuous fun t : ℝ≥0 => Real.sqrt (2 * D.invβ) • (sigW d 1 t σ i - sigW d 1 0 σ i) := by
      have := hcs σ i
      fun_prop
    exact continuous_const.add (Torus.continuous_mk.comp hc)
  · intro t
    refine measurable_pi_iff.2 fun i => ?_
    simp only [hXe]
    have h1 : Measurable fun σ : Sig d 1 => sigW d 1 t σ i := (measurable_pi_apply i).comp (measurable_sigW t)
    have h0 : Measurable fun σ : Sig d 1 => sigW d 1 0 σ i := (measurable_pi_apply i).comp (measurable_sigW 0)
    have h2 : Measurable fun σ : Sig d 1 => σ.1 i := (measurable_pi_apply i).comp measurable_fst
    have hm : Measurable fun σ : Sig d 1 =>
        Real.sqrt (2 * D.invβ) • (sigW d 1 t σ i - sigW d 1 0 σ i) := by fun_prop
    exact h2.add (Torus.continuous_mk.measurable.comp hm)
  · refine Filter.Eventually.of_forall fun σ t _ => ?_
    simp only [collisionSet, Set.mem_setOf_eq, not_exists]
    intro i j hij
    exact hij.1 (Subsingleton.elim i j)


theorem hi_locLip (hd : 2 ≤ d) (D : DynData d) (hV : D.V = fun _ => 0) :
    IsLocLipschitzDrift (liftedFree d N) (fun _ Z => liftedDrift D Z) := by
  have hV2 : Torus.IsCk 2 D.V := by
    rw [hV]
    exact contDiff_const
  exact liftedDrift_locLipschitz D (kernelLocal_of_two_le hd D.hs0 D.hsd).smoothOffZero hV2

theorem hi_exists_canon (hd : 2 ≤ d) (hN : 1 ≤ N) (D : DynData d) (hM : D.M = -1)
    (hV : D.V = fun _ => 0) (Q : Measure (Sig d N)) [IsProbabilityMeasure Q]
    (hdist : ∀ᵐ σ ∂Q, σ.1 ∉ collisionSet d N) (hBr : IsVectorBrownian Q (sigW d N))
    (hind : IndepFun Prod.fst (fun σ : Sig d N => fun t => sigW d N t σ) Q) (T : ℝ) (hT : 0 < T) :
    ∃ Xσ : ℝ≥0 → Sig d N → Config d N, IsStrongSolution Q D T Prod.fst (sigW d N) Xσ := by
  rcases Nat.lt_or_ge N 2 with h | h
  · obtain rfl : N = 1 := by omega
    exact hi_exists_canon_one D hV Q T
  · have hM' : Torus.SymNonpos D.M := by
      rw [hM]
      exact eqlaw_symNonpos_neg_one
    have hV2 : Torus.IsCk 2 D.V := by
      rw [hV]
      exact contDiff_const
    exact (particle_wellposed_proof Q D hd h hM' hV2 Prod.fst measurable_fst hdist (sigW d N) hBr hind
      T hT).1

end HRS.MC.Q714.HI
