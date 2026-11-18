import HRS.Main.HaarAux1
import HRS.Stochastic.Bridge
import HRS.Torus.Sobolev

/-!
# Packet HI (row 7.14), part 1: diagonal translations and strong solutions

For the homogeneous dynamics `D.V = 0` the particle drift depends only on the differences `X i - X j`.  Hence the diagonal
translation `shiftC θ : X ↦ (X i + θ)_i` maps strong solutions to strong solutions (with initial data translated by `θ`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Q714.HI

open HRS

variable {d N : ℕ}

/-- The diagonal translation of configurations. -/
def shiftC (θ : Torus d) (X : Config d N) : Config d N := fun i => X i + θ

theorem measurable_shiftC (θ : Torus d) : Measurable (shiftC θ : Config d N → Config d N) :=
  haar_shift_measurable θ

theorem hi_shiftC_mem_collisionSet_iff (θ : Torus d) (X : Config d N) :
    shiftC θ X ∈ collisionSet d N ↔ X ∈ collisionSet d N := by
  simp only [collisionSet, Set.mem_setOf_eq, shiftC, add_left_inj]

theorem hi_grad_zero (x : Torus d) : Torus.grad (fun _ : Torus d => (0 : ℝ)) x = 0 := by
  unfold Torus.grad Torus.lift
  have : ((fun _ : Torus d => (0 : ℝ)) ∘ Torus.mk) = fun _ : Euc d => (0 : ℝ) := rfl
  rw [this]
  exact gradient_const _ _

theorem hi_particleDrift_shiftC (D : DynData d) (hV : D.V = fun _ => 0) (θ : Torus d)
    (X : Config d N) (i : Fin N) : particleDrift D (shiftC θ X) i = particleDrift D X i := by
  unfold particleDrift
  rw [hV, hi_grad_zero, hi_grad_zero]
  simp only [shiftC, add_sub_add_right_eq_sub]

theorem hi_projectPath_add {Ω : Type*} (Y : ℝ≥0 → Ω → (Fin N → Euc d)) (θ : Torus d) (s : ℝ≥0) (ω : Ω) :
    projectPath (fun t ω i => Y t ω i + Torus.rep θ) s ω = shiftC θ (projectPath Y s ω) := by
  funext i
  simp [projectPath, shiftC, Torus.mk_add, Torus.mk_rep]

theorem hi_isStrongSolution_shiftC {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {D : DynData d}
    (hV : D.V = fun _ => 0) {T : ℝ} {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} (θ : Torus d) (h : IsStrongSolution P D T X₀ W X) :
    IsStrongSolution P D T (fun ω => shiftC θ (X₀ ω)) W (fun t ω => shiftC θ (X t ω)) where
  lift := by
    obtain ⟨Y, hY, hX⟩ := h.lift
    refine ⟨fun t ω i => Y t ω i + Torus.rep θ, ?_, ?_⟩
    · filter_upwards [hY] with ω hω t ht
      obtain ⟨hint, heq⟩ := hω t ht
      have hdr : ∀ (i : Fin N) (s : ℝ),
          particleDrift D (projectPath (fun t ω i => Y t ω i + Torus.rep θ) (Real.toNNReal s) ω) i =
            particleDrift D (projectPath Y (Real.toNNReal s) ω) i := fun i s => by
        rw [hi_projectPath_add, hi_particleDrift_shiftC D hV]
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa only [hdr] using hint i
      · simp only [hdr]
        rw [heq i]
        abel
    · subst hX
      funext t ω
      exact (hi_projectPath_add Y θ t ω).symm
  init := by
    filter_upwards [h.init] with ω hω
    simp [hω]
  cont := by
    filter_upwards [h.cont] with ω hω i
    exact (hω i).add continuous_const
  adapted t := (measurable_shiftC θ).comp (h.adapted t)
  no_collision := by
    filter_upwards [h.no_collision] with ω hω t ht
    rw [hi_shiftC_mem_collisionSet_iff]
    exact hω t ht

end HRS.MC.Q714.HI
