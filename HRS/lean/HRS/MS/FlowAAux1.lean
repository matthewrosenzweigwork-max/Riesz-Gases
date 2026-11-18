import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.MeanValue

/-!
# MS-FLOW-A, generic ODE lemmas (Banach space `E`)

Hypotheses `Hyp`, solutions `Sol`, Gronwall consequences, time reversal and global existence for
`f' = -b(τ, f)` on `[0,T]` with `b` continuous, `Λ`-Lipschitz in space and of linear growth.
-/

open Set Metric
open scoped NNReal Topology

set_option linter.unusedSectionVars false

namespace HRS.MS.FlowA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Hypotheses on the drift. -/
structure Hyp (T Λ : ℝ) (b : ℝ → E → E) : Prop where
  Λ_nonneg : 0 ≤ Λ
  cont : ContinuousOn (fun p : ℝ × E => b p.1 p.2) (Icc (0 : ℝ) T ×ˢ univ)
  lip : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x y, ‖b τ x - b τ y‖ ≤ Λ * ‖x - y‖
  growth : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x, ‖b τ x‖ ≤ Λ * (1 + ‖x‖)

/-- `f` solves `f' = -b(τ, f)` on `[0,T]`. -/
def Sol (T : ℝ) (b : ℝ → E → E) (f : ℝ → E) : Prop :=
  ∀ τ ∈ Icc (0 : ℝ) T, HasDerivWithinAt f (-(b τ (f τ))) (Icc (0 : ℝ) T) τ

theorem Sol.mono {T S : ℝ} {b : ℝ → E → E} {f : ℝ → E} (h : Sol T b f) (hS : S ≤ T) :
    Sol S b f := fun τ hτ =>
  (h τ ⟨hτ.1, hτ.2.trans hS⟩).mono (Icc_subset_Icc_right hS)

theorem Sol.continuousOn {T : ℝ} {b : ℝ → E → E} {f : ℝ → E} (h : Sol T b f) :
    ContinuousOn f (Icc (0 : ℝ) T) := fun τ hτ => (h τ hτ).continuousWithinAt

theorem Hyp.mono {T S Λ : ℝ} {b : ℝ → E → E} (h : Hyp T Λ b) (hS : S ≤ T) : Hyp S Λ b where
  Λ_nonneg := h.Λ_nonneg
  cont := h.cont.mono (prod_mono (Icc_subset_Icc_right hS) subset_rfl)
  lip τ hτ := h.lip τ ⟨hτ.1, hτ.2.trans hS⟩
  growth τ hτ := h.growth τ ⟨hτ.1, hτ.2.trans hS⟩

/-- Gronwall for two solutions on `[0,S]`, `S ≤ T`. -/
theorem gron {T S Λ : ℝ} {b : ℝ → E → E} (h : Hyp T Λ b) (hS : S ≤ T) {f g : ℝ → E}
    (hf : Sol S b f) (hg : Sol S b g) :
    ∀ τ ∈ Icc (0 : ℝ) S, ‖f τ - g τ‖ ≤ ‖f 0 - g 0‖ * Real.exp (Λ * τ) := by
  intro τ hτ
  have hmem : ∀ t ∈ Ico (0 : ℝ) S, Icc (0 : ℝ) S ∈ 𝓝[≥] t := fun t ht =>
    Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc ht.1 le_rfl)
  have := dist_le_of_trajectories_ODE_of_mem (v := fun t y => -(b t y)) (s := fun _ => univ)
    (K := ⟨Λ, h.Λ_nonneg⟩) (f := f) (g := g) (a := 0) (b := S) (δ := ‖f 0 - g 0‖)
    (fun t ht => LipschitzOnWith.of_dist_le_mul fun x _ y _ => by
      have := h.lip t ⟨ht.1, ht.2.le.trans hS⟩ x y
      rw [dist_eq_norm, dist_eq_norm, show -b t x - -b t y = -(b t x - b t y) by abel, norm_neg]
      exact this)
    hf.continuousOn
    (fun t ht => (hf t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin (hmem t ht))
    (fun _ _ => trivial) hg.continuousOn
    (fun t ht => (hg t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin (hmem t ht))
    (fun _ _ => trivial) (by simp [dist_eq_norm]) τ hτ
  simp only [dist_eq_norm, sub_zero] at this
  exact this

theorem sol_unique {T S Λ : ℝ} {b : ℝ → E → E} (h : Hyp T Λ b) (hS : S ≤ T) {f g : ℝ → E}
    (hf : Sol S b f) (hg : Sol S b g) (h0 : f 0 = g 0) :
    ∀ τ ∈ Icc (0 : ℝ) S, f τ = g τ := by
  intro τ hτ
  have := gron h hS hf hg τ hτ
  rw [h0, sub_self, norm_zero, zero_mul] at this
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

/-- Time reversal of the drift on `[0,τ]`. -/
def rev (τ : ℝ) (b : ℝ → E → E) : ℝ → E → E := fun s y => -(b (τ - s) y)

theorem rev_rev (τ : ℝ) (b : ℝ → E → E) : rev τ (rev τ b) = b := by
  funext s y
  simp [rev]

theorem Hyp.rev {T Λ : ℝ} {b : ℝ → E → E} (h : Hyp T Λ b) {τ : ℝ} (hτ : τ ≤ T) :
    Hyp τ Λ (rev τ b) where
  Λ_nonneg := h.Λ_nonneg
  cont := by
    have hc : ContinuousOn (fun p : ℝ × E => -(b (τ - p.1) p.2)) (Icc (0 : ℝ) τ ×ˢ univ) := by
      refine ContinuousOn.neg ?_
      have := h.cont.comp (f := fun p : ℝ × E => (τ - p.1, p.2))
        (by fun_prop) (s := Icc (0 : ℝ) τ ×ˢ univ) (t := Icc (0 : ℝ) T ×ˢ univ)
        (fun p hp => ⟨⟨by linarith [hp.1.2], by linarith [hp.1.1]⟩, trivial⟩)
      exact this
    exact hc
  lip s hs x y := by
    have := h.lip (τ - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩ x y
    simp only [FlowA.rev]
    rw [show -b (τ - s) x - -b (τ - s) y = -(b (τ - s) x - b (τ - s) y) by abel, norm_neg]
    exact this
  growth s hs x := by
    have := h.growth (τ - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩ x
    simpa [FlowA.rev] using this

theorem Sol.rev {τ : ℝ} {b : ℝ → E → E} {f : ℝ → E} (h : Sol τ b f) :
    Sol τ (rev τ b) (fun s => f (τ - s)) := by
  intro s hs
  have hs' : τ - s ∈ Icc (0 : ℝ) τ := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have h1 : HasDerivWithinAt (fun s : ℝ => τ - s) (-1) (Icc (0 : ℝ) τ) s :=
    ((hasDerivAt_id s).const_sub τ).hasDerivWithinAt
  have := (h (τ - s) hs').scomp s h1 (fun r hr => ⟨by linarith [hr.2], by linarith [hr.1]⟩)
  simpa [FlowA.rev, Function.comp_def] using this

end HRS.MS.FlowA
