import HRS.Main.A8PAux2
import HRS.Main.GFB2Aux9

/-!
# Packet A8P, part 3: bookkeeping from `TorusStanding` (adjoint data, regularity, measurability of the density)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

section Ctx

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ}

theorem a8p_rho_cont_time (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ}
    (hN : 1 ≤ N) (x : Torus d) :
    ContinuousOn (fun u => S.ρ N u x) (Set.Icc 0 S.T) := by
  obtain ⟨B, ρt, h⟩ := hS.mean_field.time_derivative
  intro t ht
  exact ((h N hN).1 t ht x).continuousWithinAt

theorem a8p_rho_le (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ}
    (hN : 1 ≤ N) {r : ℝ} (hr : r ∈ Set.Icc 0 S.T) (x : Torus d) : S.ρ N r x ≤ Λ := by
  have hreg := (hS.mean_field.regular N hN).1 r hr
  have h := gfb2_sup_le_cbNorm hreg.1 x
  exact (le_abs_self _).trans (h.trans hreg.2)

theorem a8p_Lam_ge_one (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) : 1 ≤ Λ := by
  have hN : 1 ≤ 1 := le_rfl
  have hr : (0 : ℝ) ∈ Set.Icc 0 S.T := ⟨le_rfl, S.hT.le⟩
  have hd := (hS.mean_field.solution 1 hN).density 0 hr
  by_contra hlt
  push Not at hlt
  have hle : ∀ x, S.ρ 1 0 x ≤ Λ := fun x => a8p_rho_le hS hN hr x
  have : (∫ x, S.ρ 1 0 x) ≤ Λ := by
    calc (∫ x, S.ρ 1 0 x) ≤ ∫ _x : Torus d, Λ := by
          refine integral_mono_of_nonneg (Eventually.of_forall hd.nonneg) (integrable_const _)
            (Eventually.of_forall hle)
      _ = Λ := by simp
  have h1 := hd.integral_one
  linarith

theorem a8p_regular3 (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ}
    (hN : 1 ≤ N) : IsRegularMF 3 Λ S.T (S.ρ N) :=
  gfb2_isRegularMF_mono (by have := PDE.ClassicalPart.three_le_mStar d; omega)
    (hS.mean_field.regular N hN).1

theorem a8p_coeffHyp (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ}
    (hN : 1 ≤ N) : PDE.CoeffHyp (PDE.mStar d) Λ S.T (S.ρ N) := by
  refine ⟨fun r hr => (hS.mean_field.solution N hN).density r hr, fun r hr => ?_, fun r hr => ?_, ?_⟩
  · have := ((hS.mean_field.regular N hN).1 r hr).1
    exact_mod_cast this
  · have := ((hS.mean_field.regular N hN).1 r hr).2
    exact_mod_cast this
  · intro ψ hψ
    obtain ⟨Bψ, hBψ⟩ : ∃ B, ∀ x, |ψ x| ≤ B := by
      obtain ⟨B, hB⟩ := (isCompact_range hψ.abs).bddAbove
      exact ⟨B, fun x => hB ⟨x, rfl⟩⟩
    refine continuousOn_of_dominated (bound := fun _ => Bψ * Λ) (fun r hr => ?_) (fun r hr => ?_)
      (integrable_const _) (Eventually.of_forall fun x => ?_)
    · have h1 := ((hS.mean_field.regular N hN).1 r hr).1
      have h2 : Continuous (S.ρ N r) := Q54c.isCk_continuous h1
      exact (hψ.mul h2).aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      have hρ0 := ((hS.mean_field.solution N hN).density r hr).nonneg x
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hρ0]
      exact mul_le_mul (hBψ x) (a8p_rho_le hS hN hr x) hρ0 ((abs_nonneg _).trans (hBψ x))
    · exact continuousOn_const.mul (a8p_rho_cont_time hS hN x)

theorem a8p_adjointData (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ}
    (hN : 1 ≤ N) :
    PDE.AdjointData S.s (PDE.mStar d) Rg MB Λ VB (S.dyn N) ν₀ S.T (S.ρ N) where
  hs := rfl
  hM := hS.matrix_bound
  hV := hS.potential
  hμ := a8p_coeffHyp hS hN
  hT := S.hT
  regime := hS.regime N hN

/-- Joint measurability of the clamped mean-field density. -/
theorem a8p_rho_meas (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ}
    (hN : 1 ≤ N) :
    Measurable fun p : ℝ × Torus d => S.ρ N (Q54c.clampT S.T p.1) p.2 := by
  have hT : 0 ≤ S.T := S.hT.le
  have hρc : ∀ r, Continuous (S.ρ N (Q54c.clampT S.T r)) := fun r =>
    Q54c.isCk_continuous ((hS.mean_field.regular N hN).1 _ (Q54c.clampT_mem hT r)).1
  have hpt : ∀ x, Measurable fun r => S.ρ N (Q54c.clampT S.T r) x := fun x => by
    refine Continuous.measurable ?_
    have h1 : ContinuousOn (fun u => S.ρ N u x) (Set.Icc 0 S.T) := a8p_rho_cont_time hS hN x
    have h2 : Continuous fun r : ℝ => (⟨Q54c.clampT S.T r, Q54c.clampT_mem hT r⟩ : Set.Icc (0 : ℝ) S.T) :=
      (Q54c.continuous_clampT S.T).subtype_mk _
    exact (h1.comp_continuous (Q54c.continuous_clampT S.T) (fun r => Q54c.clampT_mem hT r))
  exact Q54c.measurable_uncurry_rho (fun r => S.ρ N (Q54c.clampT S.T r)) hρc hpt

end Ctx

end HRS.Main.A8P
