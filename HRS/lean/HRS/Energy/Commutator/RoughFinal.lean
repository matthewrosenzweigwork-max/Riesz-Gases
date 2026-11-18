import HRS.Energy.Commutator.RoughMain
import HRS.Energy.Commutator.RoughD1
import HRS.Energy.Commutator.RoughReduce

/-!
# Assembly of `stress_rough` (packet CM-S3)

The statement is proved here for the explicit expansion of `quadForm`; `Stress.lean` unfolds the
definition.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.KernelAux HRS.Commutator.FourierAux HRS.Commutator.RoughAux HRS.Commutator.RoughHeat
  HRS.Commutator.RoughKernel HRS.Commutator.RoughLimit HRS.Commutator.RoughMain

namespace HRS.Commutator.RoughFinal

variable {d : ℕ}

/-- The diagonal is null for an atomless finite measure. -/
theorem ae_ne_of_noAtoms (m : Measure (Torus d)) [IsFiniteMeasure m] (h : ∀ x, m {x} = 0) :
    ∀ᵐ p ∂(m.prod m), p.1 ≠ p.2 := by
  have hmeas : MeasurableSet {p : Torus d × Torus d | p.1 = p.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  have h0 : (m.prod m) {p : Torus d × Torus d | p.1 = p.2} = 0 := by
    rw [Measure.prod_apply hmeas]
    have : ∀ x : Torus d, m (Prod.mk x ⁻¹' {p : Torus d × Torus d | p.1 = p.2}) = 0 := fun x => by
      have e : Prod.mk x ⁻¹' {p : Torus d × Torus d | p.1 = p.2} = {x} := by
        ext y; simp [eq_comm]
      rw [e]; exact h x
    simp only [this, lintegral_zero]
  rw [ae_iff]
  simpa using h0


theorem d0_case {l : ℝ} (hl : 0 ≤ l) (v : Torus 0 → Euc 0) (ν μ : Measure (Torus 0)) [IsFiniteMeasure ν]
    [IsFiniteMeasure μ] :
    ((∫ x, ∫ y, commKernel (sliceGrad 0 l) v x y ∂ν ∂ν) -
        2 * (∫ x, ∫ y, commKernel (sliceGrad 0 l) v x y ∂μ ∂ν) + ∫ x, ∫ y, commKernel (sliceGrad 0 l) v x y ∂μ ∂μ = 0) ∧
    0 ≤ (∫ x, ∫ y, sliceGfull 0 l (x - y) ∂ν ∂ν) - 2 * (∫ x, ∫ y, sliceGfull 0 l (x - y) ∂μ ∂ν) +
      ∫ x, ∫ y, sliceGfull 0 l (x - y) ∂μ ∂μ := by
  haveI : Subsingleton (Torus 0) := ⟨fun a b => funext fun i => i.elim0⟩
  have hk : ∀ x y : Torus 0, commKernel (sliceGrad 0 l) v x y = 0 := fun x y => by
    unfold commKernel; rw [if_pos (Subsingleton.elim x y)]
  have hpsi : ∀ (x : Torus 0) (u : ℝ), psiFn x u = 0 := fun x u => by
    unfold psiFn
    refine (tsum_congr fun k => ?_).trans tsum_zero
    have : k = 0 := funext fun i => i.elim0
    simp [this]
  have hG : ∀ x y : Torus 0, sliceGfull 0 l (x - y) = 1 / l := fun x y => by
    unfold sliceGfull sliceG
    simp [hpsi]
  refine ⟨by simp [hk], ?_⟩
  simp only [hG, integral_const, smul_eq_mul]
  have : (ν.real Set.univ * (ν.real Set.univ * (1 / l))) - 2 * (ν.real Set.univ * (μ.real Set.univ * (1 / l))) +
      μ.real Set.univ * (μ.real Set.univ * (1 / l)) = (1 / l) * (ν.real Set.univ - μ.real Set.univ) ^ 2 := by ring
  rw [this]
  positivity


theorem core_pos (hd : 1 ≤ d) {l : ℝ} (hl : 0 ≤ l) {L : ℝ} (hL : 0 ≤ L) {v : Torus d → Euc d}
    (hv : IsLipschitzVF L v) (ν μ : Measure (Torus d)) [IsFiniteMeasure ν] [IsFiniteMeasure μ]
    (hneut : l = 0 → ν Set.univ = μ Set.univ)
    (hatom : 2 ≤ d → (∀ x, ν {x} = 0) ∧ ∀ x, μ {x} = 0)
    (hint : Integrable (fun p : Torus d × Torus d => sliceGfull d l (p.1 - p.2)) ((ν + μ).prod (ν + μ))) :
    |(∫ x, ∫ y, commKernel (sliceGrad d l) v x y ∂ν ∂ν) -
        2 * (∫ x, ∫ y, commKernel (sliceGrad d l) v x y ∂μ ∂ν) + ∫ x, ∫ y, commKernel (sliceGrad d l) v x y ∂μ ∂μ| ≤
      (2 * (2 * d + 1)) * L * ((∫ x, ∫ y, sliceGfull d l (x - y) ∂ν ∂ν) -
        2 * (∫ x, ∫ y, sliceGfull d l (x - y) ∂μ ∂ν) + ∫ x, ∫ y, sliceGfull d l (x - y) ∂μ ∂μ) := by
  obtain ⟨s, hsm, hs, hsint, hred⟩ := RoughReduce.reduce (ν := ν) (μ := μ)
  set m : Measure (Torus d) := ν + μ with hm
  have hvc : Continuous v := lipschitzVF_continuous hL hv
  -- the two kernels
  have hGm : Measurable (Function.uncurry fun x y : Torus d => sliceGfull d l (x - y)) :=
    (EnergyAux.measurable_sliceGfull l).comp (measurable_fst.sub measurable_snd)
  have hGs : ∀ x y : Torus d, sliceGfull d l (x - y) = sliceGfull d l (y - x) := fun x y => by
    unfold sliceGfull
    rw [show y - x = -(x - y) by abel, EnergyAux.sliceG_neg]
  have hkk : Integrable (Function.uncurry (kk l v)) (m.prod m) := by
    obtain ⟨A, B, hA, hB, hmaj⟩ := kk_majorant hd hl (d := d)
    have h1 : Integrable (fun p : Torus d × Torus d => L * (A * (sliceGfull d l (p.1 - p.2) - 1 / l) + B))
        (m.prod m) :=
      (((hint.sub (integrable_const (1 / l))).const_mul A).add (integrable_const B)).const_mul L
    refine Integrable.mono' h1 (measurable_kk hvc).aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]
    have := hmaj L v hL hv p.1 p.2
    simp only [sliceGfull, add_sub_cancel_right]
    exact this
  have hQK := hred (fun x y => kk l v x y) (measurable_kk hvc) (kk_symm l v) hkk
  have hQG := hred (fun x y => sliceGfull d l (x - y)) hGm hGs hint
  simp only [commKernel_sliceGrad hl v]
  rw [hQK, hQG]
  have hneut' : l = 0 → ∫ y, s y ∂m = 0 := by
    intro h0
    rw [hsint]
    simp only [Measure.real, hneut h0, sub_self]
  have hgood : ∀ᵐ p ∂(m.prod m), IntW l (p.1 - p.2) ∧
      Tendsto (fun ε : ℝ => kmol l v ε p.1 p.2) (𝓝[>] (0 : ℝ)) (𝓝 (kk l v p.1 p.2)) := by
    rcases (by omega : d = 1 ∨ 2 ≤ d) with rfl | h2
    · refine Filter.Eventually.of_forall fun p => ⟨RoughD1.d1_intW hl _, ?_⟩
      by_cases hp : p.1 = p.2
      · have hc := RoughD1.d1_kk_continuousAt hl hL hv p.1
        rw [hp] at hc ⊢
        exact kmol_tendsto_of_cont hd hl hL hv hc
      · exact kmol_tendsto hd hl hL hv hp
    · obtain ⟨h1, h2'⟩ := hatom h2
      have hm0 : ∀ x, m {x} = 0 := fun x => by
        simp only [hm, Measure.add_apply, h1 x, h2' x, add_zero]
      filter_upwards [ae_ne_of_noAtoms m hm0] with p hp
      exact ⟨intW_of_ne_zero hl (sub_ne_zero.mpr hp), kmol_tendsto hd hl hL hv hp⟩
  have := main_limit hd hl m hsm hs hneut' hL hv hint hgood
  calc _ ≤ 2 * ((2 * d + 1) * L) * ∫ p : Torus d × Torus d, s p.1 * s p.2 * sliceGfull d l (p.1 - p.2) ∂(m.prod m) := this
    _ = _ := by ring

end HRS.Commutator.RoughFinal
