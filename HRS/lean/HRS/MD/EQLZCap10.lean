import HRS.MD.EQLZVocab
import HRS.MD.EQLZCap9

/-!
# EQ-LZ packet CAP, final file: `eqlz_cap_proof`

The statement of `HRS.MD.EQLZ.eqlz_cap` (`HRS/MD/EQLZSpec.lean`, copied verbatim; tie in `EQLZCapTie.lean`), proved
from the abstract core theorem `cap_core` on `𝕋^{Nd}` through `d1_configEquiv`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MD.EQLZ.Cap

variable {d N : ℕ}

/-- `F` as a function on the big torus. -/
def toTor (F : Config d N → ℝ) : Torus (N * d) → ℝ := fun x => F ((d1_configEquiv d N).symm x)

theorem configLift_eq (F : Config d N → ℝ) : configLift (fun _ => F) 0 = d1_cl (toTor F) := by
  funext Y; simp [configLift, d1_cl, toTor]

theorem configGradSq_eq (F : Config d N → ℝ) (X : Config d N) :
    LZ.configGradSq F X = capG (toTor F) (d1_configEquiv d N X) := by
  unfold LZ.configGradSq
  rw [← capG_eq_grad, EuclideanSpace.norm_sq_eq, ← Equiv.sum_comp (d1_idx d N)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Real.norm_eq_abs, sq_abs, d1_grad_apply, configLift_eq]

theorem eqlz_cap_proof (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (F : Config d N → ℝ)
    (hF : LZ.IsLZTest (canonicalGibbs (periodicRiesz d s) V N β) F) :
    ∃ G : ℕ → Config d N → ℝ, (∀ k, IsSmoothCfg (G k)) ∧
      Tendsto (fun k => ∫ x, (G k x - F x) ^ 2 ∂(canonicalGibbs (periodicRiesz d s) V N β)) atTop (𝓝 0) ∧
      Tendsto (fun k => ∫ x, LZ.configGradSq (G k) x ∂(canonicalGibbs (periodicRiesz d s) V N β)) atTop
        (𝓝 (∫ x, LZ.configGradSq F x ∂(canonicalGibbs (periodicRiesz d s) V N β))) := by
  set μ := canonicalGibbs (periodicRiesz d s) V N β with hμ
  obtain ⟨hprob, hac, c0, hc0, hle⟩ := gibbs_facts (N := N) hd s hs0 hsd hV hβ
  have : IsProbabilityMeasure μ := hprob
  set e := d1_configEquiv d N with he
  set ν : Measure (Torus (N * d)) := μ.map e with hν
  have hνc := map_le_of_le hle
  have hν0 : ν (badSet d N) = 0 := map_badSet_null hac (by omega)
  set Φ := toTor F with hΦdef
  have hΦm : Measurable Φ := hF.measurable.comp e.symm.measurable
  have hΦe : ∀ X, Φ (e X) = F X := fun X => by simp [hΦdef, toTor, he]
  have h2 : MemLp Φ 2 ν := by
    rw [hν, memLp_map_measure_iff hΦm.aestronglyMeasurable e.measurable.aemeasurable]
    have : Φ ∘ e = F := funext hΦe
    rw [this]; exact hF.memLp
  have hcd : ContDiffOn ℝ 1 (Torus.lift Φ) {y | Torus.mk y ∉ badSet d N} := by
    have h1 : ContDiffOn ℝ 1 (d1_cl Φ) (LZ.coverFree d N) := by
      rw [← configLift_eq]; exact hF.c1
    have h3 : Torus.lift Φ = d1_cl Φ ∘ (d1_eucEquiv d N).symm := by
      rw [d1_cl_eq]; funext y; simp
    rw [h3]
    refine h1.comp (d1_eucEquiv d N).symm.contDiff.contDiffOn (fun y hy => ?_)
    show (fun i => Torus.mk ((d1_eucEquiv d N).symm y i)) ∉ collisionSet d N
    rw [← d1_configEquiv_symm_mk]; exact hy
  have hE : Integrable (capG Φ) ν := by
    rw [hν, integrable_map_measure (measurable_capG Φ).aestronglyMeasurable e.measurable.aemeasurable]
    have : capG Φ ∘ e = LZ.configGradSq F := funext fun X => (configGradSq_eq F X).symm
    rw [this]; exact hF.energy
  obtain ⟨G, hGs, hG1, hG2⟩ := cap_core ν (isClosed_badSet d N) hν0 hc0 hνc (cutFam_pair hd)
    hΦm h2 hcd hE
  have hGm : ∀ k, Measurable (G k) := fun k =>
    (continuous_of_cdiff (isSmooth_cdiff (hGs k))).measurable
  refine ⟨fun k => G k ∘ e, fun k => ?_, ?_, ?_⟩
  · simpa [IsSmoothCfg, he] using hGs k
  · refine hG1.congr fun k => ?_
    have hm : Measurable (fun x => (G k x - Φ x) ^ 2) := ((hGm k).sub hΦm).pow_const 2
    rw [hν, integral_map e.measurable.aemeasurable hm.aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all _ fun X => ?_)
    simp only [Function.comp, hΦe]
  · have hGq : ∀ k, ∫ x, LZ.configGradSq (G k ∘ e) x ∂μ = ∫ x, capG (G k) x ∂ν := by
      intro k
      rw [hν, integral_map e.measurable.aemeasurable (measurable_capG (G k)).aestronglyMeasurable]
      refine integral_congr_ae (ae_of_all _ fun X => ?_)
      rw [configGradSq_eq]
      congr 2
      funext x; simp [toTor, he]
    have hF' : ∫ x, LZ.configGradSq F x ∂μ = ∫ x, capG Φ x ∂ν := by
      rw [hν, integral_map e.measurable.aemeasurable (measurable_capG Φ).aestronglyMeasurable]
      exact integral_congr_ae (ae_of_all _ fun X => configGradSq_eq F X)
    rw [hF']
    exact hG2.congr fun k => (hGq k).symm

end HRS.MD.EQLZ.Cap
