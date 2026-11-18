import HRS.MP.SelfSimP5CoreA

/-!
# MP-SSP5CORE: `p4_core_cpt` (level chain of P4 with the Fisher information `fisherCptW`)

Namespace `HRS.MP.SelfSimP5Core`.  The chain (5)-(8) of `SelfSimP4Final` for a time-independent potential, where the
lsc statement (7) for the Fisher information is the compact-support version `p5c_fisher_lsc`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory Set
open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSim HRS HRS.MP.SelfSimP4
open HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimP5Core

variable {d : ℕ}

theorem p4_core_cpt_proof {N : ℕ} {θ : ℝ} (hθ : 0 < θ) {V : EucConfig d N → ℝ} {b : EucConfig d N → EucConfig d N}
    {T : ℝ} (hT : 0 ≤ T) (hV : P4PotHyp (fun _ => V) (fun _ => b) T)
    {μ : ℝ → Measure (EucConfig d N)} (hμ : P4FlowHyp θ (fun _ => b) T μ)
    (hfin : gibbsEntropyW (p4GibbsOf θ V) (μ 0) < ⊤) :
    ∀ t ∈ Icc (0 : ℝ) T,
      gibbsEntropyW (p4GibbsOf θ V) (μ t) +
        ((ENNReal.ofReal θ * ∫⁻ r in Icc (0 : ℝ) t, fisherCptW (p4GibbsOf θ V) (μ r) : ℝ≥0∞) : EReal) ≤
      gibbsEntropyW (p4GibbsOf θ V) (μ 0) := by
  obtain ⟨C, h5⟩ := HRS.MP.SelfSimP4Mol.p4_mollified_ineq_proof hθ hT hV hμ
  have hFp := hμ.prob
  have : IsProbabilityMeasure (μ 0) := hμ.prob 0
  obtain ⟨e, he, hinit⟩ := p4_initial_jensen_proof hθ hT hV hfin
  obtain ⟨Cm, hCm, hmom⟩ := hμ.mom
  have hv : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hv0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h7 : ∀ t ∈ Set.Icc (0 : ℝ) T,
      gibbsEntropyW (p4GibbsOf θ V) (μ t) ≤
        liminf (fun n : ℕ => ((p4Free θ V (p4Mol (1 / ((n : ℝ) + 1)) (μ t)) : ℝ) : EReal)) atTop ∧
      fisherCptW (p4GibbsOf θ V) (μ t) ≤
        liminf (fun n : ℕ => p4Diss θ V (p4Mol (1 / ((n : ℝ) + 1)) (μ t))) atTop := fun t ht => by
    have : IsProbabilityMeasure (μ t) := hμ.prob t
    exact ⟨(p4_mollify_lsc_proof hθ hT hV ht (lt_of_le_of_lt (hmom t ht) hCm) hv hv0).1,
      p5c_fisher_lsc hθ (p4m_contDiff_of_hyp hV t) (μ t) hv hv0⟩
  obtain ⟨D, -, hDI, hDE⟩ := p4_level_bookkeeping_proof (θ := θ) (T := T) (C := C)
    (F := fun v t => p4Free θ V (p4Mol v (μ t)))
    (Dv := fun v r => p4Diss θ V (p4Mol v (μ r)))
    (H := fun t => gibbsEntropyW (p4GibbsOf θ V) (μ t))
    (I := fun r => fisherCptW (p4GibbsOf θ V) (μ r))
    hθ (fun v hv => (h5 v hv).1) (fun v hv => (h5 v hv).2) he hinit
    (fun t ht => (h7 t ht).1) (fun r hr => (h7 r hr).2)
  intro t ht
  have hle : ENNReal.ofReal θ * ∫⁻ r in Icc (0 : ℝ) t, fisherCptW (p4GibbsOf θ V) (μ r) ≤
      ENNReal.ofReal θ * ∫⁻ r in Icc (0 : ℝ) t, D r := by
    refine mul_le_mul_right (lintegral_mono_ae ?_) _
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => hDI r ?_)
    exact ⟨hr.1, hr.2.trans ht.2⟩
  exact le_trans (add_le_add le_rfl (EReal.coe_ennreal_le_coe_ennreal_iff.2 hle)) (hDE t ht)

example := (@p4_core_cpt_proof : type_of% @HRS.MP.SelfSimP5Core.p4_core_cpt)

end HRS.MP.SelfSimP5Core
