import HRS.Uniform.Q54cAux41

/-!
# Q54c, part 42: regularity of the propagated test functions, decomposition lemma for the finite-dimensional laws
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54c

open HRS HRS.PDE

variable {d : ℕ}

/-- If `V = G + W(Y₀)` with `G ⟂ Y₀`, the law of `V` depends only on the laws of `G` and `Y₀`. -/
theorem map_eq_of_decomp {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {E F : Type*} [MeasurableSpace E] [MeasurableSpace F] [Add F] [MeasurableAdd₂ F]
    (G : Ω → F) (Y₀ : Ω → E) (G' : Ω' → F) (Y₀' : Ω' → E) (W : E → F) (hW : Measurable W)
    (hG : Measurable G) (hY : Measurable Y₀) (hG' : Measurable G') (hY' : Measurable Y₀')
    (hind : IndepFun G Y₀ P) (hind' : IndepFun G' Y₀' P') (hlawG : P.map G = P'.map G')
    (hlawY : P.map Y₀ = P'.map Y₀') (V : Ω → F) (V' : Ω' → F)
    (hV : ∀ ω, V ω = G ω + W (Y₀ ω)) (hV' : ∀ ω, V' ω = G' ω + W (Y₀' ω)) :
    P.map V = P'.map V' := by
  have hf : Measurable fun z : F × E => z.1 + W z.2 :=
    measurable_fst.add (hW.comp measurable_snd)
  have e1 : V = (fun z : F × E => z.1 + W z.2) ∘ (fun ω => (G ω, Y₀ ω)) := funext hV
  have e2 : V' = (fun z : F × E => z.1 + W z.2) ∘ (fun ω => (G' ω, Y₀' ω)) := funext hV'
  have hp := (indepFun_iff_map_prod_eq_prod_map_map hG.aemeasurable hY.aemeasurable).1 hind
  have hp' := (indepFun_iff_map_prod_eq_prod_map_map hG'.aemeasurable hY'.aemeasurable).1 hind'
  rw [e1, e2, ← Measure.map_map hf (hG.prodMk hY), ← Measure.map_map hf (hG'.prodMk hY'),
    hp, hp', hlawG, hlawY]

namespace PdeSetup

variable {P : PdeSetup d} {D : DynData d} {ν₀ : ℝ} {μ : ℝ → Torus d → ℝ} (h : P.Data D ν₀ μ)

include h

theorem Data.prop_regular {t : ℝ} (ht : t ∈ Set.Icc 0 P.T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    {σ : ℝ} (hσ : σ ∈ Set.Icc 0 t) :
    Continuous (propagator D μ σ t φ) ∧ Torus.IsCk 1 (propagator D μ σ t φ) := by
  have hD := HRS.Uniform.Q54.dom_smooth (J := P.n + 4) hφ
  by_cases h0 : t = 0
  · subst h0
    have : σ = 0 := le_antisymm hσ.2 hσ.1
    subst this
    rw [HRS.Uniform.Q54.prop_self_zero P.hd P.s P.hs0 P.hsd (P.n + 4) P.R P.MB P.Λ P.VB D ν₀ P.T μ
      h.hA hφ]
    refine ⟨hD.1, ?_⟩
    unfold Torus.IsSmooth Torus.IsCk at hφ
    unfold Torus.IsCk
    exact hφ.of_le (by norm_num)
  · have ht' : t ∈ Set.Ioc 0 P.T := ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), ht.2⟩
    obtain ⟨C, Cs, -, -, hmain⟩ := adjoint_torus_classical P.hd P.s P.hs0 P.hsd (P.n + 4) P.hn P.R P.MB
      P.Λ P.VB
    obtain ⟨hcls, hpe, -, -⟩ := hmain D ν₀ P.T μ h.hA t ht' φ hD.1 hD.2
    have hc2 := hcls.c2 σ hσ
    have hpe' := hpe σ hσ
    rw [hpe']
    refine ⟨?_, hc2.of_le (by norm_num)⟩
    have := (HRS.Uniform.Q54.prop_facts P.hd P.s P.hs0 P.hsd (P.n + 4) P.hn P.R P.MB P.Λ P.VB D ν₀ P.T μ
      h.hA ht' hD hσ).2
    rw [hpe'] at this
    exact this

end PdeSetup

end HRS.Uniform.Q54c
