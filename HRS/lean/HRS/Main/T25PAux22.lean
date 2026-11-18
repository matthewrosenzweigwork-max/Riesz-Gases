import HRS.Main.T25PAux21

/-!
# T25P, part 22: enlargement along a coupling of the initial field

Given a coupling `π₀` of `(law of g(X₀), ν)` on `E_m × E_m` (`g : Config → E_m` measurable, e.g. `η_N^0`), the first
enlargement (`t25p_init_enlargement`) with the kernel `K x = π₀.condKernel (g x)` gives a filtered solution on a larger space
with an `ℱ'_0`-measurable `η' ~ ν` such that `(g(X₀∘π), η')` has law `π₀`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF

variable {d : ℕ}

theorem t25p_enlarge_coupled (m : ℝ) (N : ℕ)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsFilteredSolution P ℱ W' W X)
    (hX0 : ∀ᵐ ω ∂P, X 0 ω = X₀ ω) (g : Config d N → NegSobolev d m) (hg : Measurable g)
    (ν : Measure (NegSobolev d m)) (π₀ : Measure (NegSobolev d m × NegSobolev d m))
    (hπ₀ : IsCoupling π₀ (P.map (fun ω => g (X₀ ω))) ν) :
    ∃ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (π : Ω' → Ω) (_ : MeasurePreserving π P' P) (ℱ' : Filtration ℝ mΩ')
      (η' : Ω' → NegSobolev d m),
      IsFilteredSolution P' ℱ' (fun t ω' k => W' t (π ω') k) (fun t ω' => W t (π ω'))
        (fun t ω' => X t (π ω')) ∧
      Measurable[ℱ' 0] η' ∧ P'.map η' = ν ∧
      P'.map (fun ω' => (g (X₀ (π ω')), η' ω')) = π₀ := by
  classical
  have hX0m : Measurable (X 0) := (hF.adapted 0).mono (ℱ.le 0) le_rfl
  have hX₀ae : AEMeasurable X₀ P := hX0m.aemeasurable.congr hX0
  have : IsProbabilityMeasure (P.map X₀) := inferInstance
  have hgX : AEMeasurable (fun ω => g (X₀ ω)) P := hg.comp_aemeasurable hX₀ae
  have : IsProbabilityMeasure (P.map (fun ω => g (X₀ ω))) := inferInstance
  have : IsProbabilityMeasure π₀ := hπ₀.isProbabilityMeasure
  have : Nonempty (NegSobolev d m) := ⟨0⟩
  obtain ⟨Ω', mΩ', P', hP', π, hπ, ℱ', η', -, hsol, hη'0, hlaw⟩ :=
    t25p_init_enlargement m N P X₀ W X ℱ W' hF hX0 (π₀.condKernel.comap g hg)
  have hmap : (P.map X₀).map g = π₀.fst := by
    rw [AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hX₀ae]
    exact hπ₀.1.symm
  have hpairae : AEMeasurable (fun ω' => (X₀ (π ω'), η' ω')) P' :=
    (hX₀ae.comp_quasiMeasurePreserving hπ.quasiMeasurePreserving).prodMk
      ((hη'0.mono (ℱ'.le 0) le_rfl).aemeasurable)
  have hpair2 : AEMeasurable (fun ω' => (g (X₀ (π ω')), η' ω')) P' :=
    (hg.prodMap measurable_id).comp_aemeasurable hpairae
  have hcomp : P'.map (fun ω' => (g (X₀ (π ω')), η' ω')) = π₀ := by
    have h1 : (fun ω' => (g (X₀ (π ω')), η' ω')) =
        (fun w : Config d N × NegSobolev d m => (g w.1, w.2)) ∘ (fun ω' => (X₀ (π ω'), η' ω')) := rfl
    rw [h1, ← AEMeasurable.map_map_of_aemeasurable (g := fun w : Config d N × NegSobolev d m => (g w.1, w.2))
      (hg.prodMap measurable_id).aemeasurable hpairae, hlaw,
      t25p_init_law (P.map X₀) hg π₀.condKernel, hmap]
    exact Measure.disintegrate π₀ π₀.condKernel
  refine ⟨Ω', mΩ', P', hP', π, hπ, ℱ', η', hsol, hη'0, ?_, hcomp⟩
  have : P'.map η' = (P'.map (fun ω' => (g (X₀ (π ω')), η' ω'))).map Prod.snd := by
    rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hpair2]
    rfl
  rw [this, hcomp]
  exact hπ₀.2

end HRS.T25P
