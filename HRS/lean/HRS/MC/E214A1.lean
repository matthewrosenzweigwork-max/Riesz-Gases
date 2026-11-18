import HRS.MC.E213H
import HRS.MC.E213A
import HRS.Main.HeadlineEdgeworth
import HRS.Stochastic.Particle
import HRS.Stochastic.SelectedFlow

/-!
# Packet E214A, lemma 2: non-vacuity of the particle-system antecedents of `IsWindowEdgeworth.expansion`

`e214_exists_selected`: for `N ≥ 2`, `T > 0`, `a ≥ 0` there is a probability space carrying a
`SelectedFlow` particle system (with `a + T` horizon), a filtered strong solution structure and
initial law `modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0`.  Copy of
`HRS.MC.E213H.e213h_exists_prepared_realization`, ending with `SelectedFlow`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214A

open HRS HRS.Sec7 HRS.Main HRS.MC.E213H

variable {d : ℕ}

theorem e214_exists_selected (S : PreparedData d) (β₀ m : ℝ) (hE : EdgeworthHyp S β₀ m)
    (N : ℕ) (hN : 2 ≤ N) (T a : ℝ) (hT : 0 < T) (ha : 0 ≤ a) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
      SelectedFlow P S.dyn (a + T) X₀ W X ∧
      (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
        (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) ∧
      law P X₀ = modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0 := by
  classical
  set R : Regime d := HRS.MC.E213A.regimeOfPrepared S β₀ hE with hR
  haveI : BorelSpace (Torus d) := Pi.borelSpace
  haveI : BorelSpace (Config d N) := Pi.borelSpace
  have hd1 : 1 ≤ d := by have := R.hd; omega
  have hcont : Continuous R.ρ₀ :=
    PDE.MFAux.continuous_of_isCk (ContDiff.of_le
      (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift R.ρ₀) from R.hρ₀.smooth)
      (by exact_mod_cast le_top))
  have hβ₀ : 0 ≤ R.β₀ := by rcases R.hβ₀ with h | ⟨_, h⟩ <;> linarith
  set μ : Measure (Config d N) :=
    modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀) with hμ
  haveI hμP : IsProbabilityMeasure μ :=
    alltime_gibbs_prob hd1 R.D.hs0 R.D.hsd R.hρ₀.density hcont (by omega) hβ₀
  have hμae : ∀ᵐ X ∂μ, X ∉ collisionSet d N := by
    have h : μ ≪ Measure.pi (fun _ : Fin N => withDensityReal R.ρ₀) := by
      rw [hμ]
      unfold modulatedGibbs
      exact (withDensity_absolutelyContinuous _ _).smul_left _
    exact h.ae_le (HRS.External.RefSmall.ae_not_collision hd1 R.hρ₀.density N)
  obtain ⟨W', hW'm, hW0, hWc, hind, hBF⟩ :=
    exists_enlargement_indep (Fin N × Fin d) (Config d N) μ
  set P : Measure (Config d N × ((Fin N × Fin d) → WienerSeq)) :=
    μ.prod (Measure.pi fun _ : (Fin N × Fin d) => wienerMeasure) with hP
  haveI : IsProbabilityMeasure P := inferInstance
  set ℱ := generatedFiltration P Prod.fst measurable_fst W' hW'm with hℱ
  have hmapfst : P.map Prod.fst = μ := by
    rw [hP, Measure.map_fst_prod, measure_univ, one_smul]
  have hdist : ∀ᵐ ω ∂P, (Prod.fst ω : Config d N) ∉ collisionSet d N := by
    have hmp : MeasurePreserving
        (Prod.fst : Config d N × ((Fin N × Fin d) → WienerSeq) → Config d N) P μ :=
      ⟨measurable_fst, hmapfst⟩
    exact hmp.quasiMeasurePreserving.ae hμae
  have hBM : IsVectorBrownian P (ofCoords W') :=
    isVectorBrownian_of_isBrownianFiltration P ℱ W' hBF
  have hind' : IndepFun (Prod.fst : Config d N × ((Fin N × Fin d) → WienerSeq) → Config d N)
      (fun ω => fun t => (ofCoords W') t ω) P :=
    hind.comp measurable_id (MD.EQLawFlow.eqlaw_measurable_ofCoordsPath d N)
  obtain ⟨X, hS, ℱ', W'', hF⟩ := HRS.MC.E213E.e213e_exists_global_filtered P R.D R.hd
    (by rw [R.hM]; exact e213h_symNonpos_neg_one d) (e213h_isCk_two R) Prod.fst measurable_fst hdist
    (ofCoords W') hBM hind'
  have hpos : 0 < a + T := by linarith
  have hwp := HRS.particle_wellposed_proof P R.D R.hd hN
    (by rw [R.hM]; exact e213h_symNonpos_neg_one d) (e213h_isCk_two R) Prod.fst measurable_fst hdist
    (ofCoords W') hBM hind' (a + T) hpos
  exact ⟨_, inferInstance, P, inferInstance, Prod.fst, ofCoords W', X,
    ⟨measurable_fst, hdist, hBM, hind', Or.inl ⟨hS (a + T), hwp.2⟩⟩, ⟨ℱ', W'', hF⟩, hmapfst⟩

end HRS.MC.E214A

end
