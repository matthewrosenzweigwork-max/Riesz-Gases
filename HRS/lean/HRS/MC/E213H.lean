import HRS.MC.E213E1
import HRS.Sections.Sec7Setting
import HRS.Sections.AllTimeAux1
import HRS.Equilibrium.ReferenceSmallness
import HRS.MD.EQLawFlow

/-!
# Packet E213H, L4: existence of a prepared realization for every `N ≥ 1`

`e213h_exists_prepared_realization`: for every regime `R` and `N ≥ 1` there is a probability space carrying
an initial datum `X₀ ∼ Q₀ = modulatedGibbs ... N β₀ (withDensityReal ρ₀)`, an independent vector Brownian motion
`W` and a global filtered strong solution `X`.  Template: `HRS.MD.EQLawFlow.eq_flow_exists_proof`, with the
global solution supplied by `HRS.MC.E213E.e213e_exists_global_filtered`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213H

open HRS HRS.Sec7

variable {d : ℕ}

lemma e213h_symNonpos_neg_one (n : ℕ) : Torus.SymNonpos (-1 : Matrix (Fin n) (Fin n) ℝ) := by
  unfold Torus.SymNonpos Torus.symPart
  simp only [Matrix.transpose_neg, Matrix.transpose_one]
  have : (-((1 / 2 : ℝ) • ((-1 : Matrix (Fin n) (Fin n) ℝ) + -1))) = 1 := by
    rw [← two_smul ℝ (-1 : Matrix (Fin n) (Fin n) ℝ), smul_smul]
    norm_num
  rw [this]
  exact Matrix.PosSemidef.one

lemma e213h_isCk_two (R : Regime d) : Torus.IsCk 2 R.D.V :=
  PDE.ClassicalAux.isCk_of_le (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (m := 2)
    (by first | norm_num | simp | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) R.hV

theorem e213h_exists_prepared_realization (R : Regime d) (N : ℕ) (hN : 1 ≤ N) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
      PreparedRealization R.D P
        (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X := by
  classical
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
  exact ⟨_, inferInstance, P, inferInstance, Prod.fst, ofCoords W', X,
    ⟨hmapfst, hBM, hind', hS, ⟨ℱ', W'', hF⟩⟩⟩

end HRS.MC.E213H
