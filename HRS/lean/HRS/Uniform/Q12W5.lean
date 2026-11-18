import HRS.Uniform.Q12W4b
import HRS.Uniform.Q12W3c
import HRS.Uniform.Q12Aux7

/-!
# Q12, part W5: Lemma 3.23 (`energy_W2`) from Peyre's `W_2`-`Ḣ^{-1}` inequality

The only input that is not proved here is `PeyreW2 d` (the classical comparison between the quadratic
Wasserstein distance and the `Ḣ^{-1}` norm for densities bounded below, Peyre 2018); it is the exact
analogue of the dynamic transport bound `(U:eq:negative-Sobolev-transport)` of the TeX proof.
-/

noncomputable section

open HRS MeasureTheory Filter Topology
open HRS.CoercAux
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q12

variable {d : ℕ}

/-- Peyre's inequality on the flat torus: `W_2(f dx, g dx) ≤ C m^{-1/2} ‖f - g‖_{Ḣ^{-1}}` for smooth
probability densities with `f > 0` and `g ≥ m > 0`.  (`‖h‖²_{Ḣ^{-1}} = (4π²)⁻¹ hmSum`; the constant absorbs `4π²`.) -/
def PeyreW2 (d : ℕ) : Prop :=
  ∃ Cp : ℝ, 0 < Cp ∧ ∀ f g : Torus d → ℝ, IsProbDensity f → IsProbDensity g → Torus.IsSmooth f →
    Torus.IsSmooth g → (∀ x, 0 < f x) → ∀ m : ℝ, 0 < m → (∀ x, m ≤ g x) →
      torusWassersteinE 2 (withDensityReal f) (withDensityReal g) ≤
        ENNReal.ofReal (Cp / Real.sqrt m * Real.sqrt (hmSum f g))


/-- The `W_2` distance between an empirical measure and a density, given the smearing at scale `t`:
`W_2(μ_X, μ) ≤ 2 √(d t/8) + C_P m^{-1/2} (hmSum)^{1/2}`. -/
theorem q12_W_chain (hP : PeyreW2 d) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ {t : ℝ}, 0 < t → ∀ {N : ℕ}, 0 < N → ∀ (X : Config d N)
      (ρ : Torus d → ℝ), IsProbDensity ρ → ∀ {m : ℝ}, 0 < m → (∀ x, m ≤ ρ x) →
      torusWassersteinE 2 (empirical X) (withDensityReal ρ) ≤
        ENNReal.ofReal (2 * Real.sqrt (d * t / 8) + Cp / Real.sqrt m *
          Real.sqrt (hmSum (smearDens d t (empirical X)) (smearDens d t (withDensityReal ρ)))) := by
  obtain ⟨Cp, hCp, hPey⟩ := hP
  refine ⟨Cp, hCp, fun {t} ht {N} hN X ρ hρ {m} hm hρm => ?_⟩
  haveI := PDE.MFSemigroup.isProb_withDensityReal hρ
  haveI := empirical_isProbabilityMeasure hN X
  set μ : Measure (Torus d) := withDensityReal ρ with hμ
  set ν : Measure (Torus d) := empirical X with hν
  set f := smearDens d t ν with hf
  set g := smearDens d t μ with hg
  have hfd : IsProbDensity f := q12_isProbDensity_smearDens ht ν
  have hgd : IsProbDensity g := q12_isProbDensity_smearDens ht μ
  haveI : IsProbabilityMeasure (withDensityReal f) := PDE.MFSemigroup.isProb_withDensityReal hfd
  haveI : IsProbabilityMeasure (withDensityReal g) := PDE.MFSemigroup.isProb_withDensityReal hgd
  have hm1 : torusWassersteinE 2 ν (withDensityReal f) ≤ ENNReal.ofReal (Real.sqrt (d * t / 8)) := by
    have := q12_W_smear ht ν
    rwa [q12_smearM_eq ht ν] at this
  have hm2 : torusWassersteinE 2 μ (withDensityReal g) ≤ ENNReal.ofReal (Real.sqrt (d * t / 8)) := by
    have := q12_W_smear ht μ
    rwa [q12_smearM_eq ht μ] at this
  have hm3 : torusWassersteinE 2 (withDensityReal g) μ ≤ ENNReal.ofReal (Real.sqrt (d * t / 8)) :=
    (q12_W_symm 2 (withDensityReal g) μ).trans hm2
  have hsf : Torus.IsSmooth f := q12_isSmooth_smearDens ht ν
  have hsg : Torus.IsSmooth g := q12_isSmooth_smearDens ht μ
  have hPf := hPey f g hfd hgd hsf hsg (fun x => q12_smearDens_pos ht ν x) m hm
    (fun x => q12_smearDens_ge ht hρ hρm x)
  have t1 := q12_W_triangle 2 (by norm_num) ν (withDensityReal f) μ
  have t2 := q12_W_triangle 2 (by norm_num) (withDensityReal f) (withDensityReal g) μ
  have hb : 0 ≤ Cp / Real.sqrt m * Real.sqrt (hmSum f g) := by positivity
  calc torusWassersteinE 2 ν μ ≤ torusWassersteinE 2 ν (withDensityReal f) +
        torusWassersteinE 2 (withDensityReal f) μ := t1
    _ ≤ torusWassersteinE 2 ν (withDensityReal f) +
        (torusWassersteinE 2 (withDensityReal f) (withDensityReal g) +
          torusWassersteinE 2 (withDensityReal g) μ) := by gcongr
    _ ≤ ENNReal.ofReal (Real.sqrt (d * t / 8)) +
        (ENNReal.ofReal (Cp / Real.sqrt m * Real.sqrt (hmSum f g)) +
          ENNReal.ofReal (Real.sqrt (d * t / 8))) := by gcongr
    _ = ENNReal.ofReal (2 * Real.sqrt (d * t / 8) + Cp / Real.sqrt m * Real.sqrt (hmSum f g)) := by
        rw [← ENNReal.ofReal_add hb (Real.sqrt_nonneg _),
          ← ENNReal.ofReal_add (Real.sqrt_nonneg _) (add_nonneg hb (Real.sqrt_nonneg _))]
        congr 1; ring

end HRS.Uniform.Q12
