import HRS.ME.Flow417
import HRS.ME.Asm417A
import HRS.ME.Asm417C
import HRS.ME.Asm417D

/-!
# Chunk E, row 4.17: assembly packet E (proof of M7 `integrated_forcing_type`)

* `integrated_forcing_type_proof`: M7, assembled from `single_j_bound_proof` (B2), `modulatedEnergy_integrable_proof`
  (B4 conjunct 1), `forcing_intervalIntegrable_proof` (B5 conjunct 2), `integratedCenteredForcing_aemeasurable`
  and `flow_of_hypotheses_proof` (M0).  The sup over the countable family of times is bounded by the sum over the
  lattice of the single-mode suprema (`lintegral_tsum`), and each term by `single_j_bound_proof`.

The statement of `HRS/ME/Spec417Asm.lean` is copied verbatim; `HRS/ME/Spec417Asm.lean` is not imported.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.ME

variable {d : ℕ}

open HRS HRS.LZ

/-- M7.  `integrated_forcing` with `Ω : Type`: the three conjuncts (integrability of the modulated energy, interval
integrability of the forcing, and the `L²` bound of the supremum over rational times) with the constant
`C = √(C₂ · ∑_j ⟨j⟩^{2(-m+p+d+3)})`. -/
theorem integrated_forcing_type_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hcrit : s = d / 2)
    (β : ℝ) (hβ : 0 < β) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) (m : ℝ) (hm : 24 * (d : ℝ) + 240 ≤ m) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsVectorBrownian P W →
        ProbabilityTheory.IndepFun X₀ (fun ω => fun t : ℝ≥0 => W t ω) P →
        P.map X₀ = canonicalGibbs (periodicRiesz d s) V N β →
        (∀ T' : ℝ, 0 ≤ T' → IsStrongSolution P (PDE.mfData d s hs0 hsd V β hβ) T' X₀ W X) →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        ∀ a : ℝ, 0 ≤ a →
          (∀ f : Torus d → ℝ, Torus.IsSmooth f → ∀ r : ℝ, 0 ≤ r →
            Integrable (fun ω => modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad f))
              (X r.toNNReal ω) (withDensityReal ρβ)) P) ∧
          (∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k : NonzeroLattice d,
            IntervalIntegrable (fun r =>
              centeredCommutatorForcing d s P (fun _ => withDensityReal ρβ) X
                (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ (a + t - r)
                  (fun x => Lattice.jp k.1 ^ (-m) * Torus.realMode k x)) r ω)
              volume 0 (a + t)) ∧
          ∫⁻ ω, ⨆ t ∈ {t : ℝ | t ∈ Set.Icc (0 : ℝ) T ∧ ∃ q : ℚ, (q : ℝ) = t}, ∑' k : NonzeroLattice d,
              ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d s hs0 hsd V β hβ) ρβ P X m k
                (a + t) ω ^ 2) ∂P ≤
            ENNReal.ofReal (C ^ 2 / N) := by
  classical
  obtain ⟨C₂, hC₂, hsingle⟩ := single_j_bound_proof hd hs0 hsd hcrit V hV β hβ ρβ hρβ hρS hρpos T hT.le
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  -- the exponent `2 * (-m + p + d + 3)` is `-q` with `q = 2 (m - (p + d + 3)) > d`
  have hqd : (d : ℝ) < 2 * (m - (((9 * d + 82) + d + 3 : ℕ) : ℝ)) := by
    push_cast
    linarith
  have hexp : ∀ j : NonzeroLattice d,
      Lattice.jp j.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ)))
        = Lattice.jp j.1 ^ (-(2 * (m - (((9 * d + 82) + d + 3 : ℕ) : ℝ)))) := fun j => by
    congr 1
    ring
  have hs1 : Summable fun j : NonzeroLattice d =>
      Lattice.jp j.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) :=
    (asmD_summable_rpow _ hqd).congr fun j => (hexp j).symm
  have hnn : ∀ j : NonzeroLattice d,
      0 ≤ Lattice.jp j.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) :=
    fun j => Real.rpow_nonneg (Torus.jp_pos j.1).le _
  obtain ⟨Ssum, hSsum⟩ : ∃ Ssum : ℝ, Ssum = ∑' j : NonzeroLattice d,
      Lattice.jp j.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) := ⟨_, rfl⟩
  have hSnn : 0 ≤ Ssum := by
    rw [hSsum]
    exact tsum_nonneg hnn
  refine ⟨Real.sqrt (C₂ * Ssum), Real.sqrt_nonneg _, ?_⟩
  intro N hN Ω _ P _ X₀ W X hW hind hlaw hstr hfilt a ha
  have hCsq : Real.sqrt (C₂ * Ssum) ^ 2 = C₂ * Ssum := Real.sq_sqrt (mul_nonneg hC₂ hSnn)
  have hflow0 : ∀ H : ℝ, 0 ≤ H → IsStationaryGibbsFlow P s hs0 hsd V β hβ H (X 0) W X :=
    fun H hH => flow_of_hypotheses_proof hd hs0 hsd V hV β hβ P X₀ W X hW hind hlaw hstr hfilt H hH
  have hH0 : 0 ≤ a + T := by linarith
  have hflowT : IsStationaryGibbsFlow P s hs0 hsd V β hβ (a + T) (X 0) W X := hflow0 (a + T) hH0
  refine ⟨fun f hf r hr => modulatedEnergy_integrable_proof hd hs0 hsd hcrit V hV β hβ ρβ hρβ hρS hρpos hN P
      (X 0) W X r (hflow0 r hr) f hf r hr le_rfl, ?_, ?_⟩
  · exact forcing_intervalIntegrable_proof hd hs0 hsd hcrit V hV β hβ ρβ hρβ hρS hρpos m T hT.le hN P
      (X 0) W X a ha hflowT
  · have hset : {t : ℝ | t ∈ Set.Icc (0 : ℝ) T ∧ ∃ q : ℚ, (q : ℝ) = t} = ratTimes 0 T := by
      ext t
      simp [ratTimes]
    rw [hset]
    have hA : ∀ (k : NonzeroLattice d) (b : ℝ), 0 ≤ b → b ≤ a + T →
        AEMeasurable (fun ω => integratedCenteredForcing (PDE.mfData d s hs0 hsd V β hβ) ρβ P X m k b ω) P :=
      fun k b hb hbH => integratedCenteredForcing_aemeasurable hd hs0 hsd hcrit V hV β hβ ρβ hρβ hρS hρpos m hN P
        (X 0) W X (a + T) hflowT k b hb hbH
    have hmeas : ∀ k : NonzeroLattice d, AEMeasurable (fun ω => ⨆ t ∈ ratTimes 0 T,
        ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d s hs0 hsd V β hβ) ρβ P X m k (a + t) ω ^ 2)) P := by
      intro k
      refine AEMeasurable.biSup (ratTimes 0 T) (est4_ratTimes_countable 0 T) (fun t ht => ?_)
      obtain ⟨⟨ht0, htT⟩, -⟩ := ht
      exact ((hA k (a + t) (by linarith) (by linarith)).pow_const 2).ennreal_ofReal
    have hpt : ∀ ω, (⨆ t ∈ ratTimes 0 T, ∑' k : NonzeroLattice d,
        ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d s hs0 hsd V β hβ) ρβ P X m k (a + t) ω ^ 2))
          ≤ ∑' k : NonzeroLattice d, ⨆ t ∈ ratTimes 0 T,
            ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d s hs0 hsd V β hβ) ρβ P X m k (a + t) ω ^ 2) := by
      intro ω
      refine iSup₂_le fun t ht => ?_
      exact ENNReal.tsum_le_tsum fun k => le_iSup₂ (f := fun t (_ : t ∈ ratTimes 0 T) =>
        ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d s hs0 hsd V β hβ) ρβ P X m k (a + t) ω ^ 2)) t ht
    have hcnn : ∀ k : NonzeroLattice d,
        0 ≤ C₂ * Lattice.jp k.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) / N :=
      fun k => div_nonneg (mul_nonneg hC₂ (hnn k)) (Nat.cast_nonneg N)
    have hsumc : Summable fun k : NonzeroLattice d =>
        C₂ * Lattice.jp k.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) / N :=
      (hs1.mul_left C₂).div_const (N : ℝ)
    have hfin : ENNReal.ofReal (Real.sqrt (C₂ * Ssum) ^ 2 / N) = ∑' k : NonzeroLattice d,
        ENNReal.ofReal (C₂ * Lattice.jp k.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) / N) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg hcnn hsumc, hCsq, tsum_div_const, tsum_mul_left, ← hSsum]
    rw [hfin]
    calc ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ∑' k : NonzeroLattice d,
          ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d s hs0 hsd V β hβ) ρβ P X m k (a + t) ω ^ 2) ∂P
        ≤ ∫⁻ ω, ∑' k : NonzeroLattice d, ⨆ t ∈ ratTimes 0 T,
            ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d s hs0 hsd V β hβ) ρβ P X m k (a + t) ω ^ 2) ∂P :=
          lintegral_mono fun ω => hpt ω
      _ = ∑' k : NonzeroLattice d, ∫⁻ ω, ⨆ t ∈ ratTimes 0 T,
            ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d s hs0 hsd V β hβ) ρβ P X m k (a + t) ω ^ 2) ∂P :=
          lintegral_tsum fun k => hmeas k
      _ ≤ ∑' k : NonzeroLattice d, ENNReal.ofReal
            (C₂ * Lattice.jp k.1 ^ (2 * (-m + (((9 * d + 82) + d + 3 : ℕ) : ℝ))) / N) :=
          ENNReal.tsum_le_tsum fun k => hsingle m hN P (X 0) W X a ha hflowT k

end HRS.ME
