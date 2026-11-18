import HRS.Appendix.B15EAux7

/-!
# Packet B15E, part 8: Stage 2 (Step 4 of B.15) with the proved inputs, and the assembly

Downstream copies of the Step-4 assemblies of `B15BAux1.lean` that use `b15b_*_proof`
(`b15b_gibbsEntropy_liminf_le_proof`, `b15b_fisherIntegrand_continuous_proof`,
`b15b_totalPotential_c1_proof`) instead of the frozen sorried statements, and the assembly of the
strong branch of Proposition B.15 (`b15e_free_main`).
-/

noncomputable section

open MeasureTheory InformationTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-- Downstream copy of `b15b_fisher_lintegral_liminf` (Step 4, Fisher lower bound). -/
theorem b15e_fisher_lintegral_liminf
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hV : Torus.IsCk 2 D.V) {T : ℝ} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hS : IsStrongSolution P D T X₀ W X)
    {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) {Y₀ : Ω → Fin N → Euc d}
    {Y : ℕ → ℝ → Ω → (Fin N → Euc d)}
    (hY : ∀ n, IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D (M n)) (liftedNoise D)
      Y₀ (fun _ => ⊤) (Y n))
    (hev : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ t : ℝ≥0, (t : ℝ) ≤ T → b15c_regProcess (Y n) t ω = X t ω)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N (selectedLaw P X r) ≤
      liminf (fun n => ∫⁻ r in Set.Icc (0 : ℝ) t, b15_fisherInfoGen D.invβ
        (b15c_potentialReg D (M n)) (selectedLaw P (b15c_regProcess (Y n)) r)) atTop := by
  have hpt : ∀ r ∈ Set.Icc (0 : ℝ) t, fisherInfo D N (selectedLaw P X r) ≤
      liminf (fun n => b15_fisherInfoGen D.invβ (b15c_potentialReg D (M n))
        (selectedLaw P (b15c_regProcess (Y n)) r)) atTop := by
    intro r hr
    refine b15b_fisherInfoGen_liminf_le D.invβ (U := totalPotential (N := N) D)
      (fun ζ hζ => b15b_fisherIntegrand_continuous_proof _ (b15b_totalPotential_c1_proof D hV) hζ)
      (fun ζ hζ => ?_)
      (fun φ hφ => b15c_marginal_tendsto hS hY hev hr.1 (hr.2.trans htT) hφ)
    obtain ⟨M₀, hM₀⟩ := b15c_fisherIntegrand_eventuallyEq D hζ
    filter_upwards [hM.eventually (eventually_ge_atTop M₀)] with n hn
    exact funext (hM₀ (M n) hn)
  calc ∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N (selectedLaw P X r)
      ≤ ∫⁻ r in Set.Icc (0 : ℝ) t, liminf (fun n => b15_fisherInfoGen D.invβ
          (b15c_potentialReg D (M n)) (selectedLaw P (b15c_regProcess (Y n)) r)) atTop :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ ≤ _ := by
        refine lintegral_liminf_le' fun n => ?_
        exact (b15e_measurable_fisherInfoGen_reg hV (M n) (T := T) (hY n)).mono_measure
          (Measure.restrict_mono (Set.Icc_subset_Icc_right htT) le_rfl)

/-- Downstream copy of `b15b_gibbsEntropy_selectedLaw_liminf_le` (Step 4, entropy at time `t`). -/
theorem b15e_gibbsEntropy_selectedLaw_liminf_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hβ : 0 < D.invβ) (hV : Torus.IsCk 2 D.V) {T : ℝ} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hS : IsStrongSolution P D T X₀ W X)
    {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n) {Y₀ : Ω → Fin N → Euc d}
    {Y : ℕ → ℝ → Ω → (Fin N → Euc d)}
    (hY : ∀ n, IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D (M n)) (liftedNoise D)
      Y₀ (fun _ => ⊤) (Y n))
    (hev : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ t : ℝ≥0, (t : ℝ) ≤ T → b15c_regProcess (Y n) t ω = X t ω)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    gibbsEntropy D (selectedLaw P X t) ≤
      liminf (fun n => b15c_gibbsEntropyGen D.invβ (b15c_potentialReg D (M n))
        (selectedLaw P (b15c_regProcess (Y n)) t)) atTop := by
  haveI : IsProbabilityMeasure (selectedLaw P X t) := b15b_selectedLaw_isProb hS.adapted t
  haveI : ∀ n, IsProbabilityMeasure (selectedLaw P (b15c_regProcess (Y n)) t) := fun n =>
    b15b_selectedLaw_isProb (fun s => b15c_regProcess_measurable (hY n) s) t
  exact b15b_gibbsEntropy_liminf_le_proof D hβ hV hM hM0
    (fun φ hφ => b15c_marginal_tendsto hS hY hev ht0 htT hφ)

/-- Downstream copy of `b15b_step4_limit` (Step 4, assembly) with the proved inputs. -/
theorem b15e_step4_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hβ : 0 < D.invβ) (hV : Torus.IsCk 2 D.V) {T : ℝ} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hS : IsStrongSolution P D T X₀ W X)
    {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n) {Y₀ : Ω → Fin N → Euc d}
    {Y : ℕ → ℝ → Ω → (Fin N → Euc d)}
    (hY : ∀ n, IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D (M n)) (liftedNoise D)
      Y₀ (fun _ => ⊤) (Y n))
    (hev : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ t : ℝ≥0, (t : ℝ) ≤ T → b15c_regProcess (Y n) t ω = X t ω)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) {K : EReal}
    (hreg : ∀ n, b15c_gibbsEntropyGen D.invβ (b15c_potentialReg D (M n))
        (selectedLaw P (b15c_regProcess (Y n)) t)
      + ((ENNReal.ofReal D.invβ * ∫⁻ r in Set.Icc (0 : ℝ) t, b15_fisherInfoGen D.invβ
          (b15c_potentialReg D (M n)) (selectedLaw P (b15c_regProcess (Y n)) r) : ℝ≥0∞) : EReal) ≤ K) :
    gibbsEntropy D (selectedLaw P X t)
      + ((ENNReal.ofReal D.invβ * ∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N (selectedLaw P X r) : ℝ≥0∞) : EReal)
      ≤ K :=
  b15e_limit_core (b15e_gibbsEntropy_selectedLaw_liminf_le hβ hV hS hM hM0 hY hev ht0 htT)
    (b15e_fisher_lintegral_liminf hV hS hM hY hev ht0 htT) hreg

end HRS
