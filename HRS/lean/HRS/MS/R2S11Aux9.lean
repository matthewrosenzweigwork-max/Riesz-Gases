import HRS.MS.R2S11Aux8

/-!
# S11.4 items (2), (3): assembly from item (1)
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2S11

open HRS.Whole HRS.MS.R2Mt
open HRS (Euc)

variable {d : ℕ}

/-- Items (2) and (3) of `r2_moving_moment_transfer` for the data `(B, rr)`. -/
def S11Items23 (d : ℕ) (s q β γ : ℝ) (ρ₀ : Euc d → ℝ) (j m : ℕ) (εstar r c₀ B rr : ℝ) : Prop :=
  ∃ C : ℝ, ∀ f0 : Euc d → ℝ, MovInitialClass ρ₀ j m εstar f0 →
    ∀ ρ : ℝ → Euc d → ℝ, MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ →
    ∀ (Ω : ℕ → Type) [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
      [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → EucConfig d N)
      (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → EucConfig d N),
      (∀ N, 2 ≤ N → MovParticleSetup (P N) d s q β N (X₀ N) (W N) (X N) ∧
        MovPrepared d s N γ (HRS.Whole.withDensityReal (ρ 0)) ((P N).map (X₀ N))) →
      (∀ h : Euc d → Euc d → ℝ, IsBoundedPairKernel s B h →
        R2ActualFBound (fun t : ℝ≥0 => HRS.Whole.withDensityReal (ρ t)) rr C h (r2MovFamily P X)) ∧
      R2ActualLinearBound (fun t : ℝ≥0 => HRS.Whole.withDensityReal (ρ t)) rr C (r2MovFamily P X) ∧
      (∀ (C₂ : ℝ) (h : Euc d → Euc d → ℝ) (hj : ℕ → Euc d → Euc d → ℝ), IsBoundedPairKernel s B h →
        IsRound2Approx s C₂ B (HRS.Whole.withDensityReal ρ₀) h hj →
        R2ActualFTail (fun t : ℝ≥0 => HRS.Whole.withDensityReal (ρ t)) rr h hj (r2MovFamily P X)) ∧
      (∀ (Θ : Type) (h : Θ → Euc d → Euc d → ℝ) (hj : Θ → ℕ → Euc d → Euc d → ℝ) (C₂ : ℝ),
        (∀ θ, IsBoundedPairKernel s B (h θ)) → IsR2UniformApprox s C₂ B (HRS.Whole.withDensityReal ρ₀) h hj →
        R2ActualFTailFam (fun t : ℝ≥0 => HRS.Whole.withDensityReal (ρ t)) rr h hj (r2MovFamily P X))

theorem s11_items23 (hd : 2 ≤ d) {s q β γ : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hq : 0 < q) (hβ : 0 < β)
    {ρ₀ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρ₀) {j m : ℕ} {εstar r c₀ c C₁ pinf K : ℝ}
    (hC₁ : 0 < C₁) (hc₀ : 0 < c₀) (hNL : MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C₁)
    (hpinf : 1 < pinf) (hAD : S11ActDens d s q β γ ρ₀ j m εstar r c₀ pinf K) (B rr : ℝ) (hrr : 1 ≤ rr) :
    S11Items23 d s q β γ ρ₀ j m εstar r c₀ B rr := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  obtain ⟨M, L, E, c₁, hM1, hc₁, hE, hfam⟩ := HRS.MS.MovEnt.s66_fam_exists hd hs0 hsd hq hβ hρ hC₁ hc₀.le hNL
  have hprob₀ : HRS.Whole.IsProbDensity ρ₀ := (HRS.MS.MovEnt.s66_rho0_facts hd hs0 hsd hq hβ hρ).1
  obtain ⟨CF, hCF0, hCF⟩ := s92_F_bound hd hs0 hs M L β pinf K B rr hβ hpinf hrr
  obtain ⟨CL, hCL0, hCL⟩ := s92_linear_bound hd hs0 hs M L β pinf K rr hβ hpinf hrr
  refine ⟨max CF CL, fun f0 hf0 ρ hρ' Ω _ P _ X₀ W X hsetup => ?_⟩
  have hfm := hfam f0 hf0 ρ hρ'
  have hR2 : ∀ t : ℝ≥0, IsRound2Density d s M L (ρ t) := fun t =>
    ⟨hfm.prob t t.2, hfm.bound t t.2, hfm.logm t t.2⟩
  have hAD' : ∀ (t : ℝ≥0) (N : ℕ), 2 ≤ N →
      HasR2ActualDensity s β pinf K (HRS.Whole.withDensityReal (ρ t)) (r2MovFamily P X t N) := fun t N hN => by
    have := hAD f0 hf0 ρ hρ' N hN (P N) (X₀ N) (W N) (X N) (hsetup N hN).1 (hsetup N hN).2 (t : ℝ) t.2
    simpa [r2MovFamily, Real.toNNReal_coe] using this
  have hρle : ∀ t : ℝ≥0, ∀ x, ρ t x ≤ C₁ * ρ₀ x := fun t x =>
    ((HRS.MS.MovEnt.s66_class_props hNL hf0 hρ' hc₀.le t t.2).2.2.1 x).2
  have hfam' : ∀ (Θ : Type) (h : Θ → Euc d → Euc d → ℝ) (hj : Θ → ℕ → Euc d → Euc d → ℝ) (C₂ : ℝ),
      (∀ θ, IsBoundedPairKernel s B (h θ)) → IsR2UniformApprox s C₂ B (HRS.Whole.withDensityReal ρ₀) h hj →
      R2ActualFTailFam (fun t : ℝ≥0 => HRS.Whole.withDensityReal (ρ t)) rr h hj (r2MovFamily P X) :=
    fun Θ h hj C₂ hh hu => s11_tail_fam_class hd hs0 hs hβ hpinf hrr hC₁.le hprob₀ hρle hR2 hAD' hh hu
  refine ⟨?_, ?_, ?_, hfam'⟩
  · intro h hh i N hN
    obtain ⟨h1, h2⟩ := hCF (ρ i) (hR2 i) h hh N hN (r2MovFamily P X i N) (hAD' i N hN)
    exact ⟨h1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)),
      h2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
  · intro i N hN a A ha hA
    have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
    exact (hCL (ρ i) (hR2 i) N hN (r2MovFamily P X i N) (hAD' i N hN) a A ha hA).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right _ _) hA0))
  · intro C₂ h hj hh ha
    have hu : IsR2UniformApprox s C₂ B (HRS.Whole.withDensityReal ρ₀) (fun _ : PUnit => h) (fun _ => hj) :=
      ⟨fun _ j => ha.finiteRank j, fun _ j x y hxy => ha.envelope j x y hxy,
        fun r hr hrs => by simpa using ha.converges r hr hrs⟩
    have := hfam' PUnit (fun _ => h) (fun _ => hj) C₂ (fun _ => hh) hu
    simpa [R2ActualFTailFam, R2ActualFTail] using this

end HRS.MS.R2S11
