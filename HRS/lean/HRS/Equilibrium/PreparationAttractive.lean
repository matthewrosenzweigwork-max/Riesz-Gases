import HRS.Equilibrium.PreparationAux
import DGRHS.Attractive.SourceUniform
import DGRHS.CLT.SourceRawEnergy

/-!
# The attractive side of Proposition 4.25 (`M:O:prop:log-prep`)

For the periodic logarithm and a bounded density there is `a > 0` with
`sup_{N ≥ 2} sup_{-a ≤ γ ≤ 0} K_{N,γ}(μ) < ∞` (source lines 5588-5593 for `γ ≤ 0`).  The
proof in the manuscript (lines 5605-5610) cites Delgadino-Gvalani-Rosenzweig, Theorem 2.6 and
Remark 2.1, together with the exponential-row estimate `periodic_log_row` (Lemma 4.24).

The cited theorem is available, in the abstract form needed here (any symmetric measurable
kernel with factorial row moments for the centred kernel), as
`DGRHS.Attractive.source_uniform_partition` in the vendored modules of `external/dgrhs`
(`external/dgrhs/PROVENANCE.md`).  This file only translates between the two conventions:
`W(x, y) = -g(x - y)`, the centred kernel of `DGRHS` is minus the centred kernel `g_μ` of
`HRS.centeredKernel`, and `K_{N,γ}` with `γ = -β ≤ 0` is the partition function
`∫ exp(-β N F_N^W)`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace PreparationAttractive

variable {d : ℕ}

/-- Kernel of `DGRHS` for the attractive logarithm: `W(x, y) = -g(x - y)`. -/
def Wk (g : Torus d → ℝ) (x y : Torus d) : ℝ := -g (x - y)

variable {g : Torus d → ℝ} {μ : Measure (Torus d)}

theorem Wk_symm (hg : ∀ z, g (-z) = g z) (x y : Torus d) : Wk g x y = Wk g y x := by
  unfold Wk
  rw [← hg (x - y), neg_sub]

theorem potential_eq (x : Torus d) : DGRHS.potential μ (Wk g) x = -convMeasure g μ x := by
  unfold DGRHS.potential Wk convMeasure
  rw [integral_neg]

theorem secondPotential_eq (hg : ∀ z, g (-z) = g z) (y : Torus d) :
    DGRHS.secondPotential μ (Wk g) y = -convMeasure g μ y := by
  unfold DGRHS.secondPotential Wk convMeasure
  rw [integral_neg]
  congr 2
  funext x
  rw [← hg (x - y), neg_sub]

theorem pairIntegral_eq [IsProbabilityMeasure μ]
    (hI : Integrable (fun p : Torus d × Torus d => g (p.1 - p.2)) (μ.prod μ)) :
    ∫ z, Wk g z.1 z.2 ∂μ.prod μ = -energyPairing g μ μ := by
  unfold Wk energyPairing
  rw [integral_neg, integral_prod _ hI]

theorem interactionEnergy_eq [IsProbabilityMeasure μ]
    (hI : Integrable (fun p : Torus d × Torus d => g (p.1 - p.2)) (μ.prod μ)) :
    DGRHS.interactionEnergy μ (Wk g) = -(1 / 2) * energyPairing g μ μ := by
  unfold DGRHS.interactionEnergy
  rw [pairIntegral_eq hI]
  ring

/-- The centred kernel of `DGRHS` for `W = -g(x - y)` is minus `HRS.centeredKernel`. -/
theorem centeredKernel_eq [IsProbabilityMeasure μ] (hg : ∀ z, g (-z) = g z)
    (hI : Integrable (fun p : Torus d × Torus d => g (p.1 - p.2)) (μ.prod μ)) (x y : Torus d) :
    DGRHS.centeredKernel μ (Wk g) x y = -centeredKernel g μ x y := by
  unfold DGRHS.centeredKernel HRS.centeredKernel
  rw [potential_eq, secondPotential_eq hg, pairIntegral_eq hI]
  unfold Wk
  ring

theorem offDiagonalSum_eq {N : ℕ} (h : Torus d → Torus d → ℝ) (X : Config d N) :
    DGRHS.CanonicalVariance.offDiagonalSum (Function.uncurry h) X =
      ∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j) := by
  classical
  unfold DGRHS.CanonicalVariance.offDiagonalSum
  have hoff : (Finset.univ : Finset (Fin N)).offDiag =
      (Finset.univ ×ˢ Finset.univ).filter (fun p : Fin N × Fin N => p.1 ≠ p.2) := by
    ext p; simp [Finset.mem_offDiag]
  rw [hoff, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.uncurry]
  rw [← Finset.sum_filter, Finset.filter_ne]

/-- `K_{N,γ}` for `γ = -β` is the `DGRHS` partition function with the kernel `W = -g(x - y)`:
`F_N^g = -F_N^W`. -/
theorem modulatedEnergyKernel_eq [IsProbabilityMeasure μ] (hg : ∀ z, g (-z) = g z)
    (hI : Integrable (fun p : Torus d × Torus d => g (p.1 - p.2)) (μ.prod μ))
    {N : ℕ} (hN : 0 < N) (X : Config d N) :
    modulatedEnergyKernel g X μ =
      -DGRHS.CLT.sourceCanonicalModulatedEnergy
        (fun p => DGRHS.centeredKernel μ (Wk g) p.1 p.2)
        (DGRHS.potential μ (Wk g)) (DGRHS.interactionEnergy μ (Wk g)) N X := by
  rw [DGRHS.CLT.sourceCanonicalModulatedEnergy_raw μ (Wk g) (Wk_symm hg) N hN X]
  have hoff : DGRHS.CanonicalVariance.offDiagonalSum (Function.uncurry (Wk g)) X =
      -∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j) := by
    rw [offDiagonalSum_eq]
    simp only [Wk, Finset.sum_neg_distrib]
  rw [hoff]
  rw [interactionEnergy_eq hI]
  simp only [potential_eq, Finset.sum_neg_distrib]
  unfold modulatedEnergyKernel modulatedEnergy
  change _ = _
  simp only [convMeasure, energyPairing] at *
  ring

/-- Row factorial moments of the `DGRHS` centred kernel, from the exponential row estimate
`periodic_log_row` (Lemma 4.24) with exponent `a = 1`. -/
theorem rowFactorialMoments (hd : 2 ≤ d) (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ) (Λ : ℝ)
    (hΛ : ∀ x, ρ x ≤ Λ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p : ℕ, 1 ≤ p → ∀ y,
      (∫⁻ x, ENNReal.ofReal
        (|DGRHS.centeredKernel (withDensityReal ρ) (Wk (periodicRiesz d 0)) x y| ^ p)
          ∂(withDensityReal ρ)) ≤ ENNReal.ofReal (C ^ p * (p.factorial : ℝ)) := by
  have hs0 : (0 : ℝ) ≤ 0 := le_rfl
  have hsd : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hg : Measurable (periodicRiesz d 0) := PoleCavityAux.measurable_periodicRiesz hd hs0 hsd
  have hgi : Integrable (periodicRiesz d 0) := KernelAux.integrable_periodicRiesz hd hs0 hsd
  haveI := isProb_withDensityReal hρ
  have hI := PreparationAux.integrable_pair_withDensity hg hgi ρ Λ hΛ (ν := withDensityReal ρ) rfl
  have hev : ∀ z, periodicRiesz d 0 (-z) = periodicRiesz d 0 z := fun z => periodicRiesz_neg z
  obtain ⟨Cexp, hCexp⟩ := periodic_log_row hd ρ hρ Λ hΛ 1 one_pos (by exact_mod_cast (by omega : 1 < d))
  refine ⟨max 1 Cexp, le_max_left _ _, fun p hp y => ?_⟩
  have hsymm : ∀ x, centeredKernel (periodicRiesz d 0) (withDensityReal ρ) x y =
      centeredKernel (periodicRiesz d 0) (withDensityReal ρ) y x := by
    intro x
    unfold centeredKernel
    rw [← hev (x - y), neg_sub]
    ring
  have h1 : ∀ x, ENNReal.ofReal
      (|DGRHS.centeredKernel (withDensityReal ρ) (Wk (periodicRiesz d 0)) x y| ^ p) ≤
      ENNReal.ofReal ((p.factorial : ℝ) *
        Real.exp (1 * |centeredKernel (periodicRiesz d 0) (withDensityReal ρ) y x|)) := by
    intro x
    apply ENNReal.ofReal_le_ofReal
    rw [centeredKernel_eq hev hI, abs_neg, hsymm x]
    have := Real.pow_div_factorial_le_exp
      |centeredKernel (periodicRiesz d 0) (withDensityReal ρ) y x| (abs_nonneg _) p
    have hf : (0 : ℝ) < p.factorial := by exact_mod_cast Nat.factorial_pos p
    rw [div_le_iff₀ hf] at this
    rw [one_mul]
    linarith
  calc _ ≤ ∫⁻ x, ENNReal.ofReal ((p.factorial : ℝ) *
        Real.exp (1 * |centeredKernel (periodicRiesz d 0) (withDensityReal ρ) y x|))
        ∂(withDensityReal ρ) := lintegral_mono h1
    _ = ENNReal.ofReal (p.factorial : ℝ) * ∫⁻ x, ENNReal.ofReal
        (Real.exp (1 * |centeredKernel (periodicRiesz d 0) (withDensityReal ρ) y x|))
        ∂(withDensityReal ρ) := by
        rw [← lintegral_const_mul']
        · congr 1; funext x; rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        · exact ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (p.factorial : ℝ) * ENNReal.ofReal Cexp := by
        gcongr
        exact hCexp y
    _ = ENNReal.ofReal ((p.factorial : ℝ) * Cexp) := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ ENNReal.ofReal ((max 1 Cexp) ^ p * (p.factorial : ℝ)) := by
        apply ENNReal.ofReal_le_ofReal
        have hC1 : max 1 Cexp ≤ (max 1 Cexp) ^ p := by
          calc max 1 Cexp = (max 1 Cexp) ^ 1 := (pow_one _).symm
            _ ≤ (max 1 Cexp) ^ p := pow_le_pow_right₀ (le_max_left _ _) hp
        have := le_max_right 1 Cexp
        have hf : (0 : ℝ) ≤ p.factorial := Nat.cast_nonneg _
        nlinarith

end PreparationAttractive

variable {d : ℕ}

open PreparationAttractive in
/-- The attractive half of Proposition 4.25 (`O:eq:small-negative`, `γ ≤ 0`): for the periodic
logarithm and a bounded probability density there are `a > 0` and `C` with
`K_{N,γ}(μ) ≤ C` for all `N ≥ 2` and `-a ≤ γ ≤ 0`.  Proof: the cited
Delgadino-Gvalani-Rosenzweig Theorem 2.6 / Remark 2.1 in the form
`DGRHS.Attractive.source_uniform_partition`, whose factorial row hypothesis follows from
Lemma 4.24 (`periodic_log_row`); the potential is bounded by `convMeasure_bounded`. -/
theorem log_prep_attractive (hd : 2 ≤ d) (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ) (Λ : ℝ)
    (hΛ : ∀ x, ρ x ≤ Λ) :
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ γ ∈ Set.Icc (-a) 0,
      PreparationAux.KE (periodicRiesz d 0) N γ (withDensityReal ρ) ≤ ENNReal.ofReal C := by
  have hs0 : (0 : ℝ) ≤ 0 := le_rfl
  have hsd : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  set g := periodicRiesz d 0 with hgdef
  set μ := withDensityReal ρ with hμ
  have hg : Measurable g := PoleCavityAux.measurable_periodicRiesz hd hs0 hsd
  have hgi : Integrable g := KernelAux.integrable_periodicRiesz hd hs0 hsd
  haveI : IsProbabilityMeasure μ := isProb_withDensityReal hρ
  have hI : Integrable (fun p : Torus d × Torus d => g (p.1 - p.2)) (μ.prod μ) :=
    PreparationAux.integrable_pair_withDensity hg hgi ρ Λ hΛ (ν := μ) rfl
  have hev : ∀ z, g (-z) = g z := fun z => periodicRiesz_neg z
  obtain ⟨C₁, hC₁, hrow⟩ := rowFactorialMoments hd ρ hρ Λ hΛ
  obtain ⟨Cu₀, hCu₀⟩ := convMeasure_bounded (s := 0) hd hs0 hsd ρ hρ Λ hΛ
  set Cu := max Cu₀ 0 with hCu
  have hCu0 : 0 ≤ Cu := le_max_right _ _
  have hpot : ∀ x, |DGRHS.potential μ (Wk g) x| ≤ Cu := fun x => by
    rw [potential_eq, abs_neg]; exact (hCu₀ x).trans (le_max_left _ _)
  set κ := DGRHS.Attractive.attractiveMomentConstant with hκ
  have hκpos : 0 < κ := DGRHS.Attractive.attractiveMomentConstant_pos
  have hC₁pos : 0 < C₁ := by linarith
  set a := 1 / (2 * (κ * C₁)) with ha
  have hapos : 0 < a := by positivity
  set IE := DGRHS.interactionEnergy μ (Wk g) with hIE
  refine ⟨a, hapos, Real.exp (a * |IE|) * 2 * Real.exp (a * Cu), fun N hN γ hγ => ?_⟩
  set β := -γ with hβdef
  have hβ0 : 0 ≤ β := by have := hγ.2; linarith
  have hβa : β ≤ a := by have := hγ.1; linarith
  have hsmall' : β * (κ * C₁) ≤ 1 / 2 := by
    calc β * (κ * C₁) ≤ a * (κ * C₁) := by gcongr
      _ = 1 / 2 := by rw [ha]; field_simp
  have hsmall : β * (κ * C₁) < 1 := by linarith
  have hWm : StronglyMeasurable (Function.uncurry (Wk g)) :=
    (hg.comp (measurable_fst.sub measurable_snd)).neg.stronglyMeasurable
  have hWi : Integrable (Function.uncurry (Wk g)) (μ.prod μ) := hI.neg
  have hpotm : Measurable (DGRHS.potential μ (Wk g)) := by
    have : DGRHS.potential μ (Wk g) = fun x => -convMeasure g μ x := funext potential_eq
    rw [this]; exact (PoleCavityAux.measurable_convMeasure hg μ).neg
  have htail : Integrable (fun x => Real.exp (2 * β * DGRHS.potential μ (Wk g) x)) μ := by
    refine Integrable.of_bound (C := Real.exp (2 * β * Cu))
      (hpotm.const_mul (2 * β) |>.exp).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.2
    have := (abs_le.1 (hpot x)).2
    nlinarith
  have hN0 : 0 < N := by omega
  obtain ⟨hint, hbd⟩ := DGRHS.Attractive.source_uniform_partition (μ := μ) (Wk g) hWm hWi
    (Wk_symm hev) C₁ β (by
      refine DGRHS.Attractive.rowFactorialMoments_of_lintegral μ _
        (DGRHS.Gaussian.stronglyMeasurable_hoeffdingCentered μ (Function.uncurry (Wk g))
          hWm).measurable C₁ (by linarith) hrow)
    hβ0 hsmall htail N hN0
  have hKE : PreparationAux.KE g N γ μ = ENNReal.ofReal
      (∫ x : Fin N → Torus d, Real.exp (-β * (N : ℝ) *
        DGRHS.CLT.sourceCanonicalModulatedEnergy
          (fun p => DGRHS.centeredKernel μ (Wk g) p.1 p.2)
          (DGRHS.potential μ (Wk g)) (DGRHS.interactionEnergy μ (Wk g)) N x)
        ∂Measure.pi (fun _ : Fin N => μ)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
    unfold PreparationAux.KE
    refine lintegral_congr fun X => ?_
    congr 2
    rw [modulatedEnergyKernel_eq hev hI hN0 X]
    simp only [hβdef]
    ring
  rw [hKE]
  apply ENNReal.ofReal_le_ofReal
  refine hbd.trans ?_
  have h1 : Real.exp (β * |IE|) ≤ Real.exp (a * |IE|) :=
    Real.exp_le_exp.2 (by gcongr)
  have h2 : Real.sqrt (2 / (1 - (β * (κ * C₁)) ^ 2)) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    have hp : 0 ≤ β * (κ * C₁) := by positivity
    have : (β * (κ * C₁)) ^ 2 ≤ 1 / 4 := by nlinarith
    rw [div_le_iff₀ (by nlinarith)]
    nlinarith
  have h3 : Real.sqrt (∫ x, Real.exp (2 * β * DGRHS.potential μ (Wk g) x) ∂μ) ≤
      Real.exp (a * Cu) := by
    rw [Real.sqrt_le_left (Real.exp_pos _).le]
    have hle : ∫ x, Real.exp (2 * β * DGRHS.potential μ (Wk g) x) ∂μ ≤
        Real.exp (2 * β * Cu) := by
      have := norm_integral_le_of_norm_le_const (μ := μ)
        (f := fun x => Real.exp (2 * β * DGRHS.potential μ (Wk g) x))
        (C := Real.exp (2 * β * Cu)) (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          apply Real.exp_le_exp.2
          have := (abs_le.1 (hpot x)).2
          nlinarith)
      simpa using (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)
    refine hle.trans ?_
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    push_cast
    nlinarith
  have hpos1 : 0 ≤ Real.sqrt (2 / (1 - (β * (κ * C₁)) ^ 2)) := Real.sqrt_nonneg _
  have hpos2 : 0 ≤ Real.sqrt (∫ x, Real.exp (2 * β * DGRHS.potential μ (Wk g) x) ∂μ) :=
    Real.sqrt_nonneg _
  calc _ ≤ Real.exp (a * |IE|) * 2 * Real.exp (a * Cu) := by gcongr

end HRS
