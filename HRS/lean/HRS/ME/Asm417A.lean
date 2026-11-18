import HRS.ME.Defs417
import HRS.ME.Flow417
import HRS.ME.Env417
import HRS.ME.Fourier417A

/-!
# Chunk E, row 4.17: assembly packet A (proofs of A1, A3, B4)

Proofs of `forcing_eq_forcingStat` (A1), `forcingStat_envelope` (A3) and `modulatedEnergy_integrable` (B4) of
`HRS/ME/Spec417Asm.lean` (statements copied verbatim; `HRS/ME/Spec417Asm.lean` is not imported).

* A1 uses the centering identity of `forcing_eq_generator_form_proof` (`HRS/ME/Flow417.lean`) without the normal form.
* A3 is the envelope `forcing_envelope_proof` (`HRS/ME/Env417.lean`) rewritten through `forcingStat`, plus the mode
  bound `cbNorm 2 (realMode l) ≤ 3 √2 ⟨l⟩²` (`fourierTailA_mul_realMode_cbNorm`).
* B4 uses the stationarity of the one-time marginals and the envelope of A3.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.ME

variable {d : ℕ}

open HRS HRS.LZ

/-- The modulated energy of the commutator kernel is `½` times the transport quadratic statistic. -/
theorem asmA_modEnergy_eq {s : ℝ} (f : Torus d → ℝ) (ρβ : Torus d → ℝ) {N : ℕ} (X : Config d N) :
    modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad f)) X (withDensityReal ρβ) =
      (1 / 2 : ℝ) * quadStat (hTransport d s f) (withDensityReal ρβ) X := by
  have hcomm : commKernel (periodicRieszGrad d s) (Torus.grad f) = hTransport d s f := by
    funext x y
    unfold commKernel hTransport
    by_cases hxy : x = y
    · subst hxy; simp
    · rw [if_neg hxy]
  rw [hcomm]
  unfold modulatedEnergy quadStat
  ring

/-- `forcingStat f X = √N (modulatedEnergy f X - E_μ modulatedEnergy f)` (no integrability needed). -/
theorem asmA_forcingStat_eq {s : ℝ} (V : Torus d → ℝ) (β : ℝ) (ρβ : Torus d → ℝ) {N : ℕ} (f : Torus d → ℝ)
    (X : Config d N) :
    forcingStat s V β ρβ f X = Real.sqrt N * (modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad f))
      X (withDensityReal ρβ) - ∫ Y, modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad f)) Y
        (withDensityReal ρβ) ∂(canonicalGibbs (periodicRiesz d s) V N β)) := by
  have hI : ∫ Y, modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad f)) Y (withDensityReal ρβ)
      ∂(canonicalGibbs (periodicRiesz d s) V N β) =
      (1 / 2 : ℝ) * ∫ Y, quadStat (hTransport d s f) (withDensityReal ρβ) Y
        ∂(canonicalGibbs (periodicRiesz d s) V N β) := by
    simp only [asmA_modEnergy_eq]
    rw [integral_const_mul]
  simp only [forcingStat, centeredUnder]
  rw [hI, asmA_modEnergy_eq f ρβ X]
  ring

/-- A1.  The centered commutator forcing along a stationary flow is `forcingStat` of the configuration, for every
time `r ∈ [0, H]` and every `ω` (no collision-freeness is needed: the identity is between the two definitions and the
stationary marginals).  Proof: `key` in `forcing_eq_generator_form_proof` (`HRS/ME/Flow417.lean`) without the normal
form step. -/
theorem forcing_eq_forcingStat_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N) (H : ℝ)
    (hflow : IsStationaryGibbsFlow P s hs0 hsd V β hβ H X₀ W X)
    (f : Torus d → ℝ) (hf : Torus.IsSmooth f) :
    ∀ r : ℝ, 0 ≤ r → r ≤ H → ∀ ω : Ω,
      centeredCommutatorForcing d s P (fun _ => withDensityReal ρβ) X f r ω =
        forcingStat s V β ρβ f (X r.toNNReal ω) := by
  classical
  -- the strong solution on the horizon `H` (the second disjunct of `SelectedFlow` is impossible for `d ≥ 2`)
  have hsol : IsStrongSolution P (PDE.mfData d s hs0 hsd V β hβ) H X₀ W X := by
    rcases hflow.flow.flow with h | ⟨h1, -⟩
    · exact h.1
    · exact absurd h1 (by omega)
  -- stationarity of the marginals on `[0, H]`
  have hstat := HRS.MD.Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ H hN P X₀ W X hflow
  have hTm : Measurable (Function.uncurry (hTransport d s f)) :=
    HRS.Parx.PXFID.measurable_hTransport hsd f
  haveI : SFinite (withDensityReal ρβ) := by unfold withDensityReal; infer_instance
  have hQm := me_flow_quadStat_meas (N := N) (h := hTransport d s f) hTm (ν := withDensityReal ρβ)
  have hFm : Measurable (fun Y : Config d N =>
      (1 / 2 : ℝ) * quadStat (hTransport d s f) (withDensityReal ρβ) Y) :=
    measurable_const.mul hQm
  -- the expectation of the modulated energy at time `t` is its Gibbs expectation
  have hint : ∀ t : ℝ≥0, (t : ℝ) ≤ H →
      ∫ ω', modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad f)) (X t ω')
        (withDensityReal ρβ) ∂P =
        ∫ Y, modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad f)) Y
          (withDensityReal ρβ) ∂(canonicalGibbs (periodicRiesz d s) V N β) := by
    intro t ht
    simp only [asmA_modEnergy_eq]
    have e := integral_map (μ := P) (φ := X t) (hsol.adapted t).aemeasurable hFm.aestronglyMeasurable
    rw [hstat t ht] at e
    exact e.symm
  intro r hr0 hrH ω
  have ht : ((r.toNNReal : ℝ≥0) : ℝ) = r := Real.coe_toNNReal r hr0
  have htH : ((r.toNNReal : ℝ≥0) : ℝ) ≤ H := by rw [ht]; exact hrH
  dsimp only [centeredCommutatorForcing]
  rw [asmA_forcingStat_eq, hint r.toNNReal htH]

/-- A3.  Envelope.  `B` is the function of `forcing_envelope`; the mode version uses
`cbNorm 2 e_l ≤ 3 √2 ⟨l⟩²` (`fourierTailA_mul_realMode_cbNorm` with `γ = 1`, `L = 2`). -/
theorem forcingStat_envelope_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hcrit : s = d / 2)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) {N : ℕ} (hN : 2 ≤ N) :
    ∃ B : Config d N → ℝ, Measurable B ∧ (∀ X, 0 ≤ B X) ∧
      MemLp B 2 (canonicalGibbs (periodicRiesz d s) V N β) ∧
      ∃ C₀ C₁ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧
        (∀ f : Torus d → ℝ, Torus.IsSmooth f → ∀ X : Config d N, X ∉ collisionSet d N →
          |forcingStat s V β ρβ f X| ≤ Torus.cbNorm 2 f * (B X + C₀)) ∧
        (∀ (l : NonzeroLattice d) (X : Config d N), X ∉ collisionSet d N →
          |forcingStat s V β ρβ (Torus.realMode l) X| ≤ C₁ * Lattice.jp l.1 ^ 2 * (B X + C₀)) := by
  obtain ⟨B, hBm, hB0, hBL, C₀, hC₀, hbd⟩ :=
    forcing_envelope_proof hd hs0 hsd hcrit V hV β hβ ρβ hρβ hρS hρpos hN
  refine ⟨B, hBm, hB0, hBL, C₀, 3 * Real.sqrt 2, hC₀, by positivity, ?_, ?_⟩
  · intro f hf X hX
    rw [asmA_forcingStat_eq]
    exact hbd f hf X hX
  · intro l X hX
    have hcb : Torus.cbNorm 2 (Torus.realMode l) ≤ 3 * (Real.sqrt 2 * Lattice.jp l.1 ^ 2) := by
      have h := fourierTailA_mul_realMode_cbNorm 1 l 2
      rw [show (fun x => (1 : ℝ) * Torus.realMode l x) = Torus.realMode l from funext fun x => one_mul _] at h
      refine h.trans (le_of_eq ?_)
      norm_num
    have hIsm : Torus.IsSmooth (Torus.realMode l) := HRS.FieldSingAux.isSmooth_realMode l
    have hpos : 0 ≤ B X + C₀ := add_nonneg (hB0 X) hC₀
    rw [asmA_forcingStat_eq]
    refine (hbd _ hIsm X hX).trans ?_
    exact (mul_le_mul_of_nonneg_right hcb hpos).trans (le_of_eq (by ring))

/-- B4.  Conjunct 1 of `integrated_forcing`: integrability of the modulated energy along the flow (envelope A3 and
stationarity of the one-time marginals). -/
theorem modulatedEnergy_integrable_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hcrit : s = d / 2)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hρpos : ∀ x, 0 < ρβ x) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N) (H : ℝ)
    (hflow : IsStationaryGibbsFlow P s hs0 hsd V β hβ H X₀ W X)
    (f : Torus d → ℝ) (hf : Torus.IsSmooth f) (r : ℝ) (hr : 0 ≤ r) (hrH : r ≤ H) :
    Integrable (fun ω => modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad f))
      (X r.toNNReal ω) (withDensityReal ρβ)) P := by
  classical
  have hsol : IsStrongSolution P (PDE.mfData d s hs0 hsd V β hβ) H X₀ W X := by
    rcases hflow.flow.flow with h | ⟨h1, -⟩
    · exact h.1
    · exact absurd h1 (by omega)
  have hstat := HRS.MD.Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ H hN P X₀ W X hflow
  have htH : ((r.toNNReal : ℝ≥0) : ℝ) ≤ H := by rw [Real.coe_toNNReal r hr]; exact hrH
  have hmap : P.map (X r.toNNReal) = canonicalGibbs (periodicRiesz d s) V N β := hstat _ htH
  haveI : IsFiniteMeasure (canonicalGibbs (periodicRiesz d s) V N β) := by
    rw [← hmap]; infer_instance
  obtain ⟨B, hBm, hB0, hBL, C₀, hC₀, hbd⟩ :=
    forcing_envelope_proof hd hs0 hsd hcrit V hV β hβ ρβ hρβ hρS hρpos hN
  have hXm : Measurable (X r.toNNReal) := hsol.adapted _
  -- `B ∘ X_r` is integrable under `P`, since `P.map X_r` is the Gibbs measure
  have hBint : Integrable (fun ω => B (X r.toNNReal ω)) P := by
    have h1 : Integrable B (P.map (X r.toNNReal)) := by
      rw [hmap]; exact hBL.integrable one_le_two
    exact (integrable_map_measure hBm.aestronglyMeasurable hXm.aemeasurable).1 h1
  -- measurability of the modulated energy
  have hFm : Measurable (fun Y : Config d N =>
      modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad f)) Y (withDensityReal ρβ)) := by
    have hTm : Measurable (Function.uncurry (hTransport d s f)) :=
      HRS.Parx.PXFID.measurable_hTransport hsd f
    haveI : SFinite (withDensityReal ρβ) := by unfold withDensityReal; infer_instance
    have hQm := me_flow_quadStat_meas (N := N) (h := hTransport d s f) hTm (ν := withDensityReal ρβ)
    have hfun : (fun Y : Config d N =>
        modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad f)) Y (withDensityReal ρβ)) =
        fun Y => (1 / 2 : ℝ) * quadStat (hTransport d s f) (withDensityReal ρβ) Y :=
      funext fun Y => asmA_modEnergy_eq f ρβ Y
    rw [hfun]
    exact measurable_const.mul hQm
  -- the centered energy is dominated by the envelope, almost surely
  have hdom : ∀ᵐ ω ∂P, ‖modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad f))
      (X r.toNNReal ω) (withDensityReal ρβ) -
      ∫ Y, modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad f)) Y (withDensityReal ρβ)
        ∂(canonicalGibbs (periodicRiesz d s) V N β)‖ ≤
      Torus.cbNorm 2 f * (B (X r.toNNReal ω) + C₀) := by
    filter_upwards [hsol.no_collision] with ω hω
    have hX : X r.toNNReal ω ∉ collisionSet d N := hω _ htH
    have h := hbd f hf (X r.toNNReal ω) hX
    have h1 : (1 : ℝ) ≤ Real.sqrt N := Real.one_le_sqrt.mpr (by exact_mod_cast (by omega : 1 ≤ N))
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at h
    rw [Real.norm_eq_abs]
    exact (le_mul_of_one_le_left (abs_nonneg _) h1).trans h
  have hg : Integrable (fun ω => Torus.cbNorm 2 f * (B (X r.toNNReal ω) + C₀)) P :=
    (hBint.add (integrable_const C₀)).const_mul _
  have hG : Integrable (fun ω => modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad f))
      (X r.toNNReal ω) (withDensityReal ρβ) -
      ∫ Y, modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad f)) Y (withDensityReal ρβ)
        ∂(canonicalGibbs (periodicRiesz d s) V N β)) P := by
    refine Integrable.mono' hg ?_ hdom
    exact ((hFm.comp hXm).sub measurable_const).aestronglyMeasurable
  have hfin := hG.add (integrable_const
    (∫ Y, modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad f)) Y (withDensityReal ρβ)
      ∂(canonicalGibbs (periodicRiesz d s) V N β)))
  exact hfin.congr (Filter.Eventually.of_forall fun ω => by simp)

end HRS.ME

end
