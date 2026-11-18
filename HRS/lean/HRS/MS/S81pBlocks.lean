import HRS.MS.S81pAssemble
import HRS.MS.S81w2Burn
import HRS.MS.S81w2Spec

/-!
# S8.1 (worker S81P), item (d): `S81W2Coupling` from the block data

Namespace `HRS.Whole.S81P`, prefix `s81p_`.

`S81PBlocks` is the realization-only core of `S81W2Coupling` (no Gaussian field `Z` appears): for the one retained spectral datum at the
thermal density, constants `C, c, u0`, and every canonical realization and burn-in `u ≥ u0`, a probability space over the realization
carrying
* the four physical window processes `I` (initial), `O` (old current), `R` (recent current), `F` (forcing), with the Duhamel decomposition
  `ζ^{u+·} = I + O + R - F` as window paths,
* three jointly independent Gaussian processes `G 0, G 1, G 2` whose finite-dimensional covariance matrices `S i` are positive semidefinite
  and add up to the covariance profile `s81p_Qmat` (`Q_{αα'}(|t-t'|)`) of the stationary Gaussian field,
* `L²`-bounds `I ≈ G 0`, `O ≈ G 1`, `R ≈ G 2`, `‖F‖ ≤ εF` with total `≤ C (e^{-cu} + N^{-1/2})`.

`s81p_coupling_of_blocks : S81PBlocks → S81W2Coupling` is the (proved) reduction.  Everything that remains of `S81W2Coupling` is therefore the
construction of the block data (initial Gaussian path and decay; old current: spectral producer + return map + physical identification;
recent current: feature producer; Duhamel identity; forcing `weighted_critical_forcing`), all independent of the Gaussian field.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole HRS.Whole.S81W2

namespace HRS.Whole.S81P

/-- The block data of the burn-in coupling (see the module docstring). -/
def S81PBlocks : Prop :=
  ∀ {d : ℕ}, 2 ≤ d → ∀ (a β : ℝ), 0 < a → 0 < β → ∀ (m : ℝ), (wholeSpaceIndex d : ℝ) ≤ m →
    ∀ T : ℝ, 0 < T →
    ∃ (e : ℕ → Euc d → ℝ) (om : ℕ → ℝ),
      IsSpectralData d β (thermalDensity d ((d : ℝ) / 2) a β) e om ∧
      S81W2Coef d a β (thermalDensity d ((d : ℝ) / 2) a β) e om m ∧
      ∃ C c u0 : ℝ, 0 < c ∧ 0 ≤ u0 ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        IsCanonicalRealization d ((d : ℝ) / 2) a β N P X₀ W X →
      ∀ u : ℝ, u0 ≤ u →
        ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (Q : Measure Ω'') (_ : IsProbabilityMeasure Q)
          (π : Ω'' → Ω), MeasurePreserving π Q P ∧
        ∃ (Ip Op Rp Fp : ℝ → Ω'' → OscDual d m) (G : Fin 3 → ℝ → Ω'' → OscDual d m)
          (S : Fin 3 → ∀ (p : ℕ), (Fin p → ℝ) → (Fin p → MultiIndex d) → Matrix (Fin p) (Fin p) ℝ)
          (ε₀ ε₁ ε₂ εF : ℝ≥0∞),
          S81PProc Q T Ip ∧ S81PProc Q T Op ∧ S81PProc Q T Rp ∧ S81PProc Q T Fp ∧
          (∀ i, S81PProc Q T (G i)) ∧
          (∀ᵐ ζ ∂Q, zetaPathW m T u P X (π ζ) = processWindow m T 0 Ip ζ + processWindow m T 0 Op ζ +
            processWindow m T 0 Rp ζ - processWindow m T 0 Fp ζ) ∧
          iIndepFun (fun (i : Fin 3) (ζ : Ω'') (t : ℝ) => G i t ζ) Q ∧
          (∀ i p ts αs, (∀ c, ts c ∈ Icc (0 : ℝ) T) → (S i p ts αs).PosSemidef) ∧
          (∀ i p ts αs, (∀ c, ts c ∈ Icc (0 : ℝ) T) →
            Q.map (s81p_vec (G i) ts αs) = multivariateGaussian 0 (S i p ts αs)) ∧
          (∀ p ts αs, (∀ c, ts c ∈ Icc (0 : ℝ) T) →
            S 0 p ts αs + S 1 p ts αs + S 2 p ts αs =
              s81p_Qmat d β (thermalDensity d ((d : ℝ) / 2) a β) e om m ts αs) ∧
          s81p_L2 Q (fun ζ => processWindow m T 0 Ip ζ - processWindow m T 0 (G 0) ζ) ≤ ε₀ ∧
          s81p_L2 Q (fun ζ => processWindow m T 0 Op ζ - processWindow m T 0 (G 1) ζ) ≤ ε₁ ∧
          s81p_L2 Q (fun ζ => processWindow m T 0 Rp ζ - processWindow m T 0 (G 2) ζ) ≤ ε₂ ∧
          s81p_L2 Q (fun ζ => processWindow m T 0 Fp ζ) ≤ εF ∧
          ε₀ + ε₁ + ε₂ + εF ≤ ENNReal.ofReal (C * (Real.exp (-c * u) + (N : ℝ) ^ (-(1 / 2 : ℝ))))

/-- **Reduction**: the block data give the burn-in coupling `S81W2Coupling`. -/
theorem s81p_coupling_of_blocks (hB : S81PBlocks) : S81W2Coupling := by
  intro d hd a β ha hβ m hm T hT
  obtain ⟨e, om, hdata, hcoef, C, c, u0, hc, hu0, hblock⟩ := hB hd a β ha hβ m hm T hT
  refine ⟨C, c, u0, hc, fun ρβ hρβ N hN Ω _ P _ X₀ W X hR Ω' _ P' _ Z hZ u hu => ?_⟩
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by linarith
  have hρeq : ρβ = thermalDensity d ((d : ℝ) / 2) a β :=
    HRS.MS.Mov0.mv0_rho_eq hd hs0.le hsd ha hβ hρβ
  subst hρeq
  have hu0' : 0 ≤ u := hu0.trans hu
  obtain ⟨Ω'', _, Q, _, π, hπ, Ip, Op, Rp, Fp, G, S, ε₀, ε₁, ε₂, εF, hI, hO, hR', hF, hG, hduh, hind,
    hpsd, hlaw, hsum, b₀, b₁, b₂, bF, hε⟩ := hblock N hN P X₀ W X hR u hu
  -- measurability of the physical window
  have hAw : AEMeasurable (zetaPathW m T u P X) P := by
    have hR1 := HRS.Whole.BreakdownS81.s81b_isCanonical_shift hR u.toNNReal
    have hz : zetaPathW m T u P X = zetaPathW m T 0 P (HRS.Whole.S79.s79p_shiftX u.toNNReal X) :=
      funext fun ζ => HRS.Whole.S79.s79p_zetaPathW_shift P T X hu0' ζ
    rw [hz]
    exact s81w2_zeta_aemeas hd hN hm hT hR1
  obtain ⟨A, Gp, hA, hGp, hAlaw, hGlaw, hcost⟩ := s81p_assemble hd ha hβ hρβ hm hdata hcoef hT P Q π hπ
    (zetaPathW m T u P X) hAw Ip Op Rp Fp G hI hO hR' hF hG hduh hind S hpsd hlaw hsum ε₀ ε₁ ε₂ εF
    b₀ b₁ b₂ bF P' Z hZ
  refine ⟨Ω'', inferInstance, Q, A, Gp, inferInstance, hA, hGp, hAlaw, hGlaw, ?_⟩
  exact hcost.trans hε

end HRS.Whole.S81P
