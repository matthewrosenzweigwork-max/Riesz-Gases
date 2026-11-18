import HRS.MS.S21E_Fin
import HRS.MS.S21E_Kappa
import HRS.MS.S21E_Wick
import HRS.MS.S21E_Eps
import HRS.MS.S21E_Meas
import HRS.MS.S21E_Int
import HRS.MS.S21E_Dens
import HRS.MS.S21E_Uniq
import HRS.MS.Fp81S21CovCoreBound
import HRS.MS.S81G_Main
import HRS.MS.S104eFinal

/-!
# S2.1(iii) conditional end-to-end skeleton (wR14)

This file closes only the Lean assembly.  The named contracts below are the remaining
mathematics, not axioms or proof holes.

* O1, `fp81s21_O1_gaussian_wick`: per-start Gaussian objects on one probability space,
  projective-tensor moments uniform in the start, and exactly W0/W1/W2 plus
  `CubicFormulaIntegrable`, the inputs of `s21e_formulaFor_of_wick`.
  Sources: both audits' Gaussian/Wick findings and SOL13 §§9–10.  Fixed-time Wick
  identities in S21G2/S21L discharge only parts; moving D/J and uniform moments remain.
  Estimated size: 2k–3k lines.
* O2, `fp81s21_O2_static_initial_error`: the common trajectory-dependent sequence
  alpha_N -> 0 for the static correction at rho^0 (especially beta_0 > 0), chosen
  before N and every realization/start/test.  Source: review finding 1 and both audits'
  initial-Stein finding.  Estimated size: 3k–10k lines.
* O3, `fp81s21_O3_window_law`: a Gaussian evolution and path-law identification for
  every admissible external Z.  Source: review finding 4 and pro-audit §5.  It is needed
  to make the selected Gaussian tensor independent of the realization.
  Estimated size: included in the 2k–3k Gaussian/Wick estimate.
* O4 is the outer `fp81s21_O4_common_radius` contract.  Its radius precedes the
  trajectory; its O1/O2/O5 constants precede a0, N, realizations, and tests.  O4 is
  the required common-radius extraction for orbit, terminal, covariance, and producer
  constants.  Sources: SOL13 §§4–5 and review finding 2.  Estimated size: 150–300 lines.
  The compiled `sol13_covcore` is separately combined with this radius below.
* O5, `fp81s21_O5_recent_decomposition`: the uniform error decomposition consumed by
  `s21e_uniform_of_decomp` and `s21e_eps_of_uniform`.  Its fixed-L term contains the
  recent-window correction convergence and remote-tail weights.  Its proof must supply
  the wR13 moving duality/orbit identity, wR10 Gram, wR11 measurability, and the
  full-history (time zero to a0+T) interpolation.  This checkout has wR10/wR11 source,
  but no declarations named `fp81s21_moving_duality` or `moving_orbit_zeta`.
  Sources: both audits' moving-interpolation and weighted-tail findings.
  Estimated size: 2k–4k lines.
* O6, included in O5's quantitative estimate: the lifting inputs for recent corrections,
  namely uniform sixth path moments, uniform quadratic-field approximation tails,
  the leading W1 comparison with the needed radius order, and the centered-bias transfer
  from flucPathW to zetaPathW.  Sources: pro-audit §§6–8 and review findings 5–7.
  Estimated size: 1.5k–3k lines.

The displayed O5 interface is the weakest scalar profile consumed by the epsilon
assemblers: it bounds the actual S21eExpBound error by alpha_N + A_N^L + C exp(-cL).
The decomposition is a place to prove the analytic producers; it does not assume a
weaker expansion or change any quantifier in the frozen conclusion.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S21E

variable {p : Parameters} {δ : ℝ}

/-- The exact residual input contract for the three Wick identities consumed by G11. -/
structure fp81s21_WickInput
    {Ω : Type} [MeasurableSpace Ω] {d : ℕ} {s a β β₀ T a₀ : ℝ}
    {ρ : ℝ → Euc d → ℝ} (P : Measure Ω) [IsProbabilityMeasure P]
    (κ₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3)
    (D Z : Ω → OscPath d (wholeSpaceIndex d) T)
    (J : Ω → TensorDual (OscPath d (wholeSpaceIndex d) T) 2)
    (τ : Fin 3 → Set.Icc (0 : ℝ) T) (φ : Fin 3 → Euc d → ℝ)
    (χ : Fin 3 → ℝ → Euc d → ℝ) (hφ : ∀ i, IsOscTest (wholeSpaceIndex d) (φ i)) : Prop where
  integrable : HRS.Whole.CubicFormulaIntegrable (HRS.Whole.quadraticGradientDyn d s a β) ρ β₀
    (HRS.Whole.withDensityReal (ρ 0)) (fun i => a₀ + τ i) φ χ
  W0 : κ₀ (HRS.MC.E213U18.trilin (fun i => HRS.Whole.s21eObs (wholeSpaceIndex d : ℝ) T
      (hφ i).2 (τ i))) =
    ∫ x, HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal (ρ 0)) β₀
        (HRS.Whole.propagatorW ((HRS.Whole.quadraticGradientDyn d s a β).coeff ρ) 0 (a₀ + τ 0) (φ 0)) x *
      HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal (ρ 0)) β₀
        (HRS.Whole.propagatorW ((HRS.Whole.quadraticGradientDyn d s a β).coeff ρ) 0 (a₀ + τ 1) (φ 1)) x *
      HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal (ρ 0)) β₀
        (HRS.Whole.propagatorW ((HRS.Whole.quadraticGradientDyn d s a β).coeff ρ) 0 (a₀ + τ 2) (φ 2)) x
      ∂(HRS.Whole.withDensityReal (ρ 0))
  W1 : ∀ i : Fin 3,
    (∫ ω, HRS.Whole.s21eObs (wholeSpaceIndex d : ℝ) T (hφ i).2 (τ i) (D ω) *
        HRS.Whole.s21eObs (wholeSpaceIndex d : ℝ) T (hφ (i + 1)).2 (τ (i + 1)) (Z ω) *
        HRS.Whole.s21eObs (wholeSpaceIndex d : ℝ) T (hφ (i + 2)).2 (τ (i + 2)) (Z ω) ∂P) =
      ∫ r in Set.Icc (0 : ℝ) (a₀ + τ i), ∫ x, ∫ y,
        HRS.Whole.commutatorKernel d s (fun z => gradient (HRS.Whole.propagatorW
          ((HRS.Whole.quadraticGradientDyn d s a β).coeff ρ) r (a₀ + τ i) (φ i)) z) x y *
          χ (i + 1) r x * χ (i + 2) r y
  W2 : ∀ i : Fin 3,
    (∫ ω, HRS.Whole.s21eObs (wholeSpaceIndex d : ℝ) T (hφ (i + 2)).2 (τ (i + 2)) (Z ω) *
        J ω (HRS.MC.E213U18.mk2 (HRS.Whole.s21eObs (wholeSpaceIndex d : ℝ) T
          (hφ i).2 (τ i)) (HRS.Whole.s21eObs (wholeSpaceIndex d : ℝ) T
          (hφ (i + 1)).2 (τ (i + 1)))) ∂P) =
      (2 / β) * ∫ r in Set.Icc (0 : ℝ) (min (a₀ + τ i) (a₀ + τ (i + 1))), ∫ x,
        inner ℝ (gradient (HRS.Whole.propagatorW ((HRS.Whole.quadraticGradientDyn d s a β).coeff ρ)
          r (a₀ + τ i) (φ i)) x)
          (gradient (HRS.Whole.propagatorW ((HRS.Whole.quadraticGradientDyn d s a β).coeff ρ)
            r (a₀ + τ (i + 1)) (φ (i + 1))) x) * χ (i + 2) r x

/-- Gaussian data at one start.  The law field is O3; `wick` is O1. -/
structure fp81s21_GaussianAt
    (d : ℕ) (s a β β₀ T : ℝ) (ρ : ℝ → Euc d → ℝ) (a₀ : ℝ) where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  P : Measure Ω
  [hP : IsProbabilityMeasure P]
  process : ℝ → Ω → OscDual d (wholeSpaceIndex d)
  evolution : ∀ H : ℝ,
    HRS.Whole.IsLinearGaussianEvolutionW P ((HRS.Whole.quadraticGradientDyn d s a β).coeff ρ)
      (wholeSpaceIndex d) β⁻¹ H
      (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal (ρ 0)) β₀) process
  window : Ω → OscPath d (wholeSpaceIndex d) T
  window_eq : ∀ ω, window ω = processWindow (wholeSpaceIndex d) T a₀ process ω
  window_meas : AEMeasurable window P
  law_identification : ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
      [IsProbabilityMeasure P'] (Z : ℝ → Ω' → OscDual d (wholeSpaceIndex d)),
    (∀ H : ℝ, HRS.Whole.IsLinearGaussianEvolutionW P'
      ((HRS.Whole.quadraticGradientDyn d s a β).coeff ρ) (wholeSpaceIndex d) β⁻¹ H
      (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal (ρ 0)) β₀) Z) →
    Measure.map (processWindow (wholeSpaceIndex d) T a₀ Z) P' = Measure.map window P
  κ₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3
  κ₀_mem : κ₀ ∈ projTensor (OscPath d (wholeSpaceIndex d) T) 3
  κ₀_symm : ∀ (σ : Equiv.Perm (Fin 3))
      (M : (OscPath d (wholeSpaceIndex d) T) [×3]→L[ℝ] ℝ),
      κ₀ (M.domDomCongr σ) = κ₀ M
  D : Ω → OscPath d (wholeSpaceIndex d) T
  Zpath : Ω → OscPath d (wholeSpaceIndex d) T
  J : Ω → TensorDual (OscPath d (wholeSpaceIndex d) T) 2
  Zpath_eq : Zpath = window
  D_meas : AEStronglyMeasurable D P
  Z_meas : AEStronglyMeasurable Zpath P
  J_meas : AEStronglyMeasurable J P
  DZZ_integrable : Integrable (fun ω => ‖D ω‖ * ‖Zpath ω‖ * ‖Zpath ω‖) P
  JZ_integrable : Integrable (fun ω => ‖J ω‖ * ‖Zpath ω‖) P
  J_projective : ∀ᵐ ω ∂P, J ω ∈ projTensor (OscPath d (wholeSpaceIndex d) T) 2
  J_symmetric : ∀ᵐ ω ∂P, ∀ x y : OscPath d (wholeSpaceIndex d) T →L[ℝ] ℝ,
    J ω (HRS.MC.E213U18.mk2 x y) = J ω (HRS.MC.E213U18.mk2 y x)
  wick : ∀ (τ : Fin 3 → Set.Icc (0 : ℝ) T) (φ : Fin 3 → Euc d → ℝ)
      (χ : Fin 3 → ℝ → Euc d → ℝ),
    (hφ : ∀ i, IsOscTest (wholeSpaceIndex d) (φ i)) →
    S21eChiClause d s a β β₀ ρ T a₀ τ φ χ →
    fp81s21_WickInput (d := d) (s := s) (a := a) (β := β) (β₀ := β₀)
      (T := T) (a₀ := a₀) (ρ := ρ) P κ₀ D Zpath J τ φ χ hφ

noncomputable def fp81s21_kappaValue
    {d : ℕ} {s a β β₀ T : ℝ} {ρ : ℝ → Euc d → ℝ} {a₀ : ℝ}
    (G : fp81s21_GaussianAt d s a β β₀ T ρ a₀) :
    TensorDual (OscPath d (wholeSpaceIndex d) T) 3 := by
  letI : MeasurableSpace G.Ω := G.mΩ
  letI : IsProbabilityMeasure G.P := G.hP
  exact HRS.MS.S21E.s21eKappa G.P G.κ₀ G.D G.Zpath G.J

/-- O1: one canonical Gaussian probability space per start and uniform moments before the start. -/
structure fp81s21_O1_gaussian_wick
    (d : ℕ) (s a β β₀ T : ℝ) (ρ : ℝ → Euc d → ℝ) where
  Kb : ℝ
  data : ∀ a₀ : ℝ, 0 ≤ a₀ → fp81s21_GaussianAt d s a β β₀ T ρ a₀
  moment_bound : ∀ a₀ : ℝ, ∀ ha₀ : 0 ≤ a₀,
    ‖(data a₀ ha₀).κ₀‖ +
      3 * (∫ ω, ‖(data a₀ ha₀).D ω‖ * ‖(data a₀ ha₀).Zpath ω‖ *
        ‖(data a₀ ha₀).Zpath ω‖ ∂(data a₀ ha₀).P) +
      3 * (∫ ω, ‖(data a₀ ha₀).J ω‖ * ‖(data a₀ ha₀).Zpath ω‖ ∂(data a₀ ha₀).P) ≤ Kb

noncomputable def fp81s21_O1_kappa
    {d : ℕ} {s a β β₀ T : ℝ} {ρ : ℝ → Euc d → ℝ}
    (O1 : fp81s21_O1_gaussian_wick d s a β β₀ T ρ) :
    ℝ → projTensor (OscPath d (wholeSpaceIndex d) T) 3 := fun a₀ =>
  if ha₀ : 0 ≤ a₀ then
    let G := O1.data a₀ ha₀
    letI : MeasurableSpace G.Ω := G.mΩ
    letI : IsProbabilityMeasure G.P := G.hP
    ⟨fp81s21_kappaValue G,
      HRS.MS.S21E.s21e_kappa_mem (P := G.P) (κ₀ := G.κ₀) (D := G.D)
        (Z := G.Zpath) (J := G.J) G.κ₀_mem G.D_meas G.Z_meas G.J_meas
        G.DZZ_integrable G.JZ_integrable G.J_projective⟩
  else 0

theorem fp81s21_O1_kappa_eq
    {d : ℕ} {s a β β₀ T : ℝ} {ρ : ℝ → Euc d → ℝ}
    (O1 : fp81s21_O1_gaussian_wick d s a β β₀ T ρ)
    (a₀ : ℝ) (ha₀ : 0 ≤ a₀) :
    (fp81s21_O1_kappa O1 a₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3) =
      fp81s21_kappaValue (O1.data a₀ ha₀) := by
  simp [fp81s21_O1_kappa, ha₀]

/-- O3: the selected future Gaussian has the law of every admissible external evolution window. -/
def fp81s21_O3_window_law
    {d : ℕ} {s a β β₀ T : ℝ} {ρ : ℝ → Euc d → ℝ} {a₀ : ℝ}
    (G : fp81s21_GaussianAt d s a β β₀ T ρ a₀) : Prop := by
  letI : MeasurableSpace G.Ω := G.mΩ
  letI : IsProbabilityMeasure G.P := G.hP
  exact ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (Z : ℝ → Ω' → OscDual d (wholeSpaceIndex d)),
    (∀ H : ℝ, HRS.Whole.IsLinearGaussianEvolutionW P'
      ((HRS.Whole.quadraticGradientDyn d s a β).coeff ρ) (wholeSpaceIndex d) β⁻¹ H
      (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s)
        (HRS.Whole.withDensityReal (ρ 0)) β₀) Z) →
    Measure.map (processWindow (wholeSpaceIndex d) T a₀ Z) P' = Measure.map G.window G.P

/-- O2: the nonthermal initial Stein correction profile, uniform over all starts and consumers. -/
structure fp81s21_O2_static_initial_error
    (d : ℕ) (s a β β₀ T : ℝ) (ρ : ℝ → Euc d → ℝ) where
  alpha : ℕ → ℝ
  alpha_tendsto : Tendsto alpha atTop (𝓝 0)

/-- O5: the residual finite-N error and its fixed-L recent-window/remote-tail decomposition. -/
structure fp81s21_O5_recent_decomposition
    (d : ℕ) (s a β β₀ T : ℝ) (ρ : ℝ → Euc d → ℝ)
    (κ : ℝ → projTensor (OscPath d (wholeSpaceIndex d) T) 3)
    (O2 : fp81s21_O2_static_initial_error d s a β β₀ T ρ) where
  E : ℕ → ℝ
  C : ℝ
  c : ℝ
  c_pos : 0 < c
  E_nonneg : ∀ N, 2 ≤ N → 0 ≤ E N
  E_finite : ∀ N, 2 ≤ N → ∃ M : ℝ, E N ≤ M
  quantitative : S21eExpBound d s a β β₀ ρ T κ E
  decomposition : ∀ L : ℝ, 0 < L → ∃ A : ℕ → ℝ,
    Tendsto A atTop (𝓝 0) ∧
    ∀ N : ℕ, 2 ≤ N → E N ≤ O2.alpha N + A N + C * Real.exp (-c * L)

/-- O4: one radius before the trajectory, with the remaining constants chosen afterward but
uniformly before all window starts and particle/Gaussian consumers. -/
def fp81s21_O4_common_radius (p : Parameters) : Prop :=
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      ∃ O1 : fp81s21_O1_gaussian_wick p.d p.s p.a p.β p.γ p.T R.ρ,
      ∃ O2 : fp81s21_O2_static_initial_error p.d p.s p.a p.β p.γ p.T R.ρ,
        Nonempty (fp81s21_O5_recent_decomposition p.d p.s p.a p.β p.γ p.T R.ρ
          (fp81s21_O1_kappa O1) O2)

/-- Build the Gaussian tensor, its uniform projective norm bound, symmetry, and formula clause. -/
theorem fp81s21_gaussian_parts
    {d : ℕ} {s a β β₀ T : ℝ} {ρ : ℝ → Euc d → ℝ}
    (O1 : fp81s21_O1_gaussian_wick d s a β β₀ T ρ)
    (hcore : S21eCovCore d s a β β₀ ρ) :
      (∃ Kb : ℝ, ∀ a₀ : ℝ, 0 ≤ a₀ → ‖fp81s21_O1_kappa O1 a₀‖ ≤ Kb) ∧
      (∀ a₀ : ℝ, 0 ≤ a₀ → ∀ (σ : Equiv.Perm (Fin 3))
        (M : (OscPath d (wholeSpaceIndex d) T) [×3]→L[ℝ] ℝ),
        (fp81s21_O1_kappa O1 a₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3)
            (M.domDomCongr σ) =
          (fp81s21_O1_kappa O1 a₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3) M) ∧
      (∀ a₀ : ℝ, 0 ≤ a₀ →
        ∀ (τ : Fin 3 → Set.Icc (0 : ℝ) T) (φ : Fin 3 → Euc d → ℝ),
          (∀ i, IsOscTest (wholeSpaceIndex d) (φ i)) →
          ∃ χ : Fin 3 → ℝ → Euc d → ℝ,
            S21eChiClause d s a β β₀ ρ T a₀ τ φ χ ∧
            S21eFormulaFor d s a β β₀ ρ T a₀ (fp81s21_O1_kappa O1 a₀) τ φ χ) := by
  classical
  let κ := fp81s21_O1_kappa O1
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨O1.Kb, ?_⟩
    intro a₀ ha₀
    let G := O1.data a₀ ha₀
    letI : MeasurableSpace G.Ω := G.mΩ
    letI : IsProbabilityMeasure G.P := G.hP
    have hn := HRS.MS.S21E.s21e_kappa_norm_le
      (P := G.P) (κ₀ := G.κ₀) (D := G.D) (Z := G.Zpath) (J := G.J)
      G.D_meas G.Z_meas G.J_meas G.DZZ_integrable G.JZ_integrable
    calc
      ‖κ a₀‖ = ‖(κ a₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3)‖ := rfl
      _ = ‖fp81s21_kappaValue G‖ := congrArg norm (fp81s21_O1_kappa_eq O1 a₀ ha₀)
      _ = ‖HRS.MS.S21E.s21eKappa G.P G.κ₀ G.D G.Zpath G.J‖ := by
        simp [fp81s21_kappaValue, G]
      _ ≤ _ := le_trans hn (O1.moment_bound a₀ ha₀)
  · intro a₀ ha₀ σ M
    let G := O1.data a₀ ha₀
    letI : MeasurableSpace G.Ω := G.mΩ
    letI : IsProbabilityMeasure G.P := G.hP
    rw [fp81s21_O1_kappa_eq O1 a₀ ha₀]
    exact HRS.MS.S21E.s21e_kappa_symm G.P G.κ₀ G.D G.Zpath G.J M σ
  · intro a₀ ha₀ τ φ hφ
    obtain ⟨χ, hχ⟩ := HRS.MS.S21E.s21e_cross_exist_of_core hcore T a₀ ha₀ τ φ hφ
    let G := O1.data a₀ ha₀
    letI : MeasurableSpace G.Ω := G.mΩ
    letI : IsProbabilityMeasure G.P := G.hP
    have hw := G.wick τ φ χ hφ hχ
    have hκ : (κ a₀ : TensorDual (OscPath d (wholeSpaceIndex d) T) 3) =
        HRS.MS.S21E.s21eKappa G.P G.κ₀ G.D G.Zpath G.J := by
      simpa [fp81s21_kappaValue, G] using fp81s21_O1_kappa_eq O1 a₀ ha₀
    refine ⟨χ, hχ, ?_⟩
    exact HRS.Whole.s21e_formulaFor_of_wick (κ a₀) G.P G.κ₀ G.κ₀_symm
      G.D G.Zpath G.J G.D_meas G.Z_meas G.J_meas
      G.DZZ_integrable G.JZ_integrable G.J_symmetric hκ τ φ hφ χ hw.integrable
      hw.W0 hw.W1 hw.W2

/-- Choose the error sequence using the two compiled epsilon assemblers. -/
theorem fp81s21_error_of_profile
    {d : ℕ} {s a β β₀ T : ℝ} (hd : 2 ≤ d) (hT : 0 < T)
    {ρ : ℝ → Euc d → ℝ} {κ : ℝ → projTensor (OscPath d (wholeSpaceIndex d) T) 3}
    (O2 : fp81s21_O2_static_initial_error d s a β β₀ T ρ)
    (O5 : fp81s21_O5_recent_decomposition d s a β β₀ T ρ κ O2) :
    ∃ εN : ℕ → ℝ, Tendsto εN atTop (𝓝 0) ∧ S21eExpBound d s a β β₀ ρ T κ εN := by
  let Eunit : ℕ → Unit → ℝ := fun N _ => if 2 ≤ N then O5.E N else 0
  have hdecomp : ∀ L : ℝ, 0 < L → ∃ A : ℕ → ℝ,
      Tendsto A atTop (𝓝 0) ∧
      ∀ N : ℕ, 2 ≤ N → ∀ (_ : Unit), Eunit N () ≤ O2.alpha N + A N + O5.C * Real.exp (-O5.c * L) := by
    intro L hL
    obtain ⟨A, hA, hbound⟩ := O5.decomposition L hL
    exact ⟨A, hA, fun N hN _ => by simpa [Eunit, hN] using hbound N hN⟩
  have hlim : ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → 2 ≤ N → ∀ (_ : Unit), Eunit N () ≤ η :=
    s21e_uniform_of_decomp Eunit O5.C O5.c O5.c_pos O2.alpha O2.alpha_tendsto hdecomp
  obtain ⟨εN, hεlim, hEε⟩ := s21e_eps_of_uniform Eunit
    (fun N _ => by
      by_cases hN : 2 ≤ N
      · simpa [Eunit, hN] using O5.E_nonneg N hN
      · simp [Eunit, hN])
    (fun N hN => by
      obtain ⟨M, hM⟩ := O5.E_finite N hN
      exact ⟨M, fun _ => by simpa [Eunit, hN] using hM⟩)
    hlim
  refine ⟨εN, hεlim, ?_⟩
  intro N hN Ω _ P _ X₀ W X hBr hInd hlaw hstrong Ω' _ P' _ Z hZ a₀ ha₀ Φ hΦ
  have hrough := O5.quantitative N hN P X₀ W X hBr hInd hlaw hstrong P' Z hZ a₀ ha₀ Φ hΦ
  have hEe : O5.E N ≤ εN N := by
    simpa [Eunit, hN] using hEε N hN ()
  exact le_trans hrough hEe

/-- **Compiled end-to-end conditional skeleton** for the frozen whole-space theorem. -/
theorem fp81s21_whole_space_edgeworth_skeleton
    (hOpen : ∀ p : Parameters, fp81s21_O4_common_radius p) :
    HRS.Whole.WholeSpaceEdgeworthStatement := by
  classical
  apply HRS.Whole.whole_space_edgeworth_of_body
  intro d hd s hs0 hs a β ha hβ β₀ hβ₀ hβ₀s T hT c₁ C₁
  let p : Parameters := ⟨d, hd, s, hs0, hs, a, ha, β, hβ, β₀, hβ₀, hβ₀s, T, hT, c₁, C₁⟩
  obtain ⟨δopen, hδopen, hδopenHalf, hAt⟩ := hOpen p
  obtain ⟨δcov, hδcov, hδcovHalf, hCov⟩ := sol13_covcore p
  let δstar : ℝ := min δopen δcov
  have hδstar : 0 < δstar := lt_min hδopen hδcov
  have hδstarHalf : δstar ≤ 1 / 2 := (min_le_left _ _).trans hδopenHalf
  refine ⟨δstar, hδstar, ?_⟩
  intro ρβ hρβ ε ψ hadm ρ hρ
  let R : Trajectory p δstar := ⟨ρβ, hρβ, ε, ψ, hadm, ρ, hρ⟩
  have hOpenR := hAt δstar hδstar (by dsimp [δstar]; exact min_le_left _ _) R
  obtain ⟨O1, O2, hO5⟩ := hOpenR
  let O5 := Classical.choice hO5
  have hcovδ : δstar ≤ δcov := by dsimp [δstar]; exact min_le_right _ _
  have hcore : S21eCovCore d s a β β₀ ρ := hCov δstar hδstar hcovδ R
  let κ := fp81s21_O1_kappa O1
  obtain ⟨hbd, hsym, hform⟩ := fp81s21_gaussian_parts O1 hcore
  obtain ⟨εN, hlim, hExp⟩ := fp81s21_error_of_profile hd hT O2 O5
  have hexp : S21eExpansion d s a β β₀ ρ T κ εN :=
    s21e_expansion_of_bound hd hT hExp
  have hcross : ∀ a₀ : ℝ, 0 ≤ a₀ → S21eCrossExist d s a β β₀ ρ T a₀ := by
    intro a₀ ha₀
    exact HRS.MS.S21E.s21e_cross_exist_of_core hcore T a₀ ha₀
  exact HRS.Whole.s21e_body_of_parts κ εN hbd hsym hlim hcross hform hexp

/-- The entropy-contraction side condition of the prepared theorem is discharged unconditionally. -/
theorem fp81s21_gibbsEntropyContraction (p : Parameters) (N : ℕ) :
    HRS.Whole.GibbsEntropyContraction p.d p.s p.a p.β N :=
  HRS.MS.S81G.s81g_gibbsEntropyContraction
    (Nat.le_trans (by decide : 1 ≤ 2) p.hd) p.hs0 p.ha p.hβ

/-
Recent-window routing note: `s104e_final_whole_space_prepared` is applied at the fixed
history length `L + T`, so its window covers the full recent physical segment `[0,L+T]`.
Its W1 estimate is for `flucPathW` (eta_N).  O5 must combine the centered-bias estimate
with that bound to obtain the `zetaPathW` comparison consumed by `S21eExpBound`; the
prepared theorem's particle clause takes `GibbsEntropyContraction`, supplied by the
lemma above.  It does not by itself supply uniform sixth path moments or quadratic-field
approximation tails.
-/

#print axioms fp81s21_gaussian_parts
#print axioms fp81s21_O1_kappa_eq
#print axioms fp81s21_error_of_profile
#print axioms fp81s21_whole_space_edgeworth_skeleton
#print axioms fp81s21_gibbsEntropyContraction

end HRS.Fp81.S21

end
