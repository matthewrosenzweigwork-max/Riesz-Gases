import HRS.Sections.Sec5
import HRS.Stochastic.DualityProof
import HRS.Stochastic.QuadraticVariation
import HRS.Sections.Q40bAux1
import HRS.Sections.Q40bAux2
import HRS.Sections.Q40bAux3
import HRS.Sections.Q40bAux4
import HRS.Sections.Q40bAux5
import HRS.Sections.Q40bAux6
import HRS.Sections.Q40bAux7
import HRS.Sections.Q40bAux8

/-!
# Packet Q40b, part 9: the centered identity from the trajectory data

* `q40b_ito_stop`: an Itô integral with integrand vanishing after `t` is constant after `t`;
* `q40b_ae_identity`: `⟨φ, ζ_N^t⟩ = ⟨U^{0,t}φ, ζ_N^∘⟩ + √N M_N(t,φ) - 𝓡_N(t,φ)` a.s., for every `t ≥ 0`,
  assembling the PDE inputs (part 2), the `L¹` bound (part 7) and `q40b_centered_identity` (part 6).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section
namespace HRS.Q40b

variable {d N : ℕ}

section Stop

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {ι : Type*} [Fintype ι] {W : ℝ≥0 → Ω → ι → ℝ}

/-- An Itô integral whose integrand vanishes after `t` is constant after `t`. -/
theorem q40b_ito_stop (hW : IsBrownianFiltration P ℱ W) {Φ : ℝ → Ω → ι → ℝ}
    (hΦ : IsProgressiveL2 P ℱ Φ) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T)
    (hzero : ∀ s ω k, t < s → Φ s ω k = 0) :
    ∀ᵐ ω ∂P, itoIntegral P ℱ W Φ T ω = itoIntegral P ℱ W Φ t ω := by
  have hiso := integral_itoIntegral_sub_sq hW hΦ ht htT
  have hzero' : ∫ ω, (∫ r in Set.Ioc t T, ∑ k, Φ r ω k ^ 2) ∂P = 0 := by
    have : ∀ ω, ∫ r in Set.Ioc t T, ∑ k, Φ r ω k ^ 2 = 0 := by
      intro ω
      refine setIntegral_eq_zero_of_forall_eq_zero fun r hr => ?_
      simp [hzero r ω _ hr.1]
    simp [this]
  rw [hzero'] at hiso
  have hint : Integrable (fun ω => (itoIntegral P ℱ W Φ T ω - itoIntegral P ℱ W Φ t ω) ^ 2) P :=
    ((memLp_two_itoIntegral hW hΦ T).sub (memLp_two_itoIntegral hW hΦ t)).integrable_sq
  have h0 := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hint).1 hiso
  filter_upwards [h0] with ω hω
  have : (itoIntegral P ℱ W Φ T ω - itoIntegral P ℱ W Φ t ω) ^ 2 = 0 := hω
  have := pow_eq_zero_iff (two_ne_zero) |>.1 this
  linarith

end Stop


section AeIdentity

variable {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

theorem q40b_ae_identity (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    (hN : 2 ≤ N) [NeZero N] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hsol : ∀ T : ℝ, 0 ≤ T → IsStrongSolution P htr.dyn T X₀ W X)
    (hfilt : IsFilteredSolution P ℱ W' W X) {H₁ : ℝ}
    {t : ℝ} (ht : 0 ≤ t) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {F : ℝ → Torus d → ℝ}
    (hF : IsClassicalAdjointSolution htr.dyn ρ t φ F)
    (hFp : ∀ r ∈ Set.Icc 0 t, propagator htr.dyn ρ r t φ = F r)
    (hentQ : ∀ r ∈ Set.Icc (0 : ℝ) t, relEntropy (P.map (X r.toNNReal))
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ r))) ≤ ENNReal.ofReal H₁) :
    ∀ᵐ ω ∂P, zetaStat P X t φ ω = zetaStat P X 0 (propagator htr.dyn ρ 0 t φ) ω +
      Real.sqrt N * itoIntegral P ℱ W' (empiricalNoiseIntegrand htr.dyn t F X) t ω -
      integratedRemainder htr.dyn ρ P X t φ ω := by
  have hd1 : 1 ≤ d := by omega
  have hN0 : 0 < N := by omega
  have hφ2 : Torus.IsCk 2 φ := PDE.ClassicalAux.isCk_of_le (WithTop.coe_le_coe.2 le_top) hφ
  rcases ht.eq_or_lt with h0 | hpos
  · -- `t = 0`
    subst h0
    have hψ : propagator htr.dyn ρ 0 0 φ = φ := by
      rw [hFp 0 ⟨le_rfl, le_rfl⟩]; exact hF.terminal
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [hψ, itoIntegral_of_nonpos P ℱ W' _ (le_refl (0 : ℝ))]
    unfold integratedRemainder
    simp
  · -- `t > 0`
    obtain ⟨c₀, hc₀, Λ, hΛ⟩ := q40b_rho_bounds hd1 htr
    obtain ⟨Λ3, hreg⟩ := q40b_regular hd1 htr t
    have hB : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, ρ r x ≤ Λ 0 := by
      intro r hr x
      have h0 : Torus.IsCk 0 (ρ r) := PDE.ClassicalAux.isCk_of_le (WithTop.coe_le_coe.2 zero_le) (hΛ r hr.1).2.1
      exact (le_abs_self _).trans ((Cor516Aux.abs_le_cbNorm' h0 x).trans ((hΛ r hr.1).2.2.2 0))
    have hXm : ∀ r : ℝ≥0, Measurable (X r) := fun r => hfilt.adapted r |>.mono (ℱ.le _) le_rfl
    obtain ⟨K, hK, hL1⟩ := q40b_hL1 hd htr ht hF hN hXm hfilt.progressive hentQ
    have hid := q40b_centered_identity (N := N) hd1 (D := htr.dyn) rfl
      (PDE.ClassicalAux.isCk_of_le (WithTop.coe_le_coe.2 le_top) htr.V_smooth) hpos (ρ := ρ) (Λ := Λ3) (B := Λ 0)
      (q40b_meanField hd1 htr hpos) hreg (q40b_jointCont hd1 htr t) hB hφ2 hF hFp hN
      (hsol t ht) hfilt hK hL1
    have hΨeq : empiricalNoiseIntegrand htr.dyn t (fun r => propagator htr.dyn ρ r t φ) X =
        empiricalNoiseIntegrand htr.dyn t F X := by
      funext s' ω k
      unfold empiricalNoiseIntegrand
      by_cases hs : s' ∈ Set.Icc 0 t
      · simp only [hs, if_true]; rw [hFp s' hs]
      · simp [hs]
    have hMeq : empiricalMartingale P ℱ W' htr.dyn t (fun r => propagator htr.dyn ρ r t φ) X =
        itoIntegral P ℱ W' (empiricalNoiseIntegrand htr.dyn t F X) := by
      unfold empiricalMartingale; rw [hΨeq]
    rw [hMeq, Real.coe_toNNReal _ ht] at hid
    exact hid

end AeIdentity

end HRS.Q40b
