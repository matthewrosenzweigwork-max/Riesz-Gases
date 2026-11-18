import HRS.Energy.G336C1Aux6
import HRS.Energy.Commutator.CommonProof

/-!
# G336C1 final: Proposition 3.36 (C1), zero temperature

`gronwall_zero_temperature_proof` and `gronwall_zero_temperature_moment_proof` (statements verbatim from
`HRS/Energy/Coercivity.lean`, with the repair `Torus.IsCk 2 D.V`).

Proof (all in `G336C1Aux1`-`Aux6`): at `invβ = 0` a.e. path is the deterministic ODE solution `Y`; the energy identity
of Prop 3.38 (`comparison_kernel_identity_proof`, on an auxiliary filtered Brownian space carrying the
deterministic path) for the truncated kernels `g_n`, `n → ∞` by dominated convergence, `micro_g ≤ 0` by `SymNonpos`,
the commutator/coercivity bound (`commutator_coercivity_common_proof`) and an integral Grönwall.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-- The pathwise bound with the constant `C/2` from the commutator/coercivity estimate. -/
theorem g336c1_ae_bound (hd : 1 ≤ d) {s : ℝ} {C₀ C : ℝ} (hC : 0 < C)
    (hcc : ∀ (Λ : ℝ), 1 ≤ Λ → ∀ (N : ℕ), 2 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
        0 ≤ rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N ∧
        (∀ (v : Torus d → Euc d) (K : ℝ), HasTransportBound d s v K →
          |commQuantity d s v X (withDensityReal ρ)| ≤
            C * K * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N)))
    (D : DynData d) (hDs : D.s = s) (hinv : D.invβ = 0) (hS : Torus.SymNonpos D.M)
    (hV : Torus.IsCk 2 D.V) (hN : 2 ≤ N) {T : ℝ} (hT : 0 ≤ T)
    {ρ : ℝ → Torus d → ℝ} {r : ℕ} {Λ : ℝ} (hr : 3 ≤ r) (hΛ : 1 ≤ Λ)
    (hmf : IsMeanFieldSolution D T ρ) (hregr : IsRegularMF r Λ T ρ)
    {Λ' : ℝ} (hΛ' : ∀ t ∈ Set.Icc 0 T, HasTransportBound d s (meanFieldDrift D (ρ t)) Λ')
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hsol : IsStrongSolution P D T X₀ W X) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc 0 T,
      correctedEnergy D C₀ Λ ρ (X (Real.toNNReal t) ω) t ≤
        Real.exp (C / 2 * T * Λ') * correctedEnergy D C₀ Λ ρ (X 0 ω) 0 := by
  subst hDs
  have hreg3 : IsRegularMF 3 Λ T ρ := fun t ht =>
    ⟨(hregr t ht).1.of_le (by exact_mod_cast hr), (KernelGrad.cbNorm_mono hr).trans (hregr t ht).2⟩
  have c : HRS.KID.MFctx D T Λ ρ := ⟨hd, hT, hV, hmf, hreg3⟩
  have hcontA := hsol.cont
  have hcolA := hsol.no_collision
  obtain ⟨Y, hY, rfl⟩ := hsol.lift
  filter_upwards [hY, hcontA, hcolA] with ω hω hcont hcol
  set Y' : ℝ≥0 → Fin N → Euc d := fun t => Y t ω with hY'
  have hp : G336C1Path D T Y' :=
    { hint := fun t htT i => (hω t htT).1 i
      hy := fun t htT i => by
        have := (hω t htT).2 i
        rw [hinv] at this
        simp only [mul_zero, Real.sqrt_zero, zero_smul, add_zero] at this
        exact this
      hcont := hcont
      hcol := fun t htT => hcol t htT }
  have hA : ∀ r ∈ Set.Icc (0 : ℝ) T,
      0 ≤ rieszEnergy d D.s (g336c1_x Y' r) (withDensityReal (ρ r)) + oNΛ d D.s C₀ Λ N ∧
      |commQuantity d D.s (meanFieldDrift D (ρ r)) (g336c1_x Y' r) (withDensityReal (ρ r))| ≤
        C * Λ' * (rieszEnergy d D.s (g336c1_x Y' r) (withDensityReal (ρ r)) + oNΛ d D.s C₀ Λ N) := by
    intro r hrT
    obtain ⟨h1, h2⟩ := hcc Λ hΛ N hN (ρ r) (hmf.density r hrT)
      (fun x => (le_abs_self _).trans (c.abs_le hrT x)) (g336c1_x Y' r) (g336c1_x_not_collision hp hrT)
    exact ⟨h1, h2 _ _ (hΛ' r hrT)⟩
  intro t ht
  have key := g336c1_det_gronwall hd D hinv hS hN hV hT hmf hreg3 hΛ' hp hC (fun r hr => (hA r hr).1)
    (fun r hr => (hA r hr).2) t ht
  have e0 : g336c1_x Y' 0 = projectPath Y 0 ω := by
    funext i; simp [g336c1_x, projectPath, hY']
  unfold correctedEnergy
  rw [e0] at key
  exact key

theorem gronwall_zero_temperature_proof (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (D : DynData d), D.s = s → D.invβ = 0 → Torus.SymNonpos D.M → Torus.IsCk 2 D.V →
      ∀ (N : ℕ), 2 ≤ N → ∀ (T : ℝ), 0 ≤ T →
      ∀ (ρ : ℝ → Torus d → ℝ) (r : ℕ) (Λ : ℝ), 3 ≤ r → 1 ≤ Λ →
        IsMeanFieldSolution D T ρ → IsRegularMF r Λ T ρ →
      ∀ Λ' : ℝ, (∀ t ∈ Set.Icc 0 T, HasTransportBound d s (meanFieldDrift D (ρ t)) Λ') →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStrongSolution P D T X₀ W X →
        ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc 0 T,
          correctedEnergy D C₀ Λ ρ (X (Real.toNNReal t) ω) t ≤
            Real.exp (C * T * Λ') * correctedEnergy D C₀ Λ ρ (X 0 ω) 0 := by
  obtain ⟨C₀, C, hC₀, hC, hcc⟩ := commutator_coercivity_common_proof hd hs0 hsd
  refine ⟨C₀, C / 2, hC₀, half_pos hC, ?_⟩
  intro D hDs hinv hS hV N hN T hT ρ r Λ hr hΛ hmf hregr Λ' hΛ' Ω _ P _ X₀ W X hsol
  exact g336c1_ae_bound hd hC (fun Λ hΛ N hN ρ hρ hρΛ X hX =>
    ⟨(hcc Λ hΛ N hN ρ hρ hρΛ X hX).1, (hcc Λ hΛ N hN ρ hρ hρΛ X hX).2.1⟩) D hDs hinv hS hV hN hT hr hΛ
    hmf hregr hΛ' P X₀ W X hsol

theorem gronwall_zero_temperature_moment_proof (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (D : DynData d), D.s = s → D.invβ = 0 → Torus.SymNonpos D.M → Torus.IsCk 2 D.V →
      ∀ (N : ℕ), 2 ≤ N → ∀ (T : ℝ), 0 ≤ T →
      ∀ (ρ : ℝ → Torus d → ℝ) (r : ℕ) (Λ : ℝ), 3 ≤ r → 1 ≤ Λ →
        IsMeanFieldSolution D T ρ → IsRegularMF r Λ T ρ →
      ∀ Λ' : ℝ, (∀ t ∈ Set.Icc 0 T, HasTransportBound d s (meanFieldDrift D (ρ t)) Λ') →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStrongSolution P D T X₀ W X →
        Integrable (fun ω => correctedEnergy D C₀ Λ ρ (X 0 ω) 0) P →
        ∀ t ∈ Set.Icc 0 T,
          ∫⁻ ω, ENNReal.ofReal (correctedEnergy D C₀ Λ ρ (X (Real.toNNReal t) ω) t) ∂P ≤
            ENNReal.ofReal (Real.exp (C * T * Λ') *
              ∫ ω, correctedEnergy D C₀ Λ ρ (X 0 ω) 0 ∂P) := by
  obtain ⟨C₀, C, hC₀, hC, hcc⟩ := commutator_coercivity_common_proof hd hs0 hsd
  refine ⟨C₀, C / 2, hC₀, half_pos hC, ?_⟩
  intro D hDs hinv hS hV N hN T hT ρ r Λ hr hΛ hmf hregr Λ' hΛ' Ω _ P _ X₀ W X hsol hint t ht
  have hcc' : ∀ (Λ : ℝ), 1 ≤ Λ → ∀ (N : ℕ), 2 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
        0 ≤ rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N ∧
        (∀ (v : Torus d → Euc d) (K : ℝ), HasTransportBound d s v K →
          |commQuantity d s v X (withDensityReal ρ)| ≤
            C * K * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N)) :=
    fun Λ hΛ N hN ρ hρ hρΛ X hX =>
      ⟨(hcc Λ hΛ N hN ρ hρ hρΛ X hX).1, (hcc Λ hΛ N hN ρ hρ hρΛ X hX).2.1⟩
  have hae := g336c1_ae_bound hd hC hcc' D hDs hinv hS hV hN hT hr hΛ hmf hregr hΛ' P X₀ W X hsol
  have hreg3 : IsRegularMF 3 Λ T ρ := fun t ht =>
    ⟨(hregr t ht).1.of_le (by exact_mod_cast hr), (KernelGrad.cbNorm_mono hr).trans (hregr t ht).2⟩
  have c : HRS.KID.MFctx D T Λ ρ := ⟨hd, hT, hV, hmf, hreg3⟩
  have h0T : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
  have hnn : ∀ᵐ ω ∂P, 0 ≤ correctedEnergy D C₀ Λ ρ (X 0 ω) 0 := by
    filter_upwards [hsol.no_collision] with ω hω
    have h1 := (hcc Λ hΛ N hN (ρ 0) (hmf.density 0 h0T)
      (fun x => (le_abs_self _).trans (c.abs_le h0T x)) (X 0 ω) (hω 0 (by simpa using hT))).1
    subst hDs
    exact h1
  set K : ℝ := Real.exp (C / 2 * T * Λ') with hK
  have hK0 : 0 ≤ K := (Real.exp_pos _).le
  calc ∫⁻ ω, ENNReal.ofReal (correctedEnergy D C₀ Λ ρ (X (Real.toNNReal t) ω) t) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (K * correctedEnergy D C₀ Λ ρ (X 0 ω) 0) ∂P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with ω hω
        exact ENNReal.ofReal_le_ofReal (hω t ht)
    _ = ENNReal.ofReal (∫ ω, K * correctedEnergy D C₀ Λ ρ (X 0 ω) 0 ∂P) := by
        rw [ofReal_integral_eq_lintegral_ofReal (hint.const_mul K)
          (hnn.mono fun ω h => mul_nonneg hK0 h)]
    _ = _ := by rw [integral_const_mul]

end HRS

example := (@HRS.gronwall_zero_temperature_proof : type_of% @HRS.gronwall_zero_temperature)
example := (@HRS.gronwall_zero_temperature_moment_proof : type_of% @HRS.gronwall_zero_temperature_moment)
