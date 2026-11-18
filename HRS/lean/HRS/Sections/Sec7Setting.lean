import HRS.Equilibrium.StaticLimits
import HRS.Dynamics.Setup
import HRS.Prob.Gaussian
import HRS.PDE.MeanField

/-!
# Section 7: the common setting of the dynamic rows (SPEC-7)

Definitions shared by the Section 7 statements (`HRS/Sections/Sec7*.lean`).  These are *not* the Appendix A
assumption bundles (drafted separately in `HRS/Main/`); they package only the standing assumptions of the
subsections `H:subsec:edgeworth` (TeX L1255-1265) and `U:sec:uniformdata` (TeX L8353-8366), and the
objects used by Propositions 7.6-7.14.

## Representation decisions
* The particle system is the project's `HRS.IsStrongSolution` of the gradient dynamics `D` (`D.M = -1`),
  `PreparedRealization` bundling: initial law `Q₀`, vector Brownian motion independent of the initial
  configuration, a strong solution on every horizon `[0,T]`, and (field `filtered`, ISSUES.md entry "Filtered strong
  solutions: follow-up repairs") the Brownian filtration to which it is adapted (`IsFilteredSolution`).
* `ζ_N^t = √N(μ_N^t - E μ_N^t)` is `HRS.zetaE` with `P = law of X_t`; paths `ζ_N^{a+·}` are the windows
  `zetaWin`, using the project's `toPath` (junk value `0` for a non-continuous path; only used for
  realisations, where continuity holds a.s. -- the statements are about laws).
* The Gaussian limit `η` is characterised through `HRS.IsLinearFluctuationSolution` (mild form with centred
  Gaussian noise part) with centred Gaussian initial law of covariance the prepared susceptibility
  `⟨P_{μ°}φ,(I+β₀K_{μ°})⁻¹P_{μ°}ψ⟩` (`H:eq:prepared-susceptibility`, TeX L816-818), `q = β⁻¹`.
* The Wick-centred quadratic Gaussian field `ℬ^t(φ) = ½ I_2^{𝒞_t}(h_{∇φ})` is represented through the real
  trigonometric basis `e_k = Torus.realMode k` of `L²_0`: `Q = ½ I_2^{𝒞}(h)` means
  `Q = L²-lim_{S ↑} ½ ∑_{k,l ∈ S} ĥ°_{kl} (η(e_k)η(e_l) - E[η(e_k)η(e_l)])`, with `ĥ°_{kl} = ∬ h°(x,y)e_k(x)e_l(y)dxdy`
  and `h° = (P_μ⊗P_μ)h` (`canonicalCenter`, "the pair kernel is centred under `μ^t`", TeX L8213).
  `h_{∇φ}` is `HRS.hTransport d s φ`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Sec7

variable {d : ℕ}

/-- Borel `σ`-algebra on `L²([0,R];E_r)` (not provided by Mathlib; used to state Wasserstein
convergence of the pair `(ζ_N, ℬ_N)`). -/
scoped instance lpMeasurableSpace {E : Type*} [NormedAddCommGroup E] {α : Type*} [MeasurableSpace α]
    (μ : Measure α) : MeasurableSpace (Lp E 2 μ) := borel _

scoped instance lpBorelSpace {E : Type*} [NormedAddCommGroup E] {α : Type*} [MeasurableSpace α]
    (μ : Measure α) : BorelSpace (Lp E 2 μ) := ⟨rfl⟩

/-- The space `L²([0,R]; E_r)`. -/
abbrev L2Path (d : ℕ) (r R : ℝ) : Type := Lp (NegSobolev d r) 2 (volume.restrict (Set.Icc (0 : ℝ) R))

open Classical in
/-- The element of `L²([0,R];E_r)` given by a path `t ↦ Y t` (`0` if `Y` is not in `L²`). -/
def toL2 (r R : ℝ) (Y : ℝ → NegSobolev d r) : L2Path d r R :=
  if h : MemLp Y 2 (volume.restrict (Set.Icc (0 : ℝ) R)) then h.toLp Y else 0

/-- `D` is the gradient dynamics (`M = -I`) of exponent `s`, potential `V`, inverse temperature `β > 0`. -/
def IsGradientData (D : DynData d) (s β : ℝ) (V : Torus d → ℝ) : Prop :=
  D.s = s ∧ D.M = -1 ∧ D.V = V ∧ D.invβ = β⁻¹

/-- A realisation of the particle system with initial law `Q₀` (TeX L170-178, L1255-1265): a strong solution
`X` on every horizon `[0,T]`, driven by independent Brownian motions `W`, independent of the initial
configuration `X₀ ∼ Q₀`.

Statement repair (ISSUES.md, entry "Filtered strong solutions: follow-up repairs"): the new field `filtered` makes `X` a filtered strong solution (`∃ ℱ W', IsFilteredSolution P ℱ W' W X`: a Brownian filtration carrying `W` to which `X` is adapted), the strong-solution adaptedness of A.1 that `IsStrongSolution` records only as measurability (ISSUES D1) and that the Itô calculus / duality identity / B.15 used by every consumer (`path_Ito`, the chaos and quench statements) needs. -/
structure PreparedRealization {N : ℕ} (D : DynData d) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Q₀ : Measure (Config d N)) (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → Config d N) : Prop where
  law_init : P.map X₀ = Q₀
  brownian : IsVectorBrownian P W
  indep : ProbabilityTheory.IndepFun X₀ (fun ω => fun t => W t ω) P
  solution : ∀ T : ℝ, IsStrongSolution P D T X₀ W X
  filtered : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X

/-- `ζ_N^t = √N(μ_N^t - E[μ_N^t])` as an element of `E_m` (`H:eq:centerings`, TeX L461-466). -/
def zetaAt {N : ℕ} (m : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → Config d N)
    (t : ℝ) (ω : Ω) : NegSobolev d m :=
  zetaE m (P.map (X t.toNNReal)) (X t.toNNReal ω)

/-- The window `ζ_N^{a+·}` as a random element of `𝒳_{m,T} = C([0,T];E_m)`. -/
def zetaWin {N : ℕ} (m T a : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → Config d N) (ω : Ω) : PathSpace d m T :=
  toPath m T (fun t ω => zetaAt m P X (a + t) ω) ω

/-- The window `η^{a+·}` (any `E_m`-valued process) as a random element of `𝒳_{m,T}`. -/
def procWin {Ω : Type} (m T a : ℝ) (η : ℝ → Ω → NegSobolev d m) (ω : Ω) : PathSpace d m T :=
  toPath m T (fun t ω => η (a + t) ω) ω

/-! ### The Gaussian limit and its Wick-centred quadratic field -/

/-- `η` is the centred Gaussian solution of the linear fluctuation equation `H:eq:linear-equation`
(TeX L489-500) with dynamics `D` (`q = D.invβ`), mean-field density `ρ`, and a centred Gaussian initial law
of covariance `⟨P_{μ₀}φ,(I+β₀K_{μ₀})⁻¹P_{μ₀}ψ⟩` (`H:eq:prepared-susceptibility`, TeX L816-818; `β₀ = 0`
gives the independent-sampling covariance `Cov_{μ₀}`), on every horizon `[0,T]`. -/
def IsGaussianLimitField (D : DynData d) (ρ : ℝ → Torus d → ℝ) (μ₀ : Measure (Torus d)) (β₀ r : ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (η : ℝ → Ω → NegSobolev d r) : Prop :=
  ∃ Y₀ : Ω → NegSobolev d r,
    IsCenteredGaussianWithCov r (P.map Y₀) (susceptibilityCov (periodicRiesz d D.s) μ₀ β₀) ∧
    ∀ T : ℝ, IsLinearFluctuationSolution P D ρ r D.invβ T Y₀ η

/-- The coefficient `ĥ°_{kl} = ∬ h°(x,y) e_k(x) e_l(y) dx dy` of the `μ`-centred pair kernel in the real
trigonometric basis (`e_k = Torus.realMode k`). -/
def wickCoeff (μ : Measure (Torus d)) (h : Torus d → Torus d → ℝ) (k l : NonzeroLattice d) : ℝ :=
  ∫ x, ∫ y, canonicalCenter μ h x y * Torus.realMode k x * Torus.realMode l y

/-- `Q = ½ I_2^{𝒞}(h°)` for the centred Gaussian field `η`: `Q` is the `L²(P)`-limit, along finite sets `S`
of nonzero frequencies, of `½ ∑_{k,l∈S} ĥ°_{kl}(η(e_k)η(e_l) - Cov(η(e_k),η(e_l)))`, where `h° = (P_μ⊗P_μ)h`
and `η(e_k)` is the `k`-th real Fourier coefficient. -/
def IsHalfWick {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {r : ℝ} (η : Ω → NegSobolev d r)
    (μ : Measure (Torus d)) (h : Torus d → Torus d → ℝ) (Q : Ω → ℝ) : Prop :=
  Tendsto (fun S : Finset (NonzeroLattice d) => ∫⁻ ω, ‖Q ω - (1 / 2) * ∑ k ∈ S, ∑ l ∈ S,
      wickCoeff μ h k l * (NegSobolev.fourierCoeff (η ω) k * NegSobolev.fourierCoeff (η ω) l -
        ∫ ω', NegSobolev.fourierCoeff (η ω') k * NegSobolev.fourierCoeff (η ω') l ∂P)‖ₑ ^ 2 ∂P)
    atTop (𝓝 0)

/-- `ℬ` is the Wick-centred quadratic field of `η` with commutator kernel `h_{∇φ}`
(`U:eq:B-limit`, `F:eq:Blimit`): for every basis test `e_k`, `ℬ(e_k) = ½ I_2^{𝒞}(h_{∇e_k})`, the pair kernel
being centred under `μ`. -/
def IsWickQuadraticField (s : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {r : ℝ}
    (η : Ω → NegSobolev d r) (μ : Measure (Torus d)) (B : Ω → NegSobolev d r) : Prop :=
  ∀ k : NonzeroLattice d,
    IsHalfWick P η μ (hTransport d s (Torus.realMode k)) fun ω => NegSobolev.eval (B ω) (Torus.realMode k)

/-! ### The standing regime of Section 7 -/

/-- The standing regime of the dynamic rows of Section 7 (TeX L1255-1265 `H:subsec:edgeworth`; L7893;
L8353-8366 `U:sec:uniformdata`): `d ≥ 2`; gradient dynamics `D` (`M = -I`) with `0 ≤ s < d/2`, fixed
`β > 0` (`D.invβ = β⁻¹`), smooth `V`; preparation `Q_{N,β₀}(μ°)` with smooth positive `μ° = ρ₀dx`,
`β₀ > 0` (`β₀ = 0` additionally permitted for `s = 0`); `ρ` the mean-field solution from `ρ₀`.
Only data selecting the classical solution is assumed: `sol` says that for every `K > d/2 + 6`, `ρ^t` (`t ≥ 0`) is the
coefficient-level solution in `C([0,∞);H^K)` of Proposition 5.1 (`O:prop:finite-reg`, TeX L5771-5791;
`HRS.PDE.IsMFSolutionHK`; unique by `HRS.PDE.finite_reg_exists_unique`).  The deterministic facts the TeX imports
from Proposition 5.1 (L8356-8357) -- uniform bounds `0 < m₀ ≤ ρ^t ≤ M₀`, uniform `C^j` bounds, the thermal density
`ρ_β`, exponential relaxation `‖ρ^t - ρ_β‖_{C^j} ≤ C_j e^{-c_j t}` (`U:eq:background-uniform`) -- are *not*
assumed; they are the lemmas `Regime.bounds`, `Regime.reg`, `Regime.thermal`, `Regime.relax` below, derived from
`HRS.PDE.finite_reg_*`.  `init` (`ρ 0 = ρ₀`) is also a consequence of `sol` (Fourier inversion for smooth `ρ₀`) and
is kept as a convenience field. -/
structure Regime (d : ℕ) where
  D : DynData d
  β : ℝ
  β₀ : ℝ
  ρ₀ : Torus d → ℝ
  ρ : ℝ → Torus d → ℝ
  hd : 2 ≤ d
  hM : D.M = -1
  hs : D.s < (d : ℝ) / 2
  hβ : 0 < β
  hDβ : D.invβ = β⁻¹
  hβ₀ : 0 < β₀ ∨ (D.s = 0 ∧ β₀ = 0)
  hV : Torus.IsSmooth D.V
  hρ₀ : SmoothPosDensity ρ₀
  init : ρ 0 = ρ₀
  sol : ∀ K : ℕ, (d : ℝ) / 2 + 6 < K → ∃ ρc : ℝ → PDE.Coeff d,
    PDE.IsMFSolutionHK d D.s D.V D.invβ (K : ℝ) ρ₀ ρc ∧ ∀ t : ℝ, 0 ≤ t → ρ t = PDE.mfPath ρc t

namespace Regime

variable (R : Regime d)

open Classical in
/-- The thermal equilibrium density `ρ_β` of the regime (exists and is unique, smooth and positive:
`HRS.PDE.thermal_exists_unique_smooth`, TeX L919-920 / Prop. 5.1 L5777). -/
def ρβ : Torus d → ℝ :=
  if h : ∃ ρ : Torus d → ℝ, IsThermalDensity (periodicRiesz d R.D.s) R.D.V R.β ρ ∧ Torus.IsSmooth ρ ∧
      (∀ x, 0 < ρ x) then h.choose else 0

/-- `ρ_β` is the smooth positive thermal density. -/
theorem thermal : IsThermalDensity (periodicRiesz d R.D.s) R.D.V R.β R.ρβ ∧ Torus.IsSmooth R.ρβ ∧
    ∀ x, 0 < R.ρβ x := by
  have h : ∃ ρ : Torus d → ℝ, IsThermalDensity (periodicRiesz d R.D.s) R.D.V R.β ρ ∧ Torus.IsSmooth ρ ∧
      (∀ x, 0 < ρ x) := by
    obtain ⟨ρ, h1, h2, h3, -⟩ := PDE.thermal_exists_unique_smooth R.hd R.D.s R.D.hs0 R.D.hsd R.β R.hβ R.D.V R.hV
    exact ⟨ρ, h1, h2, h3⟩
  unfold ρβ
  rw [dif_pos h]
  exact h.choose_spec

/-- The hypotheses of Proposition 5.1 hold for the regime at every `K > d/2 + 6` (with the degenerate temperature
interval `β₋ = β₊ = β`). -/
theorem finiteRegHyp (K : ℕ) (hK : (d : ℝ) / 2 + 6 < K) :
    PDE.FiniteRegHyp d R.D.s R.β R.β K R.D.V R.ρ₀ := by
  have hcont : Continuous R.ρ₀ := PDE.MFAux.continuous_of_isCk (ContDiff.of_le
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift R.ρ₀) from R.hρ₀.smooth)
    (by exact_mod_cast le_top))
  obtain ⟨x₀, -, hx₀⟩ := (isCompact_univ (X := Torus d)).exists_isMinOn Set.univ_nonempty
    hcont.continuousOn
  exact ⟨R.D.hs0, R.D.hsd, R.hβ, le_rfl, hK,
    PDE.ClassicalAux.isCk_of_le (by rw [← WithTop.coe_natCast]; exact WithTop.coe_le_coe.mpr le_top) R.hV,
    R.hρ₀.density, PDE.MFSemigroup.memSobolev_of_isSmooth R.hρ₀.smooth _,
    ⟨R.ρ₀ x₀, R.hρ₀.pos x₀, fun x => hx₀ (Set.mem_univ x)⟩⟩

/-- Prop. 5.1 `O:eq:finite-bounds` (L5777-5780) for the regime: `0 < m₀ ≤ ρ^t ≤ M₀` for all `t ≥ 0`
(`U:eq:background-uniform`, TeX L8360). -/
theorem bounds : ∃ m₀ M₀ : ℝ, 0 < m₀ ∧ ∀ t : ℝ, 0 ≤ t → ∀ x, m₀ ≤ R.ρ t x ∧ R.ρ t x ≤ M₀ := by
  obtain ⟨ρc, hρc, hρ⟩ := R.sol (⌊(d : ℝ) / 2 + 6⌋₊ + 1) (by
    have := Nat.lt_floor_add_one ((d : ℝ) / 2 + 6)
    push_cast; exact this)
  obtain ⟨c, C, hc, H⟩ := PDE.finite_reg_uniform_bounds (by have := R.hd; omega) R.D.s R.β R.β
    (⌊(d : ℝ) / 2 + 6⌋₊ + 1) R.D.V R.ρ₀ (R.finiteRegHyp _ (by
      have := Nat.lt_floor_add_one ((d : ℝ) / 2 + 6)
      push_cast; exact this))
  refine ⟨c, C, hc, fun t ht x => ?_⟩
  have := (H R.β ⟨le_rfl, le_rfl⟩ ρc (by rw [R.hDβ] at hρc; exact hρc) t ht).1 x
  rw [hρ t ht]; exact this

/-- Prop. 5.1 (L5771-5791, via `H^K ⊂ C^j`) for the regime: uniform `C^j` bounds of `ρ^t`, `t ≥ 0`, for every `j`
(`IsRegularMF`).  Not yet derived (Sobolev embedding of the coefficient solution into `C^j` and transfer of
`finite_reg_uniform_bounds`'s `H^K` bound); stated with `sorry`. -/
theorem reg (j : ℕ) : ∃ Λ : ℝ, ∀ T : ℝ, IsRegularMF j Λ T R.ρ := by
  sorry

/-- Prop. 5.1 `O:eq:finite-decay` (L5781-5784) in `C^j` for the regime: `‖ρ^t - ρ_β‖_{C^j} ≤ C_j e^{-c_j t}`
(`U:eq:background-uniform`, TeX L8360).  Not yet derived (from `HRS.PDE.finite_reg_decay` at `r > j + d/2` and
`cbNorm_le_sobolevNorm`); stated with `sorry`. -/
theorem relax (j : ℕ) : ∃ C c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 ≤ t →
    Torus.cbNorm j (fun x => R.ρ t x - R.ρβ x) ≤ C * Real.exp (-c * t) := by
  sorry

/-- The regime's `ρ` is a weak solution of the mean-field equation on every horizon `[0,T]`, `T > 0`
(`HRS.PDE.finite_reg_isMeanFieldSolution`). -/
theorem mf (T : ℝ) (hT : 0 < T) : IsMeanFieldSolution R.D T R.ρ := by
  have hK : (d : ℝ) / 2 + 6 < ((⌊(d : ℝ) / 2 + 6⌋₊ + 1 : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one ((d : ℝ) / 2 + 6)
    push_cast; exact this
  obtain ⟨ρc, hρc, hρ⟩ := R.sol _ hK
  have key : ∀ D : DynData d, D.M = -1 → D.invβ = R.β⁻¹ →
      D = PDE.mfData d D.s D.hs0 D.hsd D.V R.β R.hβ := by
    rintro ⟨s, M, V, iβ, h1, h2, h3⟩ h4 h5
    simp only at h4 h5
    subst h4 h5
    rfl
  have hD : R.D = PDE.mfData d R.D.s R.D.hs0 R.D.hsd R.D.V R.β R.hβ := key R.D R.hM R.hDβ
  have H := PDE.finite_reg_isMeanFieldSolution (by have := R.hd; omega) R.D.s R.β R.β _ R.D.V R.ρ₀
    (R.finiteRegHyp _ hK) R.β ⟨le_rfl, le_rfl⟩ ρc (by rw [R.hDβ] at hρc; exact hρc) T hT
  rw [hD]
  have hcongr : ∀ t ∈ Set.Icc (0 : ℝ) T, R.ρ t = PDE.mfPath ρc t := fun t ht => hρ t ht.1
  refine ⟨fun t ht => ?_, fun ψ hψ t ht => ?_⟩
  · rw [hcongr t ht]; exact H.density t ht
  · have h := H.weak ψ hψ t ht
    rw [hcongr 0 ⟨le_rfl, hT.le⟩, hcongr t ht, h]
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    rw [hcongr r ⟨hr.1, hr.2.trans ht.2⟩]

end Regime

end Sec7

end HRS

end
