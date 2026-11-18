import HRS.Main.Headline
import HRS.Equilibrium.StaticLimits
import HRS.Main.HaarAux1

/-!
# Section 2 of the main manuscript: equilibrium rates, sharpness and the covariance obstruction
(headline results and prose claims, part 2)

Specification file SPEC-2 (statements with `sorry` proofs; definitions contain no `sorry`).
Source: `HRS_periodic_main_20261008T010000Z.tex` ("M"), Section 2, lines 994-1241.

Rows covered: `M:prose:L994-1034`, `M:H:prop:critical` (2.10), `M:prose:L1104-1148`,
`M:H:prop:covariance-obstruction` (2.11), `M:prose:L1198-1218` (with `deltaN_two_thirds` of
`HRS/Main/Headline.lean`), `M:@remark:L1219`.

## Representation decisions

* The rate family `φ = cos(2πk·x)`, `V_θ = -θφ/β` (`H:eq:rate-family`) and its variables
  `Y_{N,θ} = √N(μ_N(φ) - m_{N,θ}(φ))`, `G_θ = Z_{β,θ}^0(φ) ∼ N(0, C_{β,μ_θ}(φ,φ))`
  (`H:eq:rate-family-variables`) are the existing `rateV`, `rateGibbs`, `rateY`, `rateMeanN`,
  `rateVarN` of `HRS/Equilibrium/Response.lean`; `μ_θ` is given by its density `ρ θ` with the thermal
  equation (`IsThermalDensity`), as in Lemma 4.18; `rateLaw`, `rateGaussian` are the two laws.
* Distances between laws on `ℝ` are `wassersteinE` (`ℝ≥0∞`); their `θ`-integrals are `lintegral`s and
  `limsup`/`liminf` are taken in `ℝ≥0∞` (no junk values).  The `d_j` distances `smoothDist j` are real;
  they are converted by `ENNReal.ofReal`.
* Path statements (Proposition 2.10): the stationary canonical gradient law is a `SelectedFlow` with
  `law X₀ = canonicalGibbs`, on the horizon `u + T` for the window start `u ≥ 0`; `Z_β` is
  `IsStationaryGaussianField` (`HRS/Sections/Sec3.lean`); windows are `windowFluc` (centered at `μ_β`), `windowZeta` (centered at the
  actual first marginal), `windowPath`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Main

variable {d : ℕ}

/-! ### The rate family -/

/-- The law of `Y_{N,θ}` (`H:eq:rate-family-variables`, TeX L1028) under the canonical law
`ℙ_{N,θ}` of the potential `V_θ` (`HRS.rateGibbs`). -/
def rateLaw (d : ℕ) (s : ℝ) (k : Lattice d) (β : ℝ) (N : ℕ) (θ : ℝ) : Measure ℝ :=
  (rateGibbs d s k β θ N).map (rateY d s k β N θ)

/-- The law of `G_θ = Z_{β,θ}^0(φ)` (`H:eq:rate-family-variables`, TeX L1029): the centered
Gaussian `N(0, C_{β,μ_θ}(φ,φ))` with the *limiting* susceptibility variance (not the finite-`N`
variance, TeX L1031-1032), `μ_θ = ρ_θ dx`, `φ = cos(2πk·x)`. -/
def rateGaussian (d : ℕ) (s : ℝ) (k : Lattice d) (β : ℝ) (ρθ : Torus d → ℝ) : Measure ℝ :=
  gaussianLaw (susceptibilityCov (periodicRiesz d s) (withDensityReal ρθ) β
    (Torus.cosMode k) (Torus.cosMode k))

/-- The leading critical bias `b_{β,μ}` of `H:eq:critical-bias` (TeX L1041-1043),
`b_{β,μ} = (β²|𝕊^{d-1}|/d)(R_{β,μ}P_μρ) μ`, `μ = ρ dx`, as an element of `E_m` (the signed measure
with density `(β²|𝕊^{d-1}|/d)(R_{β,μ}P_μρ)ρ`; it has zero total mass since `R_{β,μ}P_μρ` is
centered, so nothing is lost by dropping the zero mode). -/
def criticalBias (d : ℕ) (s β m : ℝ) (ρ : Torus d → ℝ) : NegSobolev d m :=
  NegSobolev.ofFun m fun x =>
    β ^ 2 * sphereArea d / d *
      responseInverse (periodicRiesz d s) (withDensityReal ρ) β ρ x * ρ x

/-- The constant path `t ↦ b` in `𝒳_{m,T}` (`h(t) = b_{β,μ}`, TeX L1088). -/
def constPath (m T : ℝ) (b : NegSobolev d m) : PathSpace d m T :=
  ContinuousMap.const (Set.Icc (0 : ℝ) T) b

/-- The third central moment `∫ (x - ∫ y dν)³ dν` of a probability law `ν` on `ℝ` (the third
cumulant). -/
def thirdCentralMoment (ν : Measure ℝ) : ℝ := ∫ x, (x - ∫ y, y ∂ν) ^ 3 ∂ν

/-- The law `ν_t` of `e^{-λt}√v|G₀| + √(v(1 - e^{-2λt}))G₁` of `H:eq:half-normal` (TeX L1233-1237),
`v = v_{β,k} = (1 + βĝ(k))⁻¹`, `λ = λ_{β,k} = (2π|k|)²(β⁻¹ + ĝ(k))` (`PDE.transientRate`),
`G₀, G₁` independent standard Gaussians: the convolution of the law of `e^{-λt}√v|G₀|` with the
centered Gaussian of variance `v(1 - e^{-2λt})`. -/
def halfNormalMixtureLaw (d : ℕ) (s β : ℝ) (k : Lattice d) (t : ℝ) : Measure ℝ :=
  Measure.conv
    ((gaussianReal 0 1).map fun z : ℝ =>
      Real.exp (-PDE.transientRate d s β k * t) * Real.sqrt (1 + β * rieszCoeff d s k)⁻¹ * |z|)
    (gaussianLaw ((1 + β * rieszCoeff d s k)⁻¹ *
      (1 - Real.exp (-2 * PDE.transientRate d s β k * t))))

/-! ### Proposition 2.10: the critical marginal response

Uniformity (TeX L1001-1006, L1007-1011, L1109-1111): "the constants in the periodic equilibrium
estimates may be chosen uniformly for `β ∈ [β₋,β₊] ⋐ (0,∞)`", and the path estimate "is locally uniform in
the parameters whenever the displayed density, derivative, one-body gap and adjoint bounds remain
uniform".  Every quantitative clause of Proposition 2.10 below is therefore stated with its constant
chosen *before* `β ∈ [β₋,β₊]` (and, for the marginal expansion, before the density `ρ` ranging over
a family with uniform lower bound and derivative bound); the fixed-`β` statement of the TeX is the
case `β₋ = β₊ = β`.  **AMBIGUITY**: the TeX does not name the derivative level or the "one-body gap
and adjoint bounds"; they are determined by `V` and `β` (hence uniform on compact `β`-intervals) and
are not hypotheses; for the marginal expansion a derivative level `k₀` is asserted to exist. -/

/-- Proposition 2.10 `M:H:prop:critical` (TeX L1035-1053), the marginal part.  `s = d/2`, `d ≥ 2`,
`μ = ρ dx` with `ρ` a smooth strictly positive probability density, `m_N` the first marginal of
`ℚ_{N,β}(μ)`.  Then `m_N ≪ μ` and
`‖dm_N/dμ - 1 - (log N/N) db_{β,μ}/dμ‖_{L²(μ)} ≤ C√(log N)/N` (`H:eq:critical-L2`), where
`db_{β,μ}/dμ = (β²|𝕊^{d-1}|/d)R_{β,μ}P_μρ` (`H:eq:critical-bias`), for `N ≥ 2`.  Uniform form (see above):
there is a derivative level `k₀` such that for all `c₀ > 0`, `Λ` there is `C` with the bound for all
`β ∈ [β₋,β₊]` and all smooth positive densities `ρ ≥ c₀` with `‖ρ‖_{C^{k₀}} ≤ Λ`. -/
theorem critical_marginal_expansion (hd : 2 ≤ d) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) :
    ∃ k₀ : ℕ, ∀ c₀ Λ : ℝ, 0 < c₀ → ∃ C : ℝ, ∀ β : ℝ, β ∈ Set.Icc βm βp →
      ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, c₀ ≤ ρ x) → Torus.cbNorm k₀ ρ ≤ Λ →
      ∀ N : ℕ, 2 ≤ N →
      firstMarginal (modulatedGibbs (periodicRiesz d ((d : ℝ) / 2)) N β (withDensityReal ρ)) ≪
          withDensityReal ρ ∧
        eLpNorm (fun y =>
            ((firstMarginal (modulatedGibbs (periodicRiesz d ((d : ℝ) / 2)) N β
                (withDensityReal ρ))).rnDeriv (withDensityReal ρ) y).toReal - 1 -
              Real.log N / N * (β ^ 2 * sphereArea d / d *
                responseInverse (periodicRiesz d ((d : ℝ) / 2)) (withDensityReal ρ) β ρ y))
          2 (withDensityReal ρ) ≤ ENNReal.ofReal (C * Real.sqrt (Real.log N) / N) := by
  sorry

/-- Proposition 2.10 `M:H:prop:critical` (TeX L1051-1052): "the coefficient is nonzero for every
nonconstant periodic density": `b_{β,μ} ≠ 0` (as an element of `E_m`, any `m`) when `ρ` is a
nonconstant smooth positive density.  Statement repair ME-R4 (ISSUES; independently reviewed, approved
2026-10-20): the Sobolev index is restricted to `0 ≤ m` (for `m < 0` `NegSobolev.ofFun m f` is `0` unless
`⟨k⟩^{-m} f̂(k) ∈ ℓ²`, which needs `h ρ ∈ H^{|m|}`; the only consumer has `m ≥ 24d+240`). -/
theorem criticalBias_ne_zero (hd : 2 ≤ d) (β : ℝ) (hβ : 0 < β) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) (hnc : ∃ x y, ρ x ≠ ρ y) (m : ℝ) (hm : 0 ≤ m) :
    criticalBias d ((d : ℝ) / 2) β m ρ ≠ 0 := by
  sorry

/-- Proposition 2.10 `M:H:prop:critical` (TeX L1052): "Haar measure is exactly unbiased":
the first marginal of `ℚ_{N,β}(dx)` is `dx` for every `N ≥ 1`. -/
theorem critical_haar_unbiased (hd : 2 ≤ d) (β : ℝ) (hβ : 0 < β) (N : ℕ) (hN : 1 ≤ N) :
    firstMarginal (modulatedGibbs (periodicRiesz d ((d : ℝ) / 2)) N β (volume : Measure (Torus d))) =
      volume :=
  haar_firstMarginal_volume hd β hβ N hN

/-! #### Stationary path assertions -/

/-- Proposition 2.10 `M:H:prop:critical` (TeX L1054-1064), the centered stationary path rate
`H:eq:critical-centered-path`, uniform in the temperature.  `s = d/2` (`hs0`, `hsd` are the facts
`0 ≤ d/2 < d`, technical: they make `PDE.mfData` well formed), smooth `V`, stationary canonical
gradient law (`SelectedFlow` of `PDE.mfData` on `[0,u+T]` with `law X₀ = ℙ_{N,β}` the canonical Gibbs
law), `μ = μ_β` (`ρβ`, `IsThermalDensity`), `m ≥ 24d + 240`, `T < ∞`, `𝒳 = C([0,T];E_m)`, `Z_β` the
stationary Gaussian field.  There is `C_T` (before `β ∈ [β₋,β₊]`) such that for every `β`, window start
`u ≥ 0`, `N ≥ 2`: `W_2^𝒳(ζ_N^{u+·}, Z_β) ≤ C_T N^{-1/2}` (`ζ_N` centered at the actual first marginal,
`windowZeta`); the same upper order for `W_p`, `1 ≤ p ≤ 2`, and for the bounded smooth metrics `d_k`,
`k ≥ 1`.

Statement repair (ISSUES.md, entry "Filtered strong solutions: follow-up repairs"): the proof (TeX L5054-5070) uses the exact centered empirical mild identity (the duality identity `B:prop:duality-identity`) and the stationarity of the Gibbs law along the flow (B.15 `sde_entropy_law`), both needing a Brownian filtration, so `X` is assumed a filtered strong solution (`∃ ℱ W', IsFilteredSolution P ℱ W' W X`, the strong-solution adaptedness of A.1 that `SelectedFlow` records only as measurability, ISSUES D1). -/
theorem critical_centered_path (hd : 2 ≤ d) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (m : ℝ) (hm : 24 * (d : ℝ) + 240 ≤ m) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρβ →
      ∀ u : ℝ, 0 ≤ u → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β (hβm.trans_le hβ.1)) (u + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        law P X₀ = canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → NegSobolev d m),
        IsStationaryGaussianField P' ((d : ℝ) / 2) β hs0 hsd (hβm.trans_le hβ.1) V ρβ m Z →
        wassersteinE 2 (law P (windowZeta m T u P X)) (law P' (windowPath m T 0 Z)) ≤
          ENNReal.ofReal (C * (N : ℝ) ^ (-(1 : ℝ) / 2)) ∧
        (∀ p : ℝ, 1 ≤ p → p ≤ 2 →
          wassersteinE p (law P (windowZeta m T u P X)) (law P' (windowPath m T 0 Z)) ≤
            ENNReal.ofReal (C * (N : ℝ) ^ (-(1 : ℝ) / 2))) ∧
        (∀ k : ℕ, 1 ≤ k →
          smoothDist k (law P (windowZeta m T u P X)) (law P' (windowPath m T 0 Z)) ≤
            C * (N : ℝ) ^ (-(1 : ℝ) / 2)) := by
  sorry

/-- A set `𝒱` of smooth periodic potentials is *bounded in `C^∞`*: every `C_b^j` norm is bounded on `𝒱`
(equivalently, `𝒱` is relatively compact in `C^∞(𝕋^d)`, by Arzela-Ascoli).  Each `V ∈ 𝒱` is smooth and
periodic, so `Torus.cbNorm j V` is a finite supremum of bounded continuous functions: no junk `iSup`. -/
def PotentialFamilyBounded (𝒱 : Set (Torus d → ℝ)) : Prop :=
  (∀ V ∈ 𝒱, Torus.IsSmooth V) ∧ ∀ j : ℕ, ∃ Λ : ℝ, ∀ V ∈ 𝒱, Torus.cbNorm j V ≤ Λ

/-- Proposition 2.10 `M:H:prop:critical`, centered stationary path rate `H:eq:critical-centered-path`
(TeX L1054-1064), with the constant chosen uniformly over a compact family of potentials and over
`β ∈ [β₋,β₊]` (TeX L1001-1006: "the constants in the periodic equilibrium estimates may be chosen
uniformly for `β ∈ [β₋,β₊] ⋐ (0,∞)`"; TeX L1109-1111: "the path estimate is locally uniform in the
parameters whenever the displayed density, derivative, one-body gap, and adjoint bounds remain uniform").
This is the form needed for the periodic family `V_θ = -θφ/β`, `θ ∈ [0,R]`, of `H:eq:rate-family`
(the supremum over `θ` in `H:eq:critical-family-sharpness` and the sentence "the supremum of the
corresponding field or path distance over `θ ∈ [0,R]` therefore has the same order", TeX L1071-1072).

Reading of "the bounds remain uniform" (AMBIGUITY, flagged): the TeX names the density, derivative, one-body
gap and adjoint bounds; these are functions of `(V, β)` and are uniform on a set of potentials bounded in
every `C^j` norm (`PotentialFamilyBounded`: relatively compact in `C^∞`) together with `β` in a compact interval.
The TeX also says the proofs use finitely many derivatives (L1018) without naming the level; assuming all
`C^j` bounds is the weaker hypothesis, hence the weaker (safe) statement.  The conclusion is the frozen
`critical_centered_path` with `V` moved inside the quantifier after the constant `C`;
for `𝒱 = {V}` it is `critical_centered_path`. -/
theorem critical_centered_path_uniform (hd : 2 ≤ d) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d)
    (𝒱 : Set (Torus d → ℝ)) (h𝒱 : PotentialFamilyBounded 𝒱) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (m : ℝ) (hm : 24 * (d : ℝ) + 240 ≤ m) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ V ∈ 𝒱, ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρβ →
      ∀ u : ℝ, 0 ≤ u → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β (hβm.trans_le hβ.1)) (u + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        law P X₀ = canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → NegSobolev d m),
        IsStationaryGaussianField P' ((d : ℝ) / 2) β hs0 hsd (hβm.trans_le hβ.1) V ρβ m Z →
        wassersteinE 2 (law P (windowZeta m T u P X)) (law P' (windowPath m T 0 Z)) ≤
          ENNReal.ofReal (C * (N : ℝ) ^ (-(1 : ℝ) / 2)) ∧
        (∀ p : ℝ, 1 ≤ p → p ≤ 2 →
          wassersteinE p (law P (windowZeta m T u P X)) (law P' (windowPath m T 0 Z)) ≤
            ENNReal.ofReal (C * (N : ℝ) ^ (-(1 : ℝ) / 2))) ∧
        (∀ k : ℕ, 1 ≤ k →
          smoothDist k (law P (windowZeta m T u P X)) (law P' (windowPath m T 0 Z)) ≤
            C * (N : ℝ) ^ (-(1 : ℝ) / 2)) := by
  sorry

/-- Consistency check (sorry-free modulo `critical_centered_path_uniform`): the singleton family `𝒱 = {V}`
recovers the frozen `HRS.Main.critical_centered_path`; in particular the hypothesis `PotentialFamilyBounded {V}`
is satisfiable for every smooth `V`. -/
example : type_of% (@HRS.Main.critical_centered_path d) := by
  intro hd hs0 hsd V hV βm βp hβm hββ m hm T hT
  obtain ⟨C, hC, h⟩ := critical_centered_path_uniform hd hs0 hsd {V}
    ⟨fun W hW => by rw [Set.mem_singleton_iff.mp hW]; exact hV,
     fun j => ⟨Torus.cbNorm j V, fun W hW => by rw [Set.mem_singleton_iff.mp hW]⟩⟩
    βm βp hβm hββ m hm T hT
  exact ⟨C, hC, fun β hβ => h V rfl β hβ⟩

/-- Proposition 2.10 `M:H:prop:critical` (TeX L1081-1101), the mean-field-centered periodic field
`η_N^{u+·}` (center `μ_β`, `windowFluc`) at the critical exponent, uniform in the temperature (see the
section comment): with `r_N = (log N)/√N`, `b = b_{β,μ_β}` (`criticalBias`), `h(t) = b` (`constPath`),
`m ≥ 24d + 240`:
(i) `H:eq:critical-W-constant`: for `1 ≤ p ≤ 2`, `W_p^𝒳(η_N^{u+·}, Z_β)` is finite and
`|W_p/r_N - ‖b‖_{B_m}| ≤ C_T/√(log N)` uniformly in `u ≥ 0`;
(ii) `H:eq:critical-smooth-expansion`: for every fixed `k ≥ 2`, uniformly in `u ≥ 0` and in the unit
ball of `C_b^k(𝒳)`,
`|(E Φ(η_N^{u+·}) - E Φ(Z_β))/r_N - E[DΦ(Z_β)[h]]| ≤ C_{T,k}/√(log N)`;
(iii) `H:eq:smooth-coefficient`: the leading constant of `d_k^𝒳/r_N` is
`𝔠_k^𝒳(Z_β,h) = sup_{‖Φ‖_{C_b^k} ≤ 1}|E[DΦ(Z_β)[h]]|` (`HRS.smoothConstant`; the unit ball is
symmetric, so the sup of the signed expectation is the same), with normalized error
`O((log N)^{-1/2})`, and `𝔠_k > 0` when `h ≠ 0`.
Constants chosen before `β, ρβ, u, N`, the realization and `Z`; `N ≥ 2`.

Statement repair (ISSUES.md, entry "Filtered strong solutions: follow-up repairs"): consequence of `critical_centered_path` (TeX L5709-5730), so `X` is assumed a filtered strong solution (`∃ ℱ W', IsFilteredSolution P ℱ W' W X`) exactly as there. -/
theorem critical_bias_constants (hd : 2 ≤ d) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (m : ℝ) (hm : 24 * (d : ℝ) + 240 ≤ m) (T : ℝ) (hT : 0 < T) :
    (∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρβ →
      ∀ u : ℝ, 0 ≤ u → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β (hβm.trans_le hβ.1)) (u + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        law P X₀ = canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → NegSobolev d m),
        IsStationaryGaussianField P' ((d : ℝ) / 2) β hs0 hsd (hβm.trans_le hβ.1) V ρβ m Z →
        ∀ p : ℝ, 1 ≤ p → p ≤ 2 →
          wassersteinE p (law P (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ)))
              (law P' (windowPath m T 0 Z)) ≠ ⊤ ∧
          |(wassersteinE p (law P (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ)))
              (law P' (windowPath m T 0 Z))).toReal / (Real.log N / Real.sqrt N) -
              ‖criticalBias d ((d : ℝ) / 2) β m ρβ‖| ≤ C / Real.sqrt (Real.log N)) ∧
    (∀ k : ℕ, 2 ≤ k → ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρβ →
      ∀ u : ℝ, 0 ≤ u → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β (hβm.trans_le hβ.1)) (u + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        law P X₀ = canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → NegSobolev d m),
        IsStationaryGaussianField P' ((d : ℝ) / 2) β hs0 hsd (hβm.trans_le hβ.1) V ρβ m Z →
        (∀ Φ : PathSpace d m T → ℝ, Φ ∈ CbUnitBall (PathSpace d m T) k →
          |(∫ z, Φ z ∂(law P (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ))) -
              ∫ z, Φ z ∂(law P' (windowPath m T 0 Z))) / (Real.log N / Real.sqrt N) -
            ∫ ω, fderiv ℝ Φ (windowPath m T 0 Z ω)
              (constPath m T (criticalBias d ((d : ℝ) / 2) β m ρβ)) ∂P'|
            ≤ C / Real.sqrt (Real.log N)) ∧
        |smoothDist k (law P (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ)))
              (law P' (windowPath m T 0 Z)) / (Real.log N / Real.sqrt N) -
            smoothConstant P' k (windowPath m T 0 Z)
              (constPath m T (criticalBias d ((d : ℝ) / 2) β m ρβ))| ≤ C / Real.sqrt (Real.log N)) ∧
    (∀ k : ℕ, 2 ≤ k → ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρβ →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → NegSobolev d m),
        IsStationaryGaussianField P' ((d : ℝ) / 2) β hs0 hsd (hβm.trans_le hβ.1) V ρβ m Z →
        criticalBias d ((d : ℝ) / 2) β m ρβ ≠ 0 →
        0 < smoothConstant P' k (windowPath m T 0 Z)
          (constPath m T (criticalBias d ((d : ℝ) / 2) β m ρβ))) := by
  sorry

/-! #### The periodic family: critical sharpness -/

/-- Proposition 2.10 `M:H:prop:critical` (TeX L1019-1033, L1063-1070), sharpness in the periodic
family `H:eq:rate-family` at `s = d/2` (`d ≥ 2`, `k ≠ 0`, `μ_θ = ρ_θ dx` the thermal equilibrium of
`V_θ = -θφ/β`), `R = 16(1 + βĝ(k))`: for every `β ∈ [β₋,β₊]` there are `c, C > 0` and `N₀` (depending on `β`; statement
repair ME-R2, docs/ISSUES.md 2026-10-19: the TeX proves the claim for fixed `β`, its lower bound gives `N₀` only per `β`) such that for `N ≥ N₀`
`c N^{-1/2} ≤ ∫_0^R W_2^ℝ(Y_{N,θ}, G_θ) dθ ≤ C N^{-1/2}` (`H:eq:critical-family-sharpness`). -/
theorem critical_family_sharpness (hd : 2 ≤ d) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (k : Lattice d) (hk : k ≠ 0) :
    ∀ β ∈ Set.Icc βm βp, ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ ρ : ℝ → Torus d → ℝ,
      (∀ θ, IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) (rateV k β θ) β (ρ θ)) →
      ∀ N : ℕ, N₀ ≤ N →
      ENNReal.ofReal (c * (N : ℝ) ^ (-(1 : ℝ) / 2)) ≤
          ∫⁻ θ in Set.Icc (0 : ℝ) (16 * (1 + β * rieszCoeff d ((d : ℝ) / 2) k)),
            wassersteinE 2 (rateLaw d ((d : ℝ) / 2) k β N θ)
              (rateGaussian d ((d : ℝ) / 2) k β (ρ θ)) ∧
        ∫⁻ θ in Set.Icc (0 : ℝ) (16 * (1 + β * rieszCoeff d ((d : ℝ) / 2) k)),
            wassersteinE 2 (rateLaw d ((d : ℝ) / 2) k β N θ)
              (rateGaussian d ((d : ℝ) / 2) k β (ρ θ)) ≤
          ENNReal.ofReal (C * (N : ℝ) ^ (-(1 : ℝ) / 2)) := by
  sorry

/-- Proposition 2.10 `M:H:prop:critical` (TeX L1072-1076, `H:eq:critical-fixed-limsup`): in the
same family, a measurable set `A` of positive Lebesgue measure in `(0,R]` consists of fixed parameters
with `limsup_N √N W_2^ℝ(Y_{N,θ}, G_θ) > 0`.  (Uniform-family second-Wasserstein sharpness, not an
all-`N` lower bound at every prescribed potential, TeX L1077-1079.) -/
theorem critical_family_fixed_limsup (hd : 2 ≤ d) (β : ℝ) (hβ : 0 < β) (k : Lattice d)
    (hk : k ≠ 0) (ρ : ℝ → Torus d → ℝ)
    (hρ : ∀ θ, IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) (rateV k β θ) β (ρ θ)) :
    ∃ A : Set ℝ, MeasurableSet A ∧ A ⊆ Set.Ioc 0 (16 * (1 + β * rieszCoeff d ((d : ℝ) / 2) k)) ∧
      0 < volume A ∧ ∀ θ ∈ A,
        0 < limsup (fun N : ℕ => ENNReal.ofReal (Real.sqrt N) *
          wassersteinE 2 (rateLaw d ((d : ℝ) / 2) k β N θ)
            (rateGaussian d ((d : ℝ) / 2) k β (ρ θ))) atTop := by
  sorry

/-- Proposition 2.10 `M:H:prop:critical` (TeX L1071-1072): "the supremum of the corresponding field or
path distance over `θ ∈ [0,R]` therefore has the same order".  In the periodic family at `s = d/2`
(`m ≥ 24d + 240`, `T > 0`, thermal densities `ρ_θ` of `V_θ`), for each `N ≥ N₀` and for every choice,
for `θ ∈ [0,R]`, of a stationary canonical particle system for `V_θ` and of a stationary Gaussian field
`Z_{β,θ}` (window at start `0`), the supremum over `θ ∈ [0,R]` of
`W_2^{𝒳}(ζ_N, Z_{β,θ})` lies between `c N^{-1/2}` and `C N^{-1/2}` (the lower bound follows from
`critical_family_sharpness` and `wassersteinE_map_clm_le`, the upper bound from
`critical_centered_path` locally uniform in `θ`).

Statement repair (ISSUES.md, entry "Filtered strong solutions: follow-up repairs"): the upper bound uses `critical_centered_path`, so each `X θ` is assumed a filtered strong solution (`hfilt`, `IsFilteredSolution`) exactly as there. -/
theorem critical_family_path_sup (hd : 2 ≤ d) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d)
    (β : ℝ) (hβ : 0 < β) (k : Lattice d) (hk : k ≠ 0) (m : ℝ) (hm : 24 * (d : ℝ) + 240 ≤ m)
    (T : ℝ) (hT : 0 < T) (ρ : ℝ → Torus d → ℝ)
    (hρ : ∀ θ, IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) (rateV k β θ) β (ρ θ)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (Ω : ℝ → Type) [∀ θ, MeasurableSpace (Ω θ)] (P : ∀ θ, Measure (Ω θ))
        [∀ θ, IsProbabilityMeasure (P θ)] (X₀ : ∀ θ, Ω θ → Config d N)
        (W : ∀ θ, ℝ≥0 → Ω θ → (Fin N → Euc d)) (X : ∀ θ, ℝ≥0 → Ω θ → Config d N),
      (∀ θ ∈ Set.Icc (0 : ℝ) (16 * (1 + β * rieszCoeff d ((d : ℝ) / 2) k)),
        SelectedFlow (P θ) (PDE.mfData d ((d : ℝ) / 2) hs0 hsd (rateV k β θ) β hβ) T
          (X₀ θ) (W θ) (X θ) ∧ law (P θ) (X₀ θ) = rateGibbs d ((d : ℝ) / 2) k β θ N) →
      (∀ θ ∈ Set.Icc (0 : ℝ) (16 * (1 + β * rieszCoeff d ((d : ℝ) / 2) k)),
        ∃ (ℱ : MeasureTheory.Filtration ℝ (inferInstance : MeasurableSpace (Ω θ)))
          (W' : ℝ≥0 → Ω θ → (Fin N × Fin d) → ℝ), IsFilteredSolution (P θ) ℱ W' (W θ) (X θ)) →
      ∀ (Ω' : ℝ → Type) [∀ θ, MeasurableSpace (Ω' θ)] (P' : ∀ θ, Measure (Ω' θ))
        [∀ θ, IsProbabilityMeasure (P' θ)] (Z : ∀ θ, ℝ → Ω' θ → NegSobolev d m),
      (∀ θ ∈ Set.Icc (0 : ℝ) (16 * (1 + β * rieszCoeff d ((d : ℝ) / 2) k)),
        IsStationaryGaussianField (P' θ) ((d : ℝ) / 2) β hs0 hsd hβ (rateV k β θ) (ρ θ) m (Z θ)) →
        ENNReal.ofReal (c * (N : ℝ) ^ (-(1 : ℝ) / 2)) ≤
          ⨆ θ ∈ Set.Icc (0 : ℝ) (16 * (1 + β * rieszCoeff d ((d : ℝ) / 2) k)),
            wassersteinE 2 (law (P θ) (windowZeta m T 0 (P θ) (X θ)))
              (law (P' θ) (windowPath m T 0 (Z θ))) ∧
        (⨆ θ ∈ Set.Icc (0 : ℝ) (16 * (1 + β * rieszCoeff d ((d : ℝ) / 2) k)),
            wassersteinE 2 (law (P θ) (windowZeta m T 0 (P θ) (X θ)))
              (law (P' θ) (windowPath m T 0 (Z θ)))) ≤
          ENNReal.ofReal (C * (N : ℝ) ^ (-(1 : ℝ) / 2)) := by
  sorry

/-- `M:prose:L1104-1148` (TeX L1117-1121, L1138-1141): for the mean-field-centered Gaussian
comparison at `d/2 < s < 2d/3` the rate `√N δ_N` is order-sharp "because of the equilibrium marginal
bias": for the stationary canonical gradient law with a nonconstant thermal density `ρβ`
(smooth `V`, `m > max{d+1, d/2+2}`), there are `c > 0` and `N₀` such that for all `N ≥ N₀`, window
starts `u ≥ 0`,
`W_1^{𝒳_{m,T}}(η_N^{u+·}, Z_β) ≥ c √N δ_N`
(the mean displacement `√N(m_N - μ_β)` of `η_N` is the lower bound, by Jensen's inequality for the
first moment: `E Z_β = 0`; `‖√N(m_N - μ_β)‖_{E_m} ≥ c√N δ_N` by the marginal expansion
`H:eq:periodic-bias-expansion`).  Since `W_p ≥ W_1` for `p ≥ 1`, the same lower bound holds for every `W_p`.

Statement repair (ISSUES.md, entry "Filtered strong solutions: follow-up repairs"): the first marginal of `X^{u+·}` is the Gibbs marginal only by stationarity of the Gibbs law along the selected flow, which is the entropy inequality of B.15 `sde_entropy_law` (equality of entropy at the Gibbs initial law) (TeX L3220, L8560, L12140), and that takes a Brownian filtration; so `X` is assumed a filtered strong solution (`∃ ℱ W', IsFilteredSolution P ℱ W' W X`). -/
theorem mean_field_centering_lower_bound (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (hs1 : (d : ℝ) / 2 < s)
    (hs2 : s < 2 * (d : ℝ) / 3) (β : ℝ) (hβ : 0 < β)
    (ρβ : Torus d → ℝ) (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    (hnc : ∃ x y, ρβ x ≠ ρβ y) (m : ℝ) (hm : max ((d : ℝ) + 1) ((d : ℝ) / 2 + 2) < m) (T : ℝ)
    (hT : 0 < T) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ u : ℝ, 0 ≤ u →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P (PDE.mfData d s hs0 hsd V β hβ) (u + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        law P X₀ = canonicalGibbs (periodicRiesz d s) V N β →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → NegSobolev d m), IsStationaryGaussianField P' s β hs0 hsd hβ V ρβ m Z →
        ENNReal.ofReal (c * (Real.sqrt N * deltaN d s N)) ≤
          wassersteinE 1 (law P (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ)))
            (law P' (windowPath m T 0 Z)) := by
  sorry

/-! ### Proposition 2.11: the covariance obstruction -/

/-- Proposition 2.11 `M:H:prop:covariance-obstruction` (TeX L1149-1197), the periodic family
`H:eq:rate-family` at `d/2 < s < d` (`d ≥ 2`, `β > 0`, `k ≠ 0`, thermal densities `ρ_θ`), with
`C_N(θ) = E[Y_{N,θ}²]` (`rateVarN`), `C(θ) = E[G_θ²] = C_{β,μ_θ}(φ,φ)`, `B(θ) = b_{β,μ_θ}(φ)`
(`supercriticalBias`, `H:eq:supercritical-bias`), `δ_N = N^{1-d/s}` (`deltaN`, `s > d/2`).

There are `ε, c > 0` such that `B` is smooth, `B(0) = 0` and `inf_{0≤θ≤ε} B'(θ) > 0`, and for every
fixed `0 < a < b < ε`:
* `δ_N^{-1}∫_a^b (C_N - C) dθ → B(b) - B(a) > 0` (`H:eq:covariance-average`);
* `liminf_N δ_N^{-1}∫_a^b W_2^ℝ(Y_{N,θ},G_θ) dθ ≥ c(b-a)` (`H:eq:covariance-W2-average`);
* the interval-averaged lower bounds for `W_1` at scale `δ_N/√(log(eN))` and for every `d_j`, `j ≥ 2`,
  at scale `δ_N/log(eN)` (TeX L1184-1186; constants `c₁`, `c_j > 0` chosen before `a, b`, not claimed sharp);
and there is a dense `G_δ` subset `ℛ ⊂ (0,ε)` such that every `θ ∈ ℛ` satisfies
`limsup δ_N^{-1}W_2^ℝ(Y_{N,θ},G_θ) ≥ c` (`H:eq:covariance-fixed-limsup`), positive normalized limsups
for `W_1` and every `d_j` at the scales `H:eq:covariance-weaker-scales`, and, if `s > 2d/3`,
`limsup √N W_2 = ∞` and the same for `W_1` and each `d_j`, `j ≥ 2` (`H:eq:covariance-no-rootN`, with
the same `ℛ`).  Integrals over `θ` are `lintegral`s (distances nonnegative), `limsup/liminf` in `ℝ≥0∞`.
"Dense `G_δ` subset of `(0,ε)`": `ℛ ⊆ (0,ε)`, `IsGδ ℛ`, `(0,ε) ⊆ closure ℛ`. -/
theorem covariance_obstruction (hd : 2 ≤ d) {s : ℝ} (hs1 : (d : ℝ) / 2 < s) (hsd : s < d)
    (β : ℝ) (hβ : 0 < β) (k : Lattice d) (hk : k ≠ 0) (ρ : ℝ → Torus d → ℝ)
    (hρ : ∀ θ, IsThermalDensity (periodicRiesz d s) (rateV k β θ) β (ρ θ)) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun θ => supercriticalBias d s β (ρ θ) (Torus.cosMode k)) ∧
      supercriticalBias d s β (ρ 0) (Torus.cosMode k) = 0 ∧
      (∃ c₀ : ℝ, 0 < c₀ ∧ ∀ θ ∈ Set.Icc (0 : ℝ) ε,
        c₀ ≤ deriv (fun θ' => supercriticalBias d s β (ρ θ') (Torus.cosMode k)) θ) ∧
      (∃ c₁ : ℝ, 0 < c₁ ∧ ∃ cJ : ℕ → ℝ, (∀ j : ℕ, 2 ≤ j → 0 < cJ j) ∧
        ∀ a b : ℝ, 0 < a → a < b → b < ε →
        Tendsto (fun N : ℕ => (deltaN d s N)⁻¹ * ∫ θ in a..b,
            (rateVarN d s k β N θ - susceptibilityCov (periodicRiesz d s) (withDensityReal (ρ θ)) β
              (Torus.cosMode k) (Torus.cosMode k))) atTop
          (𝓝 (supercriticalBias d s β (ρ b) (Torus.cosMode k) -
            supercriticalBias d s β (ρ a) (Torus.cosMode k))) ∧
        0 < supercriticalBias d s β (ρ b) (Torus.cosMode k) -
          supercriticalBias d s β (ρ a) (Torus.cosMode k) ∧
        ENNReal.ofReal (c * (b - a)) ≤ liminf (fun N : ℕ =>
          ENNReal.ofReal (deltaN d s N)⁻¹ * ∫⁻ θ in Set.Icc a b,
            wassersteinE 2 (rateLaw d s k β N θ) (rateGaussian d s k β (ρ θ))) atTop ∧
        ENNReal.ofReal (c₁ * (b - a)) ≤ liminf (fun N : ℕ =>
          ENNReal.ofReal (Real.sqrt (Real.log (Real.exp 1 * N)) / deltaN d s N) *
            ∫⁻ θ in Set.Icc a b,
              wassersteinE 1 (rateLaw d s k β N θ) (rateGaussian d s k β (ρ θ))) atTop ∧
        (∀ j : ℕ, 2 ≤ j → ENNReal.ofReal (cJ j * (b - a)) ≤
          liminf (fun N : ℕ =>
            ENNReal.ofReal (Real.log (Real.exp 1 * N) / deltaN d s N) *
              ∫⁻ θ in Set.Icc a b, ENNReal.ofReal
                (smoothDist j (rateLaw d s k β N θ) (rateGaussian d s k β (ρ θ)))) atTop)) ∧
      ∃ ℛ : Set ℝ, IsGδ ℛ ∧ ℛ ⊆ Set.Ioo 0 ε ∧ Set.Ioo 0 ε ⊆ closure ℛ ∧
        ∀ θ ∈ ℛ,
          ENNReal.ofReal c ≤ limsup (fun N : ℕ => ENNReal.ofReal (deltaN d s N)⁻¹ *
            wassersteinE 2 (rateLaw d s k β N θ) (rateGaussian d s k β (ρ θ))) atTop ∧
          0 < limsup (fun N : ℕ =>
            ENNReal.ofReal (Real.sqrt (Real.log (Real.exp 1 * N)) / deltaN d s N) *
              wassersteinE 1 (rateLaw d s k β N θ) (rateGaussian d s k β (ρ θ))) atTop ∧
          (∀ j : ℕ, 2 ≤ j →
            0 < limsup (fun N : ℕ => ENNReal.ofReal (Real.log (Real.exp 1 * N) / deltaN d s N) *
              ENNReal.ofReal (smoothDist j (rateLaw d s k β N θ)
                (rateGaussian d s k β (ρ θ)))) atTop) ∧
          (2 * (d : ℝ) / 3 < s →
            limsup (fun N : ℕ => ENNReal.ofReal (Real.sqrt N) *
              wassersteinE 2 (rateLaw d s k β N θ) (rateGaussian d s k β (ρ θ))) atTop = ⊤ ∧
            limsup (fun N : ℕ => ENNReal.ofReal (Real.sqrt N) *
              wassersteinE 1 (rateLaw d s k β N θ) (rateGaussian d s k β (ρ θ))) atTop = ⊤ ∧
            ∀ j : ℕ, 2 ≤ j →
              limsup (fun N : ℕ => ENNReal.ofReal (Real.sqrt N) *
                ENNReal.ofReal (smoothDist j (rateLaw d s k β N θ)
                  (rateGaussian d s k β (ρ θ)))) atTop = ⊤) := by
  sorry

/-! ### `M:@remark:L1219`: equilibrium-relative initial laws -/

/-- `M:@remark:L1219` (TeX L1229-1241, `H:eq:half-normal`), the explicit homogeneous computation.
`V = 0`, `d ≥ 2`, `0 ≤ s < d`, `β > 0`, `k ≠ 0`, `ψ_k = √2 cos(2πk·x)`, `v = (1 + βĝ(k))⁻¹`,
`λ = λ_{β,k} = (2π|k|)²(β⁻¹ + ĝ(k))`.
(a) the event `{√N μ_N(ψ_k) > 0}` has probability exactly `1/2` under the canonical Gibbs law, for every
`N ≥ 1` (TeX L1230-1231; for `k = e_1` this is Example 5.11, `conditioned_example_explicit`);
(b) the law `ν_t` of `e^{-λt}√v|G₀| + √(v(1 - e^{-2λt}))G₁` (`G₀,G₁` independent standard Gaussians;
the convolution of the two laws) has strictly positive third central moment (= third cumulant) at
every finite time `t ≥ 0` (TeX L1238-1239);
(c) if the particle systems `X_N` start from the Gibbs law conditioned on that event (`SelectedFlow` of
the gradient dynamics with `V = 0` on `[0,t]`, mean-field density `≡ 1`), then at each fixed time `t`
the coordinate `⟨ψ_k, η_N^t⟩ = √N μ_N^t(ψ_k)` (centered at Haar measure) converges in law to `ν_t`
(TeX L1231-1235).

Statement repair (ISSUES.md, entry "Filtered strong solutions: follow-up repairs"): part (c) rests on the change-of-law path expansion for the tilted preparation (TeX L9621, Proposition `O:prop:tilt`, i.e. Theorem 2.1 / the duality identity), which needs a Brownian filtration, so in (c) each `X_N` is assumed a filtered strong solution (`∃ ℱ W', IsFilteredSolution (P N) ℱ W' (W N) (X N)`). Parts (a), (b) are static and unchanged. -/
theorem conditioned_ou (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (k : Lattice d) (hk : k ≠ 0) :
    (∀ N : ℕ, 1 ≤ N →
      (canonicalGibbs (periodicRiesz d s) (fun _ => (0 : ℝ)) N β
        {X | 0 < linCoord (volume : Measure (Torus d)) (PDE.cosTest k) X}).toReal = 1 / 2) ∧
    (∀ t : ℝ, 0 ≤ t → 0 < thirdCentralMoment (halfNormalMixtureLaw d s β k t)) ∧
    (∀ (t : ℝ), 0 ≤ t →
      ∀ (Ω : ℕ → Type) [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
        [∀ N, IsProbabilityMeasure (P N)]
        (X₀ : ∀ N, Ω N → Config d N) (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d))
        (X : ∀ N, ℝ≥0 → Ω N → Config d N),
        (∀ N : ℕ, 2 ≤ N → SelectedFlow (P N) (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) t
          (X₀ N) (W N) (X N)) →
        (∀ N : ℕ, 2 ≤ N → ∃ (ℱ : MeasureTheory.Filtration ℝ (inferInstance : MeasurableSpace (Ω N)))
          (W' : ℝ≥0 → Ω N → (Fin N × Fin d) → ℝ), IsFilteredSolution (P N) ℱ W' (W N) (X N)) →
        (∀ N : ℕ, 2 ≤ N → law (P N) (X₀ N) =
          ProbabilityTheory.cond (canonicalGibbs (periodicRiesz d s) (fun _ => (0 : ℝ)) N β)
            {Y | 0 < linCoord (volume : Measure (Torus d)) (PDE.cosTest k) Y}) →
        ConvergesInLaw
          (fun N : ℕ => law (P N) (fun ω =>
            linCoord (volume : Measure (Torus d)) (PDE.cosTest k) (X N (Real.toNNReal t) ω)))
          (halfNormalMixtureLaw d s β k t)) := by
  sorry

end Main

end HRS
