import HRS.Stochastic.SelectedFlow
import HRS.PDE.MeanFieldDefs
import HRS.Energy.Modulated

/-!
# The Lyons-Zheng reversible maximal inequality (SPEC-2.9, specification file)

Specification file (statements with `sorry` proofs; definitions contain no `sorry`).
Source: `HRS_periodic_main_20261008T010000Z.tex` ("M"): Section "The continuous-path estimate",
TeX L4973-4989 (`Q:eq:bracket-corrector` L4976, `Q:eq:LyonsZheng` L4980, `Q:eq:reversible-maximal` L4985-4988, square-summable families L4989), used
* in the proof of Theorem 2.9 (`P:eq:LZ`, `P:eq:stationary-strong-moment`, TeX L4100-4133:
  stationary strong moment `sup_N E sup_{t≤T}‖ζ_N^t‖²_{E_q} < ∞`, a square-summable family of
  Fourier statistics, Doob's inequality in both time directions);
* in the proof of Proposition 4.17 (`integrated_forcing`; statement L5009-5017, proof L5019-5052, uses the decomposition
  `Q:eq:LyonsZheng` for the stationary process).
Cited source: T. J. Lyons, W. Zheng, *A crossing estimate for the canonical process on a Dirichlet
space and a tightness result*, Astérisque 157-158 (1988), 249-271 (`P-LZ`, TeX L12570).

## Clause list

| Lean | TeX | content |
|---|---|---|
| `lyonsZheng_maximal_family` | L4985-4988 (`Q:eq:reversible-maximal`) + L4989 ("same estimate for a square-summable family") + L4108-4115 | `E sup_{t∈[a,a+T]} ∑_j |F_j(X^t) - E F_j|² ≤ C ∑_j Var F_j + C β⁻¹ T ∑_j E|∇F_j|²`, `C` absolute |
| `lyonsZheng_maximal` | L4985-4988 | the scalar case (one test function), derived from the family version |

The forward/backward martingale identity `Q:eq:LyonsZheng` itself is *not* stated: its two
martingales live in the forward and the time-reversed Brownian filtration, which the repository does
not have; only its consequence `Q:eq:reversible-maximal` is used by M, and that is what is specified.

## Representation decisions

* The process is the stationary gradient diffusion of Theorem 2.9: `IsStationaryGibbsFlow`
  (`SelectedFlow` of `PDE.mfData` = `M = -I`, noise `√(2β⁻¹)`, so `ν = β⁻¹` in the TeX's
  `Q:eq:bracket-corrector`, with `law X₀ =` canonical Gibbs law and a Brownian filtration, as in every
  path statement of `HRS/Main/HeadlineEquilibrium.lean`).  It is stationary and reversible (its law
  is the canonical Gibbs law, the process is the time-reversible gradient diffusion).
* The test functions `F` (`IsLZTest`): "F belongs to the generator domain" (TeX L4980) is represented
  by the class actually used by M: `F` is measurable, in `L²(P_{N,β})`, `C¹` on the covering space
  away from the collision set, with finite Dirichlet energy `E[∑_i|∇_iF|²] < ∞` (`configGradSq`).  It
  contains the smooth Fourier statistics of Theorem 2.9 and, by TeX L4965-4972 (cut-offs near the
  collision set, `Q:eq:error-estimate-detail`), the pair statistics of Proposition 4.17.
* The supremum over `t ∈ [a, a+T]` is written over rational `t` (a countable supremum, so the
  `lintegral` is a genuine expectation), as in `integrated_forcing`; it is the same quantity because
  `t ↦ F(X^t)` is a.s. continuous (collision-free continuous paths, `F` continuous off collisions).
* The expectation `E F` and the variance are taken under the canonical Gibbs law (the one-time
  marginal of the stationary process).  All sums are `tsum`s in `ℝ≥0∞` of `ofReal` of nonnegative
  real quantities (no junk values from non-summable series).
* `C` is an absolute number chosen before `d, N, s, V, β, T, a` and the process: the TeX's `C` comes
  from Doob's inequality in the two filtrations (`L²` constant 4), and the bracket
  `E⟨M^F⟩_T = 2νT E ∑|∇_iF|²` carries the exact `ν = β⁻¹`.

## Packet plan for the proof

Non-vacuity: `IsStationaryGibbsFlow` is not asserted to be satisfiable (same exposure as
`critical_centered_path`).  Stationarity and reversibility of the flow are NOT hypotheses: they are a
THEOREM to prove (packet LZ-b below: B.15 `sde_entropy_law` for stationarity of the Gibbs law along the
flow, plus time reversal).

1. `LZ-a` (L): forward Itô formula for `F ∈ IsLZTest`, i.e. the martingale `M^F` with bracket
   `E⟨M^F⟩_T = 2νT E∑|∇F|²` (`Q:eq:bracket-corrector`) first for `F` smooth with bounded derivatives
   (uses `IsFilteredSolution`, `empiricalMartingale`-type machinery, Dynkin/`IsFKETest`).
2. `LZ-b` (L): time reversal of the stationary process (Gibbs law reversible for the gradient SDE:
   detailed balance for the SelectedFlow; B.15 `sde_entropy_law`, stationarity), reversed filtration,
   reversed martingale `M̂`; the identity `Q:eq:LyonsZheng`.
3. `LZ-c` (M): Doob in both filtrations -> scalar maximal inequality for smooth `F`.
4. `LZ-d` (M-L): extension to `IsLZTest`.  Route: smooth compactly supported off collisions ->
   truncation (bounded-gradient approximants) -> collision cut-off using zero weighted capacity of the
   collision set for `d ≥ 2` (density `e^{-βH}` vanishes there; TeX L4965-4972) -> Fatou over the
   rational times; then the square-summable family (Hilbert-valued Doob; finite-coordinate
   approximation).
Sizes: S/M/L/XL = LZ-a L, LZ-b L-XL, LZ-c M, LZ-d M-L (total about XL).

## Doubts for the reviewer

* TeX says "generator domain"; `IsLZTest` is a (larger) Dirichlet-form-type class.  The inequality
  only involves the form `E|∇F|²`, so it passes to the closure, but the identification of the
  collision-free strong solution with the Dirichlet form of the closed generator (Markov uniqueness)
  is claimed only in prose (TeX L4965-4972, `sec:equilibrium`).
* `E sup_t` is for the family version `E sup_t ∑_j` (Hilbert-valued), not `∑_j E sup_t`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace LZ

variable {d N : ℕ}

/-- The stationary gradient diffusion of Theorem 2.9 on the horizon `T`: a `SelectedFlow` of the
gradient dynamics `PDE.mfData` (potential `V`, inverse temperature `β`, Riesz exponent `s`), adapted to
a Brownian filtration (`IsFilteredSolution`, the strong-solution adaptedness of A.1, ISSUES D1), with
the canonical Gibbs law `ℙ_{N,β}` (`H:eq:canonical`) as law of the initial configuration; hence
stationary and reversible. -/
structure IsStationaryGibbsFlow {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (s : ℝ)
    (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) (β : ℝ) (hβ : 0 < β) (T : ℝ)
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N) : Prop where
  flow : SelectedFlow P (PDE.mfData d s hs0 hsd V β hβ) T X₀ W X
  filtered : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X
  init : law P X₀ = canonicalGibbs (periodicRiesz d s) V N β

/-- The covering-space points whose projection to the torus is collision-free (an open set). -/
def coverFree (d N : ℕ) : Set (Fin N → Euc d) :=
  {Y | (fun i => (Torus.mk (Y i) : Torus d)) ∉ collisionSet d N}

/-- `∑_i |∇_{x_i} F(X)|²`, the squared configuration gradient, computed on the covering space at
`rep ∘ X` (junk value only on the collision set, a null set for the Gibbs law). -/
def configGradSq (F : Config d N → ℝ) (X : Config d N) : ℝ :=
  ∑ k : Fin N × Fin d,
    (fderiv ℝ (configLift (fun _ => F) 0) (fun i => Torus.rep (X i)) (configBasis d N k)) ^ 2

/-- The class of test functions of the Lyons-Zheng inequality (the generator/Dirichlet domain, see
the module docstring): measurable, `L²(μ)`, `C¹` off the collision set, finite Dirichlet energy. -/
structure IsLZTest (μ : Measure (Config d N)) (F : Config d N → ℝ) : Prop where
  measurable : Measurable F
  memLp : MemLp F 2 μ
  c1 : ContDiffOn ℝ 1 (configLift (fun _ => F) 0) (coverFree d N)
  energy : Integrable (configGradSq F) μ

/-- The set of rational times of `[a, a+T]` (countable supremum for the maximal function). -/
def ratTimes (a T : ℝ) : Set ℝ := {t : ℝ | t ∈ Set.Icc a (a + T) ∧ ∃ q : ℚ, (q : ℝ) = t}

/-- Lyons-Zheng reversible maximal inequality, family version
(`M:Q:eq:reversible-maximal`, TeX M L4985-4988, with "finite-coordinate approximation proves the same
estimate for a square-summable family", L4989; used for `P:eq:stationary-strong-moment`, TeX L4127-4133,
and in Proposition 4.17, TeX L5019-5052).  Cited source: Lyons-Zheng, Astérisque 157-158 (1988).

There is an absolute constant `C` such that for every `d ≥ 2`, `N ≥ 2`, `0 ≤ s < d`, smooth `V`,
`β > 0`, `T, a ≥ 0`, every stationary Gibbs flow on `[0, a+T]` and every family `(F_j)_{j∈ℕ}` of test
functions (`IsLZTest` for the canonical Gibbs law `μ = ℙ_{N,β}`),
`E sup_{t∈[a,a+T]} ∑_j (F_j(X^t) - E_μ F_j)² ≤ C ∑_j Var_μ F_j + C β⁻¹ T ∑_j E_μ ∑_i |∇_iF_j|²`
(`ν = β⁻¹`, `X^t = X t.toNNReal`).  Technical hypotheses: `d ≥ 2`, `N ≥ 2` (standing assumptions,
M L417-418), `T, a ≥ 0`, `V` smooth (Theorem 2.9), `P` a probability measure. -/
theorem lyonsZheng_maximal_family :
    ∃ C : ℝ, 0 < C ∧ ∀ (d N : ℕ), 2 ≤ d → 2 ≤ N → ∀ (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
      (V : Torus d → ℝ), Torus.IsSmooth V → ∀ (β : ℝ) (hβ : 0 < β) (T a : ℝ), 0 ≤ T → 0 ≤ a →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStationaryGibbsFlow P s hs0 hsd V β hβ (a + T) X₀ W X →
        ∀ F : ℕ → Config d N → ℝ,
          (∀ j, IsLZTest (canonicalGibbs (periodicRiesz d s) V N β) (F j)) →
          ∫⁻ ω, ⨆ t ∈ ratTimes a T,
              ∑' j, ENNReal.ofReal
                ((F j (X t.toNNReal ω) - ∫ Y, F j Y ∂(canonicalGibbs (periodicRiesz d s) V N β)) ^ 2) ∂P ≤
            ENNReal.ofReal C *
              (∑' j, ENNReal.ofReal (∫ Y, (F j Y -
                  ∫ Y', F j Y' ∂(canonicalGibbs (periodicRiesz d s) V N β)) ^ 2
                    ∂(canonicalGibbs (periodicRiesz d s) V N β)) +
                ENNReal.ofReal (β⁻¹ * T) *
                  ∑' j, ENNReal.ofReal (∫ Y, configGradSq (F j) Y
                    ∂(canonicalGibbs (periodicRiesz d s) V N β))) := by
  sorry

theorem configGradSq_zero : configGradSq (fun _ : Config d N => (0 : ℝ)) = fun _ => 0 := by
  funext X
  have h : configLift (fun (_ : ℝ) (_ : Config d N) => (0 : ℝ)) 0 = fun _ => 0 := rfl
  simp [configGradSq, h]

/-- Lyons-Zheng reversible maximal inequality, scalar version (`M:Q:eq:reversible-maximal`, TeX M
L4985-4988): `E sup_{t∈[a,a+T]} |F(X^t) - E F|² ≤ C Var F + C β⁻¹ T E ∑_i |∇_iF|²` for one test
function; consequence of `lyonsZheng_maximal_family` (take `F_0 = F`, `F_j = 0`, `j ≥ 1`). -/
theorem lyonsZheng_maximal :
    ∃ C : ℝ, 0 < C ∧ ∀ (d N : ℕ), 2 ≤ d → 2 ≤ N → ∀ (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
      (V : Torus d → ℝ), Torus.IsSmooth V → ∀ (β : ℝ) (hβ : 0 < β) (T a : ℝ), 0 ≤ T → 0 ≤ a →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStationaryGibbsFlow P s hs0 hsd V β hβ (a + T) X₀ W X →
        ∀ F : Config d N → ℝ, IsLZTest (canonicalGibbs (periodicRiesz d s) V N β) F →
          ∫⁻ ω, ⨆ t ∈ ratTimes a T,
              ENNReal.ofReal
                ((F (X t.toNNReal ω) - ∫ Y, F Y ∂(canonicalGibbs (periodicRiesz d s) V N β)) ^ 2) ∂P ≤
            ENNReal.ofReal C *
              (ENNReal.ofReal (∫ Y, (F Y -
                  ∫ Y', F Y' ∂(canonicalGibbs (periodicRiesz d s) V N β)) ^ 2
                    ∂(canonicalGibbs (periodicRiesz d s) V N β)) +
                ENNReal.ofReal (β⁻¹ * T) *
                  ENNReal.ofReal (∫ Y, configGradSq F Y
                    ∂(canonicalGibbs (periodicRiesz d s) V N β))) := by
  obtain ⟨C, hC, h⟩ := lyonsZheng_maximal_family
  refine ⟨C, hC, fun d N hd hN s hs0 hsd V hV β hβ T a hT ha Ω _ P _ X₀ W X hX F hF => ?_⟩
  classical
  set μ := canonicalGibbs (periodicRiesz d s) V N β with hμ
  have hz : IsLZTest μ (fun _ : Config d N => (0 : ℝ)) := by
    refine ⟨measurable_const, MemLp.zero, ?_, ?_⟩
    · exact contDiffOn_const
    · rw [configGradSq_zero]; exact integrable_zero _ _ _
  set F' : ℕ → Config d N → ℝ := fun j => if j = 0 then F else fun _ => (0 : ℝ) with hF'
  have h0 : F' 0 = F := by simp [hF']
  have hne : ∀ j, j ≠ 0 → F' j = fun _ => (0 : ℝ) := fun j hj => by simp [hF', hj]
  have key := h d N hd hN s hs0 hsd V hV β hβ T a hT ha P X₀ W X hX F' (fun j => by
      by_cases hj : j = 0
      · subst hj; rw [h0]; exact hF
      · rw [hne j hj]; exact hz)
  have e1 : ∀ (G : ℕ → ℝ≥0∞), (∀ j, j ≠ 0 → G j = 0) → ∑' j, G j = G 0 :=
    fun G hG => tsum_eq_single 0 hG
  have hL : ∀ (ω : Ω) (t : ℝ), (∑' j, ENNReal.ofReal
      ((F' j (X t.toNNReal ω) - ∫ Y, F' j Y ∂μ) ^ 2)) =
      ENNReal.ofReal ((F (X t.toNNReal ω) - ∫ Y, F Y ∂μ) ^ 2) := by
    intro ω t
    rw [e1 _ (fun j hj => by simp [hne j hj]), h0]
  have hV' : (∑' j, ENNReal.ofReal (∫ Y, (F' j Y - ∫ Y', F' j Y' ∂μ) ^ 2 ∂μ)) =
      ENNReal.ofReal (∫ Y, (F Y - ∫ Y', F Y' ∂μ) ^ 2 ∂μ) := by
    rw [e1 _ (fun j hj => by simp [hne j hj]), h0]
  have hE : (∑' j, ENNReal.ofReal (∫ Y, configGradSq (F' j) Y ∂μ)) =
      ENNReal.ofReal (∫ Y, configGradSq F Y ∂μ) := by
    rw [e1 _ (fun j hj => by simp [hne j hj, configGradSq_zero]), h0]
  rw [← hμ] at key
  simp only [hL, hV', hE] at key
  exact key

end LZ

end HRS
