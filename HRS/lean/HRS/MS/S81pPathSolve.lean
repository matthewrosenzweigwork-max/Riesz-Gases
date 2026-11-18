import HRS.MS.WsStatAux17
import HRS.MS.S81w2Burn
import HRS.MD.EQLawPath3

/-!
# S8.1 (worker S81P), item 2, part 1: a maximal collision-free solution on the canonical data space

Namespace `HRS.Whole.S81P`, prefix `s81p_`.

Path-law stationarity of the canonical realizations (`S81W2PathStat`) is proved here WITHOUT Yamada-Watanabe and without weak
uniqueness theory, along the route of the torus packet `EQLawPath` (`HRS/MD/EQLawPath*`): the additive-noise SDE has
DETERMINISTIC pathwise uniqueness on the open collision-free set (`ode_additive_unique`), so a maximal solution constructed ONCE on the canonical
data space `Sigma = Config x C(R>=0, R^{N x d})` (law `Gibbs x Wiener`) represents every collision-free strong solution
(`s81p_compare`, next file) as a fixed measurable functional of the data (initial configuration, driving path).

This file: the canonical space `PSig d N`, its coordinate driver `psigW`, and the maximal solution on it
(`s81p_maximal`), by `exists_sde_solution_maximal` for the Brownian filtration of `ssp1_base`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Whole HRS.MP.SelfSimP1 HRS.MS.S21 HRS.MD.EQLawPath
open scoped ENNReal NNReal BigOperators

namespace HRS.Whole.S81P

variable {d N : ℕ}

/-- The canonical data space: initial configuration of `R^d` and continuous driving path. -/
abbrev PSig (d N : ℕ) : Type := EucConfig d N × WSp d N

/-- The coordinate driver on the canonical data space. -/
def psigW (d N : ℕ) : ℝ≥0 → PSig d N → (Fin N → Euc d) :=
  fun t σ i => WithLp.toLp 2 fun j => σ.2 t (i, j)

theorem s81p_measurable_psigW (t : ℝ≥0) : Measurable (psigW d N t) := by
  refine measurable_pi_iff.2 fun i => (WithLp.measurable_toLp 2 _).comp ?_
  refine measurable_pi_iff.2 fun j => ?_
  exact ((measurable_pi_apply (i, j)).comp (ContinuousMap.measurable_eval t)).comp measurable_snd

theorem s81p_continuous_psigW (σ : PSig d N) (i : Fin N) (j : Fin d) :
    Continuous fun t => psigW d N t σ i j := by
  have := (continuous_apply (i, j)).comp σ.2.continuous
  exact this

theorem s81p_psigW_apply (t : ℝ≥0) (σ : PSig d N) (i : Fin N) (j : Fin d) :
    psigW d N t σ i j = σ.2 t (i, j) := rfl

/-- The maximal collision-free solution on the canonical data space.

`Q` is a probability measure on `PSig d N` for which the coordinate driver is a vector Brownian motion independent of the initial
configuration, the initial configuration being a.s. collision free.  Then there are a lifetime `τ` and a process `Y`, measurable at
every time, with values in the collision-free set, leaving every compact subset of it before `τ < ∞`, and which is for `Q`-a.e. data
`(x, w)` the pathwise (maximal) solution of the quadratic gradient dynamics started at `x`, driven by `w`. -/
theorem s81p_maximal (s a β : ℝ) (Q : Measure (PSig d N)) [IsProbabilityMeasure Q]
    (hBrQ : IsVectorBrownian Q (psigW d N))
    (hindQ : IndepFun Prod.fst (fun σ : PSig d N => fun t => psigW d N t σ) Q)
    (hdist : ∀ᵐ σ ∂Q, σ.1 ∉ eucCollisionSet d N) :
    ∃ (τ : PSig d N → WithTop ℝ) (Y : ℝ → PSig d N → EucConfig d N),
      (∀ t, Measurable (Y t)) ∧ (∀ T : ℝ, MeasurableSet {σ | (T : WithTop ℝ) < τ σ}) ∧
      (∀ σ, 0 < τ σ) ∧
      (∀ σ, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ σ → Y t σ ∈ ssp1_U d N) ∧
      (∀ σ, τ σ < ⊤ → ∀ K : Set (EucConfig d N), IsCompact K → K ⊆ ssp1_U d N →
        ∀ t₀ : ℝ, (t₀ : WithTop ℝ) < τ σ → ∃ t : ℝ, t₀ < t ∧ (t : WithTop ℝ) < τ σ ∧ Y t σ ∉ K) ∧
      ∀ᵐ σ ∂Q, IsPathSolution (s21f_b d N s a β) (ssp1_sigma d N β⁻¹) (fun t => σ.2 t) σ.1 (τ σ)
        (fun t => Y t σ) := by
  classical
  obtain ⟨ℱ, W', hBF, hcomp, hWW', hX₀ℱ, -, -⟩ :=
    ssp1_base Q (psigW d N) hBrQ Prod.fst measurable_fst hindQ
  have hcoll : MeasurableSet (eucCollisionSet d N) := (ssp1_isClosed_coll d N).measurableSet
  obtain ⟨σ₀, hσ₀⟩ := hdist.exists
  let Y₀ : PSig d N → EucConfig d N := fun σ =>
    if σ.1 ∈ eucCollisionSet d N then σ₀.1 else σ.1
  have hY₀m : ∀ t : ℝ, Measurable[ℱ t] Y₀ := by
    intro t
    let _ : MeasurableSpace (PSig d N) := ℱ t
    exact Measurable.ite ((hX₀ℱ t) hcoll) measurable_const (hX₀ℱ t)
  have hY₀U : ∀ σ, Y₀ σ ∈ ssp1_U d N := by
    intro σ
    by_cases h : σ.1 ∈ eucCollisionSet d N
    · simp only [Y₀, h, ↓reduceIte]; exact hσ₀
    · simp only [Y₀, h, ↓reduceIte]; exact h
  have hY₀ae : ∀ᵐ σ ∂Q, Y₀ σ = σ.1 := by
    filter_upwards [hdist] with σ h
    simp only [Y₀, h, ↓reduceIte]
  obtain ⟨τ, Y, hstop, hpos, hsol, hmem, hexit, -⟩ := exists_sde_solution_maximal hBF
    (ssp1_U d N) (ssp1_isOpen_U d N) (s21f_b d N s a β) (s21f_locLipschitz s a β)
    (ssp1_sigma d N β⁻¹) Y₀ hY₀m hY₀U
  refine ⟨τ, Y, fun t => (hsol.adapted t).mono (ℱ.le t) le_rfl, fun T => ?_, hpos, hmem, hexit, ?_⟩
  · have h1 : MeasurableSet[ℱ T] {σ | τ σ ≤ (T : WithTop ℝ)} := hstop.measurableSet_le T
    have h2 : {σ | (T : WithTop ℝ) < τ σ} = {σ | τ σ ≤ (T : WithTop ℝ)}ᶜ := by
      ext σ; simp [not_le]
    rw [h2]
    exact (ℱ.le T _ h1).compl
  · filter_upwards [hsol.isPathSolution, hWW', hY₀ae] with σ h1 hw hY0
    have hwe : (fun t : ℝ≥0 => W' t σ) = fun t => σ.2 t := by
      funext t
      funext ij
      exact hw t ij.1 ij.2
    rw [hwe, hY0] at h1
    exact h1

end HRS.Whole.S81P
