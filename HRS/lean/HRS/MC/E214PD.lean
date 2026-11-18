import HRS.MC.E214Unique
import HRS.MC.E214E5
import HRS.MC.QRAsmFinal
import HRS.MC.E213U3G
import HRS.MC.E213U1b
import HRS.MC.E213U11j
import HRS.MC.E213U13o
import HRS.MC.E213U2
import HRS.MC.E213TSymm
import HRS.MC.E213Final
import HRS.MC.S7PIDDefs

/-!
# Plan for the tensor half of Corollary 2.14 (`stationary_tensor_relaxation`): the REMAINING chain

Plan file (statements compile; every lemma marked `sorry` is a work packet; the glue is proved).  Companion note:
`docs/MC_E214_TENSOR_PLAN.md` (answer to the key question M3, packet table, dependency graph, traps, estimate).

Proved here (trivial glue): `edgeworth_window_forall_gd` (the proof of `E214A.edgeworth_window_gd` works for EVERY
`GaussData`), `Kproj_eq_of_gd`, `K_eq_Kproj` (any `K` with `IsWindowEdgeworth` is `gd.Kproj T` for every `gd`, by
`E214U.windowEdgeworth_tensor_unique`), `norm_sub_le_exp` and the final assembly `stationary_tensor_relaxation_chain`
(its type is checked equal to `HRS.Main.stationary_tensor_relaxation`).

Layout: §0 data (`StatDatum` = what packet e214i provides, `CoupledPair`, `PairGD` = the pair as two `GaussData` on ONE
probability space); §1 uniqueness glue; §2 fixed-time and path estimates of the pair; §3 propagator comparison (the
unavoidable operator input); §4 relaxation of the correction data `D_a, J_a` (P6); §5 tensor assembly (P8); §6 the
stationary tensor `Kst` (P7); §7 final assembly (P9), with the covariance half taken as a hypothesis lemma (packet e214h).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214Plan

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final

variable {d : ℕ}

/-! ## §0  Data -/

/-- What packet e214i provides (`E214I.stationaryPrepared`, `stationaryPrepared_hE`, `stationaryRegime_*`): a stationary
prepared datum `Ss` (initial density `ρβ`, constant trajectory `ρβ`, `β₀ = S.β`, same dynamics) with `EdgeworthHyp` at the
same `m`, whose regime has the same dynamics and the constant density `R.ρβ`.  Kept abstract so that this file does not
import `E214I` (not merged on this branch). -/
structure StatDatum (S : PreparedData d) (β₀ m : ℝ) (hE : EdgeworthHyp S β₀ m) where
  Ss : PreparedData d
  hEs : EdgeworthHyp Ss S.β m
  hD : (regime Ss S.β hEs).D = (regime S β₀ hE).D
  hρ : (regime Ss S.β hEs).ρ = fun _ => (regime S β₀ hE).ρβ
  hρ₀ : (regime Ss S.β hEs).ρ₀ = (regime S β₀ hE).ρβ

/-- The six hypotheses of `quadratic_relaxation` / `l2c6c_proof` / `exists_coupled_pair_proof` (copy of
`E214F.IsCoupledPair`, which lives in a file containing `sorry`): independent Gaussian initial fields, the prepared and
the stationary linear fluctuation solutions, driven by the same noise. -/
def CoupledPair (R : Regime d) (r : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Y₀ Ys₀ : Ω → NegSobolev d r) (η ηs : ℝ → Ω → NegSobolev d r) : Prop :=
  IsCenteredGaussianWithCov r (P.map Y₀)
      (susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρ₀) R.β₀) ∧
    IsCenteredGaussianWithCov r (P.map Ys₀)
      (susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρβ) R.β) ∧
    IndepFun Y₀ Ys₀ P ∧
    (∀ T : ℝ, IsLinearFluctuationSolution P R.D R.ρ r R.D.invβ T Y₀ η) ∧
    (∀ T : ℝ, IsLinearFluctuationSolution P R.D (fun _ => R.ρβ) r R.D.invβ T Ys₀ ηs) ∧
    IsSameNoise R.D R.ρ (fun _ => R.ρβ) r P Y₀ Ys₀ η ηs

section Pair

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (sd : StatDatum S β₀ m hE)

/-- The coupled pair `(η, η̄)` together with the Wick fields `B, B̄` of the two fields, on ONE probability space.  The
fields are those of two `GaussData` (the prepared one for `S` and the stationary one for `Ss`) sharing `(Ω, P)`; packaging
them as a structure avoids type equalities `gds.Ω₀ = gd.Ω₀`. -/
structure PairGD where
  Ω : Type
  [mΩ : MeasurableSpace Ω]
  P : Measure Ω
  [pP : IsProbabilityMeasure P]
  Y₀ : Ω → NegSobolev d (rLvl d)
  Ys₀ : Ω → NegSobolev d (rLvl d)
  η : ℝ → Ω → NegSobolev d (rLvl d)
  ηs : ℝ → Ω → NegSobolev d (rLvl d)
  B : ℝ → Ω → NegSobolev d (rLvl d)
  Bs : ℝ → Ω → NegSobolev d (rLvl d)
  pair : CoupledPair (regime S β₀ hE) (rLvl d) P Y₀ Ys₀ η ηs
  limit_s : IsGaussianLimitField sd.Ss.dyn sd.Ss.ρ (withDensityReal sd.Ss.ρ0) S.β (rLvl d) P ηs
  B_meas : Measurable (Function.uncurry B)
  B_wick : ∀ᵐ t ∂(volume.restrict (Set.Ici (0 : ℝ))),
    IsWickQuadraticField S.s P (fun ω => η t ω) (withDensityReal (S.ρ t)) (B t)
  B_L2 : ∀ Rw : ℝ, 0 < Rw → ∀ a : ℝ, 0 ≤ a →
    ∀ᵐ ω ∂P, MemLp (fun t => B (a + t) ω) 2 (volume.restrict (Set.Icc (0 : ℝ) Rw))
  Bs_meas : Measurable (Function.uncurry Bs)
  Bs_wick : ∀ᵐ t ∂(volume.restrict (Set.Ici (0 : ℝ))),
    IsWickQuadraticField sd.Ss.s P (fun ω => ηs t ω) (withDensityReal (sd.Ss.ρ t)) (Bs t)
  Bs_L2 : ∀ Rw : ℝ, 0 < Rw → ∀ a : ℝ, 0 ≤ a →
    ∀ᵐ ω ∂P, MemLp (fun t => Bs (a + t) ω) 2 (volume.restrict (Set.Icc (0 : ℝ) Rw))
  /-- The path-supremum estimate of the pair.  It is a property of the SPECIFIC pair built in `E214G` (the increment
  bound of `E214G` holds for that pair only, not for every `CoupledPair`), hence a field. -/
  path_sup : ∀ T : ℝ, 0 < T → ∀ p : ℝ, 2 ≤ p → ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ a : ℝ, 0 ≤ a →
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖η (a + t) ω - ηs (a + t) ω‖ₑ) ^ p ∂P ≤
      ENNReal.ofReal ((C * Real.exp (-κ * a)) ^ p)

attribute [instance] PairGD.mΩ PairGD.pP

variable {sd}

/-- The prepared `GaussData` of the pair (first marginal). -/
def PairGD.gd (pg : PairGD sd) : GaussData S β₀ hE where
  Ω₀ := pg.Ω
  P₀ := pg.P
  η := pg.η
  B := pg.B
  limit := ⟨pg.Y₀, pg.pair.1, pg.pair.2.2.2.1⟩
  B_meas := pg.B_meas
  B_wick := pg.B_wick
  B_L2 := pg.B_L2

/-- The stationary `GaussData` of the pair (second marginal), for the stationary datum `Ss`. -/
def PairGD.gds (pg : PairGD sd) : GaussData sd.Ss S.β sd.hEs where
  Ω₀ := pg.Ω
  P₀ := pg.P
  η := pg.ηs
  B := pg.Bs
  limit := pg.limit_s
  B_meas := pg.Bs_meas
  B_wick := pg.Bs_wick
  B_L2 := pg.Bs_L2

end Pair

/-! ## §1  Uniqueness glue (proved) -/

section Glue

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m}

/-- **Every** `GaussData` gives a window family satisfying `IsWindowEdgeworth` (the proof of `E214A.edgeworth_window_gd`
never uses that `gd` comes from `exists_gaussData`; the quantifier `∀ gd` is in `uniform_over_realisations_final`).
(i) none (TeX: the Gaussian data of Theorem 2.13 are unique up to law); (ii) `E213Final.uniform_over_realisations_final`,
`E214A.edgeworth_window_gd`; (iii) copy, 45 lines, PROVED; LOW; (iv) none. -/
theorem edgeworth_window_forall_gd (T : ℝ) (hT : 0 < T) (gd : GaussData S β₀ hE) :
    ∃ ε : ℕ → ℝ, IsWindowEdgeworth S β₀ m T (gd.Kproj T) ε := by
  obtain ⟨CK, hCK⟩ := HRS.MC.E213U11.Kproj_bounded_proof gd T hT
  have hqual : ∀ η : ℝ, η > 0 → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x : ExpData S β₀ m T,
      |(fun (N : ℕ) (x : ExpData S β₀ m T) => if x.N = N then x.expr (gd.Kproj T) else 0) N x| ≤ η := by
    intro η hη
    obtain ⟨N₀, hN₀⟩ := uniform_over_realisations_final hE T hT gd η hη
    refine ⟨N₀, fun N hN x => ?_⟩
    by_cases hx : x.N = N
    · simp only [hx, if_true]
      have h0 : 0 ≤ x.expr (gd.Kproj T) := abs_nonneg _
      rw [abs_of_nonneg h0]
      exact hN₀ x (hx ▸ hN)
    · simp only [hx, if_false, abs_zero]
      exact hη.le
  have hbdd : ∀ N : ℕ, ∃ C : ℝ, ∀ x : ExpData S β₀ m T,
      |(fun (N : ℕ) (x : ExpData S β₀ m T) => if x.N = N then x.expr (gd.Kproj T) else 0) N x| ≤ C := by
    intro N
    refine ⟨2 * Real.sqrt N + CK / 6 + |CK| / 6, fun x => ?_⟩
    by_cases hx : x.N = N
    · simp only [hx, if_true]
      have h0 : 0 ≤ x.expr (gd.Kproj T) := abs_nonneg _
      rw [abs_of_nonneg h0]
      have h1 := HRS.MC.E213U6.expr_le_proof T (gd.Kproj T) CK (fun a ha => hCK a ha) x
      subst hx
      have h2 : CK / 6 ≤ |CK| / 6 := by
        have := le_abs_self CK
        linarith
      linarith [abs_nonneg CK]
    · simp only [hx, if_false, abs_zero]
      have := Real.sqrt_nonneg (N : ℝ)
      linarith [abs_nonneg CK, neg_abs_le CK]
  obtain ⟨ε, hε0, -, hεbd⟩ := E213B.e213b_exists_eps (ι := ExpData S β₀ m T)
    (fun (N : ℕ) (x : ExpData S β₀ m T) => if x.N = N then x.expr (gd.Kproj T) else 0) hqual hbdd
  refine ⟨ε, ?_⟩
  refine ⟨fun a ha M σ => Kproj_symmetric_final gd T hT a ha M σ, ⟨CK, fun a ha => hCK a ha⟩, hε0, ?_,
    fun a ha => HRS.MC.E213U18.Kproj_formula_proof gd T hT a ha⟩
  intro a ha N hN Ω _ P _ X₀ W X hSel hfilt hlaw ν hν Ω' _ P' _ Z₀ Z hZ Φ hΦ
  have h := hεbd N hN ⟨a, ha, N, hN, Ω, P, X₀, W, X, hSel, hfilt, hlaw, ν, hν, Ω', P', Z₀, Z, hZ, Φ, hΦ⟩
  simp only [if_true] at h
  have h0 : 0 ≤ (ExpData.mk a ha N hN Ω P X₀ W X hSel hfilt hlaw ν hν Ω' P' Z₀ Z hZ Φ hΦ).expr (gd.Kproj T) :=
    abs_nonneg _
  rw [abs_of_nonneg h0] at h
  exact h

/-- Any two `GaussData` of the same datum have the same window tensors (uniqueness of the tensor in the expansion,
`E214U.windowEdgeworth_tensor_unique`).  This is the gluing device of the whole plan: the pair space carries its own
`GaussData`, the 2.13 family `K` is identified with `Kproj` of ANY of them.  PROVED from `edgeworth_window_forall_gd`. -/
theorem Kproj_eq_of_gd (T : ℝ) (hT : 0 < T) (gd gd' : GaussData S β₀ hE) :
    ∀ a : ℝ, 0 ≤ a → gd.Kproj T a = gd'.Kproj T a := by
  obtain ⟨ε, h⟩ := edgeworth_window_forall_gd (hE := hE) T hT gd
  obtain ⟨ε', h'⟩ := edgeworth_window_forall_gd (hE := hE) T hT gd'
  exact HRS.MC.E214U.windowEdgeworth_tensor_unique S β₀ m T hE hT h h'

/-- Any `K` with `IsWindowEdgeworth` is `gd.Kproj T` (for every `gd`). -/
theorem K_eq_Kproj (T : ℝ) (hT : 0 < T) {K : ℝ → projTensor (PathSpace d m T) 3} {ε : ℕ → ℝ}
    (hK : IsWindowEdgeworth S β₀ m T K ε) (gd : GaussData S β₀ hE) :
    ∀ a : ℝ, 0 ≤ a → K a = gd.Kproj T a := by
  obtain ⟨ε', h'⟩ := edgeworth_window_forall_gd (hE := hE) T hT gd
  exact HRS.MC.E214U.windowEdgeworth_tensor_unique S β₀ m T hE hT hK h'

end Glue

end HRS.MC.E214Plan

end
