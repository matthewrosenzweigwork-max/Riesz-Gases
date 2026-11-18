import HRS.MS.LcMarkovAux1
import HRS.MS.LcEngAux3
import HRS.MS.PoisMarkovAux2

/-!
# LC-5, part 2: the Markov property `lcSg r t g = lcSg r v (lcSg v t g)` (supplement S4.11, step 5)

Main theorems (namespace `HRS.MS.Lc`).  Let `(P, ℱ, W)` be a probability space with a Brownian
filtration (`IsBrownianFiltration P ℱ W`), `ν` continuous with `0 ≤ ν`, `Q` a matrix and `c, B` data with
`LcHyp Q k Λc ΛB c B`.  For `0 ≤ r ≤ v ≤ t`:

* `lc_markov_decay`: the same for the class of `lc_engine`: `g ∈ C^k` with `decayNormE k b g < ⊤`,
  `0 ≤ b` (such `g` is continuous and bounded);
* `lc_markov`: for `g` continuous and bounded (`∀ y, ‖g y‖ ≤ M`), for every `x`,
  `lcSg P W ν Q c B r t g x = lcSg P W ν Q c B r v (lcSg P W ν Q c B v t g) x`.

Statement adjustments relative to the plan row (`docs/S4_PLAN.md`, section 2.1 step 5), all harmless
weakenings of the hypotheses: the Markov property needs neither the upper bound `ν ≤ ν*`, nor the
horizon `t ≤ T`, nor the decay hypothesis on `B`, nor `ContDiff k`: only `LcHyp` (existence, uniqueness
and the flow property of `lcFlow`) and the Brownian structure of the noise.  No junk values: `g` is
bounded and measurable (continuous), so every Bochner integral below is the integral of an integrable
function, and the inner function `lcSg v t g` is bounded and measurable (part of the proof).

Route (as for `sg_markov`, `PoisMarkovAux2`).  Fix `v` and let `a = τ(v)`.  The pathwise cocycle
`lc_flow_cocycle` gives `lcFlow (G ω) r t x = lcFlow (G ω) v t (V ω)` with `V ω = lcFlow (G ω) r v x`,
which is `ℱ_a`-measurable (`lc5_measurable_V`, locality `lc5_flow_congr_past`).  The flow from `v`
only depends on the increments of `G` after `v` (`lc5_flow_congr_future`), which are the
`lc5Path`-image of the path `Θ ω = W_{a+·} - W_a` of the shifted Brownian filtration (`lc5Path_eq`,
from `lc_noise_shift`).  `Θ` is independent of `ℱ_a` (`mk_indep`, hence of `V`), so the joint law of
`(Θ, V)` is a product and Fubini gives `E[Ψ(Θ, V)] = E[lcSg v t g (V)]`, because
`∫ Ψ(θ, y) dLaw(Θ) = ∫ g(lcFlow (G ω) v t y) dP = lcSg v t g y` by definition.
Helper lemmas carry the prefix `lc5_`.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MD.EQLawPath

noncomputable section

namespace HRS.MS.Lc

variable {d : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → Fin d → ℝ} {ν : ℝ → ℝ}

/-- The Markov property for bounded continuous data. -/
theorem lc5_markov_core [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hν : Continuous ν) (hν0 : ∀ x, 0 ≤ ν x) {Q : Matrix (Fin d) (Fin d) ℝ} {k : ℕ}
    {Λc ΛB : ℝ} {c : ℝ → Euc d} {B : ℝ → Euc d → Euc d} (H : LcHyp Q k Λc ΛB c B)
    {g : Euc d → ℝ} (hg : Continuous g) {M : ℝ} (hM : ∀ y, ‖g y‖ ≤ M) {r v t : ℝ} (hr : 0 ≤ r)
    (hrv : r ≤ v) (hvt : v ≤ t) (x : Euc d) :
    lcSg P W ν Q c B r t g x = lcSg P W ν Q c B r v (lcSg P W ν Q c B v t g) x := by
  have hv : 0 ≤ v := hr.trans hrv
  set a' : ℝ≥0 := (lcTau ν v).toNNReal with ha'
  have hW' := isBrownianFiltration_shift hW a'
  set Θ := bfPath hW' with hΘ
  have hΘm : Measurable Θ := measurable_bfPath hW'
  set V : Ω → Euc d := fun ω => lcFlow Q c B (fun u => lcNoiseE W ν u ω) r v x with hV
  have hVm : Measurable[ℱ (a' : ℝ)] V := lc5_measurable_V H hW hν hν0 hr hrv x
  have hVm' : Measurable V := hVm.mono (ℱ.le _) le_rfl
  set Ψ : C(ℝ≥0, Fin d → ℝ) × Euc d → ℝ :=
    fun p => g (lcFlow Q c B (lc5Path ν v p.1) v t p.2) with hΨ
  have hΨm : Measurable Ψ := hg.measurable.comp (lc5_meas_Psi H hν hv hvt)
  -- the pathwise identities
  have hpath : ∀ ω y, g (lcFlow Q c B (fun u => lcNoiseE W ν u ω) v t y) = Ψ (Θ ω, y) := by
    intro ω y
    have h := lc5_flow_congr_future H (lc_noiseE_cont hW hν ω) (lc5Path_cont hν v (Θ ω)) hv
      (lc5_lcW_eq hW hν hν0 hv ω) hvt y
    show _ = g (lcFlow Q c B (lc5Path ν v (Θ ω)) v t y)
    rw [h]
  have hcoc : ∀ ω, g (lcFlow Q c B (fun u => lcNoiseE W ν u ω) r t x) = Ψ (Θ ω, V ω) := by
    intro ω
    rw [lc_flow_cocycle H (lc_noiseE_cont hW hν ω) hr hrv hvt x]
    exact hpath ω (V ω)
  have hL : lcSg P W ν Q c B r t g x = ∫ ω, Ψ (Θ ω, V ω) ∂P := by
    unfold lcSg
    congr 1
    funext ω
    exact hcoc ω
  -- independence and the product structure of the joint law
  have hind : IndepFun Θ V P := HRS.MS.PoisMarkov.mk_indep hW a' hVm
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hΘm.aemeasurable hVm'.aemeasurable).1 hind
  have hΨint : Integrable Ψ ((P.map Θ).prod (P.map V)) :=
    Integrable.of_bound hΨm.aestronglyMeasurable M (ae_of_all _ fun p => hM _)
  have hstep1 : ∫ ω, Ψ (Θ ω, V ω) ∂P = ∫ p, Ψ p ∂((P.map Θ).prod (P.map V)) := by
    rw [← hprod, integral_map (hΘm.prodMk hVm').aemeasurable hΨm.aestronglyMeasurable]
  have hstep2 := integral_prod_symm Ψ hΨint
  -- the inner integral is `lcSg v t g y`
  have hin : ∀ y, ∫ c', Ψ (c', y) ∂(P.map Θ) = lcSg P W ν Q c B v t g y := by
    intro y
    have hm2 : Measurable fun c' : C(ℝ≥0, Fin d → ℝ) => Ψ (c', y) := by
      have h2 : Measurable fun c' : C(ℝ≥0, Fin d → ℝ) => (c', y) :=
        measurable_id.prodMk measurable_const
      have h3 := hΨm.comp h2
      exact h3
    rw [integral_map hΘm.aemeasurable hm2.aestronglyMeasurable]
    unfold lcSg
    congr 1
    funext ω
    exact (hpath ω y).symm
  have hfun : lcSg P W ν Q c B v t g = fun y => ∫ c', Ψ (c', y) ∂(P.map Θ) :=
    funext fun y => (hin y).symm
  have hsgm : AEStronglyMeasurable (lcSg P W ν Q c B v t g) (P.map V) := by
    rw [hfun]
    exact hΨm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
  have hstep3 : ∫ y, lcSg P W ν Q c B v t g y ∂(P.map V) =
      ∫ ω, lcSg P W ν Q c B v t g (V ω) ∂P :=
    integral_map hVm'.aemeasurable hsgm
  rw [hL, hstep1, hstep2]
  simp_rw [hin]
  rw [hstep3]
  rfl

/-- **LC-5 (Markov property of `lcSg`).**  For a Brownian filtration, `ν` continuous and
nonnegative, data with `LcHyp Q k Λc ΛB c B`, times `0 ≤ r ≤ v ≤ t` and `g` continuous and bounded,
`lcSg r t g = lcSg r v (lcSg v t g)` pointwise. -/
theorem lc_markov [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hν : Continuous ν) (hν0 : ∀ x, 0 ≤ ν x) {Q : Matrix (Fin d) (Fin d) ℝ} {k : ℕ}
    {Λc ΛB : ℝ} {c : ℝ → Euc d} {B : ℝ → Euc d → Euc d} (H : LcHyp Q k Λc ΛB c B)
    {g : Euc d → ℝ} (hg : Continuous g) {M : ℝ} (hM : ∀ y, ‖g y‖ ≤ M) {r v t : ℝ} (hr : 0 ≤ r)
    (hrv : r ≤ v) (hvt : v ≤ t) (x : Euc d) :
    lcSg P W ν Q c B r t g x = lcSg P W ν Q c B r v (lcSg P W ν Q c B v t g) x :=
  lc5_markov_core hW hν hν0 H hg hM hr hrv hvt x

/-- A function with `decayNormE k b g < ⊤`, `0 ≤ b`, is bounded. -/
theorem lc5_bdd_of_decayNormE {k : ℕ} {b : ℝ} (hb : 0 ≤ b) {g : Euc d → ℝ}
    (hg : decayNormE k b g < ⊤) : ∃ M : ℝ, ∀ y, ‖g y‖ ≤ M := by
  refine ⟨(decayNormE k b g).toReal, fun y => ?_⟩
  have h1 : ENNReal.ofReal (jbracket y ^ (b + (((0 : Fin (k + 1)) : ℕ) : ℝ)) *
      |partialDeriv (Fin.elim0 : Fin ((0 : Fin (k + 1)) : ℕ) → Fin d) g y|) ≤
      decayNormE k b g := by
    unfold decayNormE derivSupE
    exact le_iSup_of_le (0 : Fin (k + 1)) (le_iSup_of_le
      (Fin.elim0 : Fin ((0 : Fin (k + 1)) : ℕ) → Fin d) (le_iSup_of_le y le_rfl))
  have h2 := (ENNReal.ofReal_le_iff_le_toReal hg.ne).1 h1
  have h3 : |partialDeriv (Fin.elim0 : Fin ((0 : Fin (k + 1)) : ℕ) → Fin d) g y| = ‖g y‖ := by
    simp [partialDeriv, iteratedFDeriv_zero_apply]
  rw [h3] at h2
  have hj0 : 1 ≤ jbracket y := by
    unfold jbracket
    exact (Real.le_sqrt' one_pos).2 (by nlinarith [sq_nonneg ‖y‖])
  have hj : 1 ≤ jbracket y ^ (b + (((0 : Fin (k + 1)) : ℕ) : ℝ)) :=
    Real.one_le_rpow hj0 (by simpa using hb)
  nlinarith [mul_le_mul_of_nonneg_right hj (norm_nonneg (g y))]

/-- **LC-5, `lc_engine` class.**  The Markov property for `g ∈ C^k` with `decayNormE k b g < ⊤`,
`0 ≤ b` (such `g` is continuous and bounded). -/
theorem lc_markov_decay [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hν : Continuous ν) (hν0 : ∀ x, 0 ≤ ν x) {Q : Matrix (Fin d) (Fin d) ℝ} {k : ℕ}
    {Λc ΛB : ℝ} {c : ℝ → Euc d} {B : ℝ → Euc d → Euc d} (H : LcHyp Q k Λc ΛB c B)
    {b : ℝ} (hb : 0 ≤ b) {g : Euc d → ℝ} (hg : ContDiff ℝ (k : WithTop ℕ∞) g)
    (hgd : decayNormE k b g < ⊤) {r v t : ℝ} (hr : 0 ≤ r) (hrv : r ≤ v) (hvt : v ≤ t)
    (x : Euc d) :
    lcSg P W ν Q c B r t g x = lcSg P W ν Q c B r v (lcSg P W ν Q c B v t g) x := by
  obtain ⟨M, hM⟩ := lc5_bdd_of_decayNormE hb hgd
  exact lc_markov hW hν hν0 H hg.continuous hM hr hrv hvt x

end HRS.MS.Lc
