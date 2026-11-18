import HRS.MS.PoisMarkovAux1

/-!
# POIS-MARKOV, part 2: the semigroup property of `sg`

Main theorems (supplement foundation packet POIS-MARKOV).  For a Brownian filtration
`IsBrownianFiltration P ℱ W`, `q ≥ 0`, `HasCbBound m Mb B` (`1 ≤ m`) and times `t, s ≥ 0`:

* `sg_markov`: for `h` continuous and bounded,
  `sg P W q B (t + s) h x = sg P W q B t (sg P W q B s h) x`.
* `sg_markov_C2`: the same for `h ∈ C²` with `‖D^i h‖ ≤ M` for `i ≤ 2` (the form requested in the
  packet; it is the special case of `sg_markov` since such `h` is continuous and bounded).

Statement adjustments relative to the packet sketch: the semigroup property only needs `h`
continuous (measurable would suffice) and bounded, so `sg_markov` is stated in that generality;
`sg_markov_C2` is the corollary for `C²` data with bounded derivatives.  The hypotheses `0 ≤ q`,
`1 ≤ m`, `HasCbBound m Mb B` are those of `sg_measurable_flowMap` (joint measurability of the flow);
no smoothness of `h` beyond continuity enters.  No junk values: `h` bounded and measurable makes every
Bochner integral below the integral of an integrable function.

Route.  Fix the shift time `t`.  The pathwise cocycle `mk_cocycle` gives
`flowMap (W ω) (t + s) x = flowMap (θ_t W ω) s (V ω)`, `V ω = flowMap (W ω) t x`, where
`θ_t W = W_{t+·} - W_t` (the shifted Brownian filtration of `EQLawPath1`).  The path
`θ_t W` (as a random element of `C(ℝ≥0, Fin d → ℝ)`) is independent of `ℱ_t`, and `V` is
`ℱ_t`-measurable (`mk_measurable_V`: `V` is the flow of the stopped noise `W_{min(·,t)}`,
`mk_flow_stopped`, which is `ℱ_t`-measurable by `sg_measurable_flowMap`).  The law of `θ_t W` is the
law of `W` (`bf_path_law_eq`).  Hence the joint law of `(θ_t W, V)` is a product, and Fubini gives
`E[h(flow_s(θ_t W, V))] = ∫ (∫ h(flow_s(c, y)) dLaw(W)(c)) dLaw(V)(y) = E[sg s h (V)]`.
Helper lemmas carry the prefix `mk_`.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.PoisFlow HRS.MS.PoisSg
open HRS.MD.EQLawPath

noncomputable section

namespace HRS.MS.PoisMarkov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {d : ℕ} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → Fin d → ℝ}

/-- `flowMap (W ω) c x` is `ℱ_c`-measurable in `ω`. -/
theorem mk_measurable_V (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ} (hq : 0 ≤ q) {m : ℕ}
    (hm : 1 ≤ m) {B : Euc d → Euc d} (hB : HasCbBound m Mb B) (c : ℝ≥0) (x : Euc d) :
    Measurable[ℱ c] (fun ω => flowMap q B (fun u => W u ω) (c : ℝ) x) := by
  have key : Measurable[ℱ c]
      (fun ω => flowMap q B (fun u => W (min u c) ω) (c : ℝ) x) := by
    letI : MeasurableSpace Ω := ℱ c
    have hN : SgNoise (fun (u : ℝ≥0) (ω : Ω) => W (min u c) ω) :=
      { meas := fun u => (hW.adapted (min u c)).mono
          (ℱ.mono (by exact_mod_cast min_le_right u c)) le_rfl
        cont := fun ω => (hW.cont ω).comp (continuous_id.min continuous_const)
        zero := fun ω => by simp [hW.zero ω] }
    have h1 := sg_measurable_flowMap hN hq hm hB c.coe_nonneg
    have h2 : Measurable (fun ω : Ω => (ω, x)) := measurable_id.prodMk measurable_const
    have h3 := h1.comp h2
    exact h3
  have e : (fun ω => flowMap q B (fun u => W u ω) (c : ℝ) x) =
      fun ω => flowMap q B (fun u => W (min u c) ω) (c : ℝ) x := by
    funext ω
    exact (mk_flow_stopped ⟨hq, hm, hB, hW.cont ω, hW.zero ω⟩ c c.coe_nonneg le_rfl x).symm
  rw [e]
  exact key

/-- The shifted path is independent of every `ℱ_a`-measurable random variable. -/
theorem mk_indep [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) (a : ℝ≥0)
    {E : Type*} [MeasurableSpace E] {V : Ω → E} (hV : Measurable[ℱ a] V) :
    IndepFun (bfPath (isBrownianFiltration_shift hW a)) V P := by
  have h := indep_zero_path (isBrownianFiltration_shift hW a)
  have e : (shiftFil ℱ a) 0 = ℱ a := by
    show ℱ ((a : ℝ) + 0) = ℱ a
    rw [add_zero]
  rw [e] at h
  have hc : MeasurableSpace.comap (bfPath (isBrownianFiltration_shift hW a)) inferInstance =
      MeasurableSpace.comap (fun ω => fun t : ℝ≥0 => shiftProc W a t ω) inferInstance := by
    rw [measurableSpace_continuousMap_eq, MeasurableSpace.comap_comp]
    rfl
  have h2 : Indep (MeasurableSpace.comap (bfPath (isBrownianFiltration_shift hW a)) inferInstance)
      (ℱ a) P := by
    rw [hc]; exact h.symm
  exact indep_of_indep_of_le_right h2 hV.comap_le

/-- The semigroup property for bounded continuous data. -/
theorem mk_markov_core [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ}
    (hq : 0 ≤ q) {m : ℕ} (hm : 1 ≤ m) {B : Euc d → Euc d} (hB : HasCbBound m Mb B)
    {h : Euc d → ℝ} (hh : Continuous h) {M : ℝ} (hM : ∀ y, ‖h y‖ ≤ M) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (x : Euc d) :
    sg P W q B (a + b) h x = sg P W q B a (sg P W q B b h) x := by
  set a' : ℝ≥0 := a.toNNReal with ha'
  have ha'c : (a' : ℝ) = a := Real.coe_toNNReal a ha
  have hW' := isBrownianFiltration_shift hW a'
  set Θ := bfPath hW' with hΘ
  have hΘm : Measurable Θ := measurable_bfPath hW'
  set V : Ω → Euc d := fun ω => flowMap q B (fun u => W u ω) (a' : ℝ) x with hV
  have hVm : Measurable[ℱ a'] V := mk_measurable_V hW hq hm hB a' x
  have hVm' : Measurable V := hVm.mono (ℱ.le _) le_rfl
  -- the noise on path space
  let W₀ : ℝ≥0 → C(ℝ≥0, Fin d → ℝ) → Fin d → ℝ := fun u c => c u - c 0
  have hN : SgNoise W₀ :=
    { meas := fun u => (ContinuousMap.measurable_eval u).sub (ContinuousMap.measurable_eval 0)
      cont := fun c => c.continuous.sub continuous_const
      zero := fun c => sub_self _ }
  set Ψ : C(ℝ≥0, Fin d → ℝ) × Euc d → ℝ :=
    fun p => h (flowMap q B (fun u => W₀ u p.1) b p.2) with hΨ
  have hΨm : Measurable Ψ := hh.measurable.comp (sg_measurable_flowMap hN hq hm hB hb)
  -- the pathwise cocycle
  have hcoc : ∀ ω, h (flowMap q B (fun u => W u ω) (a + b) x) = Ψ (Θ ω, V ω) := by
    intro ω
    have hH : PfHyp q Mb m B (fun u => W u ω) := ⟨hq, hm, hB, hW.cont ω, hW.zero ω⟩
    have hco := mk_cocycle hH a' hb x
    have e : a + b = (a' : ℝ) + b := by rw [ha'c]
    have e2 : mkShift (fun u => W u ω) a' = fun u => W₀ u (Θ ω) := by
      funext u
      simp [mkShift, W₀, Θ, bfPath, shiftProc]
    rw [e, hco, e2]
  have hL : sg P W q B (a + b) h x = ∫ ω, Ψ (Θ ω, V ω) ∂P := by
    unfold sg
    congr 1
    funext ω
    exact hcoc ω
  -- independence and the product structure of the joint law
  have hind : IndepFun Θ V P := mk_indep hW a' hVm
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hΘm.aemeasurable hVm'.aemeasurable).1 hind
  have hΨint : Integrable Ψ ((P.map Θ).prod (P.map V)) :=
    Integrable.of_bound hΨm.aestronglyMeasurable M (ae_of_all _ fun p => hM _)
  have hstep1 : ∫ ω, Ψ (Θ ω, V ω) ∂P = ∫ p, Ψ p ∂((P.map Θ).prod (P.map V)) := by
    rw [← hprod, integral_map (hΘm.prodMk hVm').aemeasurable hΨm.aestronglyMeasurable]
  have hstep2 := integral_prod_symm Ψ hΨint
  -- the inner integral is `sg b h y`
  have hin : ∀ y, ∫ c, Ψ (c, y) ∂(P.map Θ) = sg P W q B b h y := by
    intro y
    have hmeas : AEStronglyMeasurable (fun c => Ψ (c, y)) (P.map (bfPath hW)) :=
      (hΨm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    rw [hΘ, bf_path_law_eq hW' hW, integral_map (measurable_bfPath hW).aemeasurable hmeas]
    unfold sg
    congr 1
    funext ω
    have e : (fun u => W₀ u (bfPath hW ω)) = fun u => W u ω := by
      funext u
      simp [W₀, bfPath, hW.zero ω]
    show h (flowMap q B (fun u => W₀ u (bfPath hW ω)) b y) = _
    rw [e]
  have hfun : sg P W q B b h = fun y => ∫ c, Ψ (c, y) ∂(P.map Θ) := funext fun y => (hin y).symm
  have hsgm : AEStronglyMeasurable (sg P W q B b h) (P.map V) := by
    rw [hfun]
    exact hΨm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
  have hstep3 : ∫ y, sg P W q B b h y ∂(P.map V) = ∫ ω, sg P W q B b h (V ω) ∂P :=
    integral_map hVm'.aemeasurable hsgm
  have hV' : ∀ ω, V ω = flowMap q B (fun s => W s ω) a x := fun ω => by simp [hV, ha'c]
  rw [hL, hstep1, hstep2]
  simp_rw [hin]
  rw [hstep3]
  unfold sg
  congr 1
  funext ω
  rw [hV' ω]

/-- **POIS-MARKOV.**  The semigroup property `P_{t+s} h = P_t P_s h` of `sg` for continuous bounded
`h`, for a Brownian filtration, `q ≥ 0` and a drift `B` with `HasCbBound m Mb B`, `1 ≤ m`. -/
theorem sg_markov [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ}
    (hq : 0 ≤ q) {m : ℕ} (hm : 1 ≤ m) {B : Euc d → Euc d} (hB : HasCbBound m Mb B)
    {h : Euc d → ℝ} (hh : Continuous h) {M : ℝ} (hM : ∀ y, ‖h y‖ ≤ M) {t s : ℝ} (ht : 0 ≤ t)
    (hs : 0 ≤ s) (x : Euc d) :
    sg P W q B (t + s) h x = sg P W q B t (sg P W q B s h) x :=
  mk_markov_core hW hq hm hB hh hM ht hs x

/-- **POIS-MARKOV, `C²` form.**  `sg (t + s) h = sg t (sg s h)` for `h ∈ C²` with bounded derivatives
up to order 2. -/
theorem sg_markov_C2 [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ}
    (hq : 0 ≤ q) {m : ℕ} (hm : 1 ≤ m) {B : Euc d → Euc d} (hB : HasCbBound m Mb B)
    {h : Euc d → ℝ} (hh : ContDiff ℝ (2 : WithTop ℕ∞) h) {M : ℝ}
    (hM : ∀ i ≤ 2, ∀ y, ‖iteratedFDeriv ℝ i h y‖ ≤ M) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s)
    (x : Euc d) :
    sg P W q B (t + s) h x = sg P W q B t (sg P W q B s h) x := by
  refine sg_markov hW hq hm hB hh.continuous (M := M) (fun y => ?_) ht hs x
  have := hM 0 (Nat.zero_le _) y
  rwa [norm_iteratedFDeriv_zero] at this

end HRS.MS.PoisMarkov
