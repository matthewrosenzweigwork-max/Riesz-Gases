import HRS.MS.PoisInvAux1

/-!
# POIS-INV (part 2): invariance of the semigroup for invariant measures

Supplement foundation packet POIS-INV (`docs/SUPP_FOUND_PACKETS.md`, Track C).  Setting as in
`PoisInvAux1`: `q > 0`, `B` with `HasCbBound m Mb B` (`2 ≤ m`), a Brownian filtration
`IsBrownianFiltration P ℱ W`, the semigroup `sg P W q B t h x = E h(X^x_t)` of
`dX = (-q X + B X) dt + √2 dW` (`PoisSgAux2`), and `μ` with `IsInvariantMeasure (-q x + B x) μ`
and `∫ ‖x‖² dμ < ∞`.

Main theorem `HRS.MS.PoisInv.pois_inv`: for `g ∈ C²` with bounded `Dg`, `D²g`,
`∫ L g dμ = 0` (with `L g` integrable) and, for every `t ≥ 0`, `g` and `sg t g` are `μ`-integrable and
`∫ sg t g dμ = ∫ g dμ`.

Route.  The commutation `P_s (L g) = L (P_s g)` is NOT assumed: for bounded `g ∈ C²` it follows
from the Markov property (`sg_markov_C2`) and the Kolmogorov equation (`pois_kolmogorov`) applied
to `g` and to `u = P_s g`, by uniqueness of the right derivative at `s` of `r ↦ P_r g (x)`
(`inv_commute`; here `P_s g ∈ C²` with bounded derivatives, uniformly in `s ∈ [0,T]`, by
`sg_contDiff`).  Then, with the integrated Kolmogorov identity `P_t g = g + ∫_0^t P_s (L g) ds`, the
infinitesimal invariance of `PoisInvAux1` for `u = P_s g` (`inv_generator`) and Fubini
(`(s,x) ↦ P_s (L g)(x)` is jointly continuous by `kl_cont_integral` and bounded by
`A (1 + ‖x‖)`), `∫ (P_t g - g) dμ = ∫_0^t ∫ L (P_s g) dμ ds = 0` (`inv_semigroup_bdd`).  The
bounded case is extended to `g` of linear growth by the cutoffs `φ(x/R) g` (uniformly bounded
`D`, `D²`, `inv_cut_bounds`), dominated convergence under `P` (second moments of the flow,
`sg_second_moment`) and under `μ`.

Statement adjustments relative to the packet sketch: integrability of `g` and `sg t g` is part of
the conclusion (so the equality is not a junk value of the Bochner integral); `t ≥ 0`; the second
derivative bound is stated for `iteratedFDeriv ℝ 2 g` (as in `pois_kolmogorov`).  Helper lemmas
carry the prefix `inv_`.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Interval
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.PoisFlow HRS.MS.PoisSg
  HRS.MS.PoisMarkov HRS.MS.PoisKolm HRS.MS.PoisInv
open HRS.MS.FlowB (clampT continuous_clampT clampT_mem clampT_of_mem)

noncomputable section

namespace HRS.MS.PoisInv

universe u

variable {d : ℕ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → Fin d → ℝ}

theorem inv_sg_zero [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ}
    (hq : 0 ≤ q) {m : ℕ} (hm : 1 ≤ m) {B : Euc d → Euc d} (hB : HasCbBound m Mb B)
    (h : Euc d → ℝ) (x : Euc d) : sg P W q B 0 h x = h x := by
  have hn := sgNoise_of_brownian hW
  have hflow : ∀ ω, flowMap q B (fun s => W s ω) 0 x = x := fun ω => by
    have H : PfHyp q Mb m B (fun s => W s ω) := ⟨hq, hm, hB, hn.cont ω, hn.zero ω⟩
    simp [flowMap, pf_Z_zero H, pf_ou_zero (w := fun s => W s ω) (hn.zero ω)]
  simp [sg, hflow]

/-- `P_s L g = L P_s g` for `g ∈ C²` with bounded derivatives: from the Markov property and the
Kolmogorov equation. -/
theorem inv_commute [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ}
    (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d} (hB : HasCbBound m Mb B)
    {g : Euc d → ℝ} (hg : ContDiff ℝ 2 g) {M : ℝ}
    (hM : ∀ i ≤ 2, ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ M) {T : ℝ} (hT : 0 ≤ T)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (x : Euc d) :
    sg P W q B s (kolmL q B g) x = kolmL q B (sg P W q B s g) x := by
  have hn := sgNoise_of_brownian hW
  have hM1 : ∀ y, ‖fderiv ℝ g y‖ ≤ M := fun y => by
    rw [← norm_iteratedFDeriv_one]; exact hM 1 (by norm_num) y
  have hM2 : ∀ y, ‖iteratedFDeriv ℝ 2 g y‖ ≤ M := fun y => hM 2 le_rfl y
  have hM2' : ∀ y, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ M := fun y => by
    rw [kl_norm_fderiv_fderiv']; exact hM2 y
  obtain ⟨C, hC1, hC⟩ := sg_contDiff (d := d) q Mb hq m hm T hT 2 hm
  obtain ⟨hu, -, hub⟩ := hC P W hn B hB g (by exact_mod_cast hg) M hM s hs
  have hu2 : ContDiff ℝ 2 (sg P W q B s g) := by exact_mod_cast hu
  have hub1 : ∀ y, ‖fderiv ℝ (sg P W q B s g) y‖ ≤ C * M := fun y => by
    rw [← norm_iteratedFDeriv_one]; exact hub 1 (by norm_num) y
  have hub2 : ∀ y, ‖iteratedFDeriv ℝ 2 (sg P W q B s g) y‖ ≤ C * M := fun y => hub 2 le_rfl y
  have hD1 := (pois_kolmogorov hq hm hB hW hg hM1 hM2).2.1 x s hs.1
  have hD2 := (pois_kolmogorov hq hm hB hW hu2 hub1 hub2).2.1 x 0 le_rfl
  rw [inv_sg_zero hW hq.le (by omega) hB] at hD2
  have hcomp : HasDerivWithinAt (fun r : ℝ => sg P W q B (r + s) g x)
      (sg P W q B s (kolmL q B g) x) (Ici 0) 0 := by
    have h1 : HasDerivWithinAt (fun r : ℝ => r + s) 1 (Ici (0 : ℝ)) 0 :=
      (hasDerivWithinAt_id 0 _).add_const s
    have h2 : HasDerivWithinAt (fun r => sg P W q B r g x) (sg P W q B s (kolmL q B g) x)
        (Ici 0) (0 + s) := by simpa using hD1
    have := h2.scomp (0 : ℝ) h1 (fun r hr => by
      show r + s ∈ Ici (0 : ℝ)
      exact add_nonneg hr hs.1)
    simpa [Function.comp_def] using this
  have hD3 : HasDerivWithinAt (fun r : ℝ => sg P W q B r (sg P W q B s g) x)
      (sg P W q B s (kolmL q B g) x) (Ici 0) 0 := by
    refine hcomp.congr (fun r hr => ?_) ?_
    · have hr0 : 0 ≤ r := hr
      rw [sg_markov_C2 hW hq.le (by omega) hB hg hM hr0 hs.1 x]
    · rw [sg_markov_C2 hW hq.le (by omega) hB hg hM le_rfl hs.1 x]
  exact (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ hD3 hD2


set_option maxHeartbeats 1000000 in
/-- **POIS-INV, semigroup invariance (bounded data).**  If `μ` is an infinitesimally invariant
probability measure of `Δ + b·∇` with finite second moment and `g ∈ C²` has bounded `g, Dg, D²g`,
then `∫ P_t g dμ = ∫ g dμ` for all `t ≥ 0`. -/
theorem inv_semigroup_bdd {q Mb : ℝ} (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d}
    (hB : HasCbBound m Mb B) [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    {μ : Measure (Euc d)} (hμ : IsInvariantMeasure (fun x => -q • x + B x) μ)
    (hμ2 : Integrable (fun x : Euc d => ‖x‖ ^ 2) μ) {g : Euc d → ℝ} (hg : ContDiff ℝ 2 g) {M : ℝ}
    (hM : ∀ i ≤ 2, ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    ∫ x, sg P W q B t g x ∂μ = ∫ x, g x ∂μ := by
  have : IsProbabilityMeasure μ := hμ.1
  have hn := sgNoise_of_brownian hW
  have hBc : Continuous B := hB.1.continuous
  have hBb : ∀ y, ‖B y‖ ≤ Mb := fun y => by simpa using hB.2 0 (Nat.zero_le _) y
  have hM1 : ∀ y, ‖fderiv ℝ g y‖ ≤ M := fun y => by
    rw [← norm_iteratedFDeriv_one]; exact hM 1 (by norm_num) y
  have hM2' : ∀ y, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ M := fun y => by
    rw [kl_norm_fderiv_fderiv']; exact hM 2 le_rfl y
  obtain ⟨C, hC1, hC⟩ := sg_contDiff (d := d) q Mb hq m hm t ht 2 hm
  -- the semigroup images are `C²` with bounded derivatives, uniformly in `s ∈ [0,t]`
  have hspec : ∀ s ∈ Icc (0 : ℝ) t, ContDiff ℝ 2 (sg P W q B s g) ∧
      (∀ y, ‖fderiv ℝ (sg P W q B s g) y‖ ≤ C * M) ∧
      (∀ y, ‖fderiv ℝ (fderiv ℝ (sg P W q B s g)) y‖ ≤ C * M) ∧
      (∀ y, ‖sg P W q B s g y‖ ≤ C * M) := fun s hs => by
    obtain ⟨hu, -, hub⟩ := hC P W hn B hB g (by exact_mod_cast hg) M hM s hs
    refine ⟨by exact_mod_cast hu, fun y => ?_, fun y => ?_, fun y => ?_⟩
    · rw [← norm_iteratedFDeriv_one]; exact hub 1 (by norm_num) y
    · rw [kl_norm_fderiv_fderiv']; exact hub 2 le_rfl y
    · have := hub 0 (by norm_num) y
      rwa [norm_iteratedFDeriv_zero] at this
  -- `∫ L (P_s g) dμ = 0`
  have hgen : ∀ s ∈ Icc (0 : ℝ) t, ∫ x, kolmL q B (sg P W q B s g) x ∂μ = 0 := fun s hs =>
    (inv_generator hBc hBb hμ hμ2 (hspec s hs).1 (hspec s hs).2.1 (hspec s hs).2.2.1).2
  -- joint continuity of `(s, x) ↦ P_s (L g) x`
  obtain ⟨a, ha, hga⟩ := kl_L_growth' (q := q) hBb hM1 hM2'
  have hcont := kl_cont_integral hq hm hB hW ht (kl_L_continuous q hBc hg) ha hga
  obtain ⟨F, hF⟩ : ∃ F : ℝ → Euc d → ℝ,
      ∀ s x, F s x = sg P W q B (clampT t s) (kolmL q B g) x := ⟨_, fun _ _ => rfl⟩
  have hFc : Continuous (fun p : ℝ × Euc d => F p.1 p.2) := by
    have h1 : Continuous (fun p : ℝ × Euc d => (clampT t p.1, p.2)) :=
      ((continuous_clampT t).comp continuous_fst).prodMk continuous_snd
    have h3 := hcont.comp_continuous h1 (fun p => ⟨clampT_mem ht p.1, mem_univ _⟩)
    simp_rw [hF]
    exact h3
  have hFeq : ∀ s x, F s x = kolmL q B (sg P W q B (clampT t s) g) x := fun s x => by
    rw [hF]
    exact inv_commute hW hq hm hB hg hM ht (clampT_mem ht s) x
  set A : ℝ := ((d * (C * M) + (C * M) * Mb) + (C * M) * |q|) with hA
  have hFb : ∀ s x, |F s x| ≤ A * (1 + ‖x‖) := fun s x => by
    rw [hFeq]
    exact inv_growth q hBb (hspec _ (clampT_mem ht s)).2.1 (hspec _ (clampT_mem ht s)).2.2.1 x
  have hAint : Integrable (fun x : Euc d => A * (1 + ‖x‖)) μ :=
    ((integrable_const (1 : ℝ)).add (inv_integrable_norm hμ2)).const_mul A
  have hmeas : Measurable (fun p : Euc d × ℝ => F p.2 p.1) := hFc.measurable.comp measurable_swap
  set ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) t) with hν
  have hint : Integrable (Function.uncurry fun (x : Euc d) (s : ℝ) => F s x) (μ.prod ν) := by
    have hb : Integrable (fun p : Euc d × ℝ => (A * (1 + ‖p.1‖)) * (1 : ℝ)) (μ.prod ν) :=
      Integrable.mul_prod (f := fun x : Euc d => A * (1 + ‖x‖)) (g := fun _ : ℝ => (1 : ℝ))
        hAint (integrable_const 1)
    refine hb.mono' hmeas.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, mul_one]
    exact hFb p.2 p.1
  have hswap := integral_integral_swap hint
  have hzero : ∫ s, ∫ x, F s x ∂μ ∂ν = 0 := by
    refine integral_eq_zero_of_ae ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun s hs => ?_)
    have hs' : s ∈ Icc (0 : ℝ) t := ⟨hs.1.le, hs.2⟩
    have : ∀ x, F s x = kolmL q B (sg P W q B s g) x := fun x => by
      rw [hFeq, clampT_of_mem hs']
    simp_rw [this]
    exact hgen s hs'
  -- the pointwise Kolmogorov identity
  have hkol := (pois_kolmogorov hq hm hB hW hg hM1 (fun y => by simpa using hM 2 le_rfl y)).1
  have hpt : ∀ x, sg P W q B t g x - g x = ∫ s, F s x ∂ν := fun x => by
    have h1 := hkol t ht x
    have h2 : ∫ s in (0 : ℝ)..t, sg P W q B s (kolmL q B g) x = ∫ s, F s x ∂ν := by
      rw [intervalIntegral.integral_of_le ht]
      refine setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
      have hs' : s ∈ Icc (0 : ℝ) t := ⟨hs.1.le, hs.2⟩
      simp only [hF, clampT_of_mem hs']
    rw [h1, h2]; ring
  have hcg : Continuous g := hg.continuous
  have hcs : Continuous (sg P W q B t g) := (hspec t ⟨ht, le_rfl⟩).1.continuous
  have hig : Integrable g μ := (integrable_const M).mono' hcg.aestronglyMeasurable (ae_of_all _ fun y => by
    have := hM 0 (by norm_num) y
    rwa [norm_iteratedFDeriv_zero] at this)
  have his : Integrable (sg P W q B t g) μ := (integrable_const (C * M)).mono' hcs.aestronglyMeasurable
    (ae_of_all _ fun y => (hspec t ⟨ht, le_rfl⟩).2.2.2 y)
  have : ∫ x, sg P W q B t g x ∂μ - ∫ x, g x ∂μ = 0 := by
    rw [← integral_sub his hig]
    simp_rw [hpt]
    rw [hswap]
    exact hzero
  linarith


theorem inv_flow_measurable [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ}
    (hq : 0 ≤ q) {m : ℕ} (hm : 1 ≤ m) {B : Euc d → Euc d} (hB : HasCbBound m Mb B) {t : ℝ}
    (ht : 0 ≤ t) (x : Euc d) : Measurable (fun ω => flowMap q B (fun s => W s ω) t x) := by
  have hn := sgNoise_of_brownian hW
  have h1 : Measurable (fun p : Ω × Euc d => flowMap q B (fun s => W s p.1) t p.2) :=
    sg_measurable_flowMap hn hq hm hB ht
  have h2 : Measurable (fun ω : Ω => (ω, x)) := measurable_id.prodMk measurable_const
  have h3 := h1.comp h2
  exact h3

/-- Growth of `P_t h` for `h` of linear growth, from the second moment of the flow. -/
theorem inv_sg_bound [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {q Mb : ℝ}
    (hq : 0 ≤ q) {m : ℕ} (hm : 1 ≤ m) {B : Euc d → Euc d} (hB : HasCbBound m Mb B) {t : ℝ}
    (ht : 0 ≤ t) {C : ℝ}
    (hmom : ∀ x : Euc d, Integrable (fun ω => ‖flowMap q B (fun s => W s ω) t x‖ ^ 2) P ∧
      ∫ ω, ‖flowMap q B (fun s => W s ω) t x‖ ^ 2 ∂P ≤ C * (1 + ‖x‖ ^ 2))
    {h : Euc d → ℝ} (hh : Continuous h) {a a' : ℝ} (ha' : 0 ≤ a') (hga : ∀ y, |h y| ≤ a + a' * ‖y‖)
    (x : Euc d) :
    Integrable (fun ω => h (flowMap q B (fun s => W s ω) t x)) P ∧
      |sg P W q B t h x| ≤ a + a' * (1 + C * (1 + ‖x‖ ^ 2)) := by
  have hX := inv_flow_measurable hW hq hm hB ht x
  have hint := kl_integrable_lin P hh.measurable ha' hga hX (hmom x).1
  refine ⟨hint, ?_⟩
  have h1 : |sg P W q B t h x| ≤ ∫ ω, |h (flowMap q B (fun s => W s ω) t x)| ∂P := by
    have := norm_integral_le_integral_norm (μ := P)
      (fun ω => h (flowMap q B (fun s => W s ω) t x))
    simpa [sg] using this
  refine h1.trans ?_
  have hI : Integrable (fun ω => 1 + ‖flowMap q B (fun s => W s ω) t x‖ ^ 2) P :=
    (integrable_const (1 : ℝ)).add (hmom x).1
  have h2 : ∫ ω, |h (flowMap q B (fun s => W s ω) t x)| ∂P ≤
      ∫ ω, (a + a' * (1 + ‖flowMap q B (fun s => W s ω) t x‖ ^ 2)) ∂P :=
    integral_mono hint.abs ((integrable_const a).add (hI.const_mul a'))
      (fun ω => kl_lin_to_quad ha' hga _)
  refine h2.trans ?_
  have h3 : ∫ ω, (1 + ‖flowMap q B (fun s => W s ω) t x‖ ^ 2) ∂P =
      1 + ∫ ω, ‖flowMap q B (fun s => W s ω) t x‖ ^ 2 ∂P := by
    rw [integral_add (integrable_const (1 : ℝ)) (hmom x).1]
    simp
  have h4 : ∫ ω, (a + a' * (1 + ‖flowMap q B (fun s => W s ω) t x‖ ^ 2)) ∂P =
      a + a' * ∫ ω, (1 + ‖flowMap q B (fun s => W s ω) t x‖ ^ 2) ∂P := by
    rw [integral_add (integrable_const a) (hI.const_mul a'), integral_const_mul]
    simp
  rw [h4, h3]
  have := (hmom x).2
  nlinarith


set_option maxHeartbeats 1000000 in
/-- **POIS-INV, semigroup invariance.**  For `μ` as in `inv_semigroup_bdd` (finite second moment)
and `g ∈ C²` with bounded `Dg`, `D²g` (`g` may grow linearly): `g` and `P_t g` are `μ`-integrable
and `∫ P_t g dμ = ∫ g dμ` for `t ≥ 0`.  Proved by approximating `g` by the compactly supported
`φ(x/R) g` and passing to the limit `R → ∞` on both sides. -/
theorem inv_semigroup {q Mb : ℝ} (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d}
    (hB : HasCbBound m Mb B) [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    {μ : Measure (Euc d)} (hμ : IsInvariantMeasure (fun x => -q • x + B x) μ)
    (hμ2 : Integrable (fun x : Euc d => ‖x‖ ^ 2) μ) {g : Euc d → ℝ} (hg : ContDiff ℝ 2 g)
    {M1 M2 : ℝ} (hM1 : ∀ y, ‖fderiv ℝ g y‖ ≤ M1) (hM2 : ∀ y, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ M2)
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable g μ ∧ Integrable (sg P W q B t g) μ ∧
      ∫ x, sg P W q B t g x ∂μ = ∫ x, g x ∂μ := by
  have : IsProbabilityMeasure μ := hμ.1
  have hn := sgNoise_of_brownian hW
  obtain ⟨M1', M2', hbnd⟩ := inv_cut_bounds hg hM1 hM2
  have hM10 : 0 ≤ M1 := by
    have := hM1 0; have := norm_nonneg (fderiv ℝ g 0); linarith
  obtain ⟨a, ha, hga⟩ : ∃ a : ℝ, 0 ≤ a ∧ ∀ y, |g y| ≤ a + M1 * ‖y‖ :=
    ⟨|g 0|, abs_nonneg _, fun y => kl_abs_le_lin hg hM1 y⟩
  obtain ⟨fR, hfR⟩ : ∃ fR : ℕ → Euc d → ℝ,
      ∀ n y, fR n y = invCutR ((n : ℝ) + 1) y * g y := ⟨fun n y => _, fun _ _ => rfl⟩
  have heq : ∀ n, fR n = fun y => invCutR ((n : ℝ) + 1) y * g y := fun n => funext (hfR n)
  have hR1 : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n => by
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hf2 : ∀ n, ContDiff ℝ 2 (fR n) := fun n => by
    rw [heq n]; exact ((inv_cutR_contDiff _).of_le (by norm_num)).mul hg
  have hfc : ∀ n, HasCompactSupport (fR n) := fun n => by
    rw [heq n]; exact (inv_cutR_compact (by positivity)).mul_right
  have hfga : ∀ n y, |fR n y| ≤ a + M1 * ‖y‖ := fun n y => by
    rw [hfR, abs_mul, abs_of_nonneg (inv_cutR_nonneg _ _)]
    refine le_trans ?_ (hga y)
    exact mul_le_of_le_one_left (abs_nonneg _) (inv_cutR_le_one _ _)
  have hbdn : ∀ n, ∃ M : ℝ, ∀ i ≤ 2, ∀ y, ‖iteratedFDeriv ℝ i (fR n) y‖ ≤ M := fun n => by
    obtain ⟨S0, -, hS0⟩ := inv_bdd (hf2 n).continuous (hfc n)
    refine ⟨max S0 (max M1' M2'), fun i hi y => ?_⟩
    interval_cases i
    · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]; exact (hS0 y).trans (le_max_left _ _)
    · rw [norm_iteratedFDeriv_one]
      have := (hbnd _ (hR1 n)).1 y
      rw [← heq n] at this
      exact this.trans ((le_max_left _ _).trans (le_max_right _ _) |>.trans le_rfl)
    · rw [← kl_norm_fderiv_fderiv']
      have := (hbnd _ (hR1 n)).2 y
      rw [← heq n] at this
      exact this.trans ((le_max_right _ _).trans (le_max_right _ _) |>.trans le_rfl)
  have hident : ∀ n, ∫ x, sg P W q B t (fR n) x ∂μ = ∫ x, fR n x ∂μ := fun n => by
    obtain ⟨M, hM⟩ := hbdn n
    exact inv_semigroup_bdd hq hm hB hW hμ hμ2 (hf2 n) hM ht
  have hAle : ∀ y : Euc d, a + M1 * ‖y‖ ≤ (a + M1) * (1 + ‖y‖) := fun y => by
    nlinarith [norm_nonneg y]
  have hig : Integrable g μ := inv_integrable_lin hμ2 hg.continuous (A := a + M1)
    (fun y => (hga y).trans (hAle y))
  obtain ⟨C, hC0, hCm⟩ := sg_second_moment (d := d) q Mb hq t ht
  have hmom := fun x => hCm P ℱ W hW m (by omega) B hB t ⟨ht, le_rfl⟩ x
  have hI2 : Integrable (fun x : Euc d => 1 + ‖x‖ ^ 2) μ := (integrable_const (1 : ℝ)).add hμ2
  have hbdint : Integrable (fun x : Euc d => a + M1 * (1 + C * (1 + ‖x‖ ^ 2))) μ :=
    (integrable_const a).add (((integrable_const (1 : ℝ)).add (hI2.const_mul C)).const_mul M1)
  -- continuity of `P_t f_n`
  obtain ⟨C2, -, hC2⟩ := sg_contDiff (d := d) q Mb hq m hm t ht 2 hm
  have hcs : ∀ n, Continuous (sg P W q B t (fR n)) := fun n => by
    obtain ⟨M, hM⟩ := hbdn n
    have := (hC2 P W hn B hB (fR n) (by exact_mod_cast hf2 n) M hM t ⟨ht, le_rfl⟩).1
    exact (by exact_mod_cast this : ContDiff ℝ 2 (sg P W q B t (fR n))).continuous
  have hlimx : ∀ x, Tendsto (fun n : ℕ => sg P W q B t (fR n) x) atTop (𝓝 (sg P W q B t g x)) := by
    intro x
    have hX := inv_flow_measurable hW hq.le (by omega : 1 ≤ m) hB ht x
    have hint := (inv_sg_bound hW hq.le (by omega : 1 ≤ m) hB ht (hmom) hg.continuous hM10 hga x).1
    have := tendsto_integral_of_dominated_convergence (μ := P)
      (fun ω => ‖g (flowMap q B (fun s => W s ω) t x)‖)
      (F := fun n ω => fR n (flowMap q B (fun s => W s ω) t x))
      (f := fun ω => g (flowMap q B (fun s => W s ω) t x))
      (fun n => ((hf2 n).continuous.measurable.comp hX).aestronglyMeasurable) hint.norm
      (fun n => Eventually.of_forall fun ω => by
        rw [hfR, norm_mul, Real.norm_eq_abs (invCutR _ _), abs_of_nonneg (inv_cutR_nonneg _ _)]
        exact mul_le_of_le_one_left (norm_nonneg _) (inv_cutR_le_one _ _))
      (Eventually.of_forall fun ω => by
        obtain ⟨N, hN⟩ := exists_nat_gt ‖flowMap q B (fun s => W s ω) t x‖
        refine (tendsto_const_nhds (x := g (flowMap q B (fun s => W s ω) t x))).congr' ?_
        refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
        have hxn : ‖flowMap q B (fun s => W s ω) t x‖ ≤ (n : ℝ) + 1 := by
          have : (N : ℝ) ≤ n := by exact_mod_cast hn
          linarith
        dsimp only
        rw [hfR, inv_cutR_one (by positivity : (0 : ℝ) < (n : ℝ) + 1) hxn, one_mul])
    exact this
  have hmeas : AEStronglyMeasurable (sg P W q B t g) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hcs n).aestronglyMeasurable)
      (ae_of_all _ hlimx)
  have hsgb : ∀ x, |sg P W q B t g x| ≤ a + M1 * (1 + C * (1 + ‖x‖ ^ 2)) := fun x =>
    (inv_sg_bound hW hq.le (by omega : 1 ≤ m) hB ht hmom hg.continuous hM10 hga x).2
  have hsgbn : ∀ n x, |sg P W q B t (fR n) x| ≤ a + M1 * (1 + C * (1 + ‖x‖ ^ 2)) := fun n x =>
    (inv_sg_bound hW hq.le (by omega : 1 ≤ m) hB ht hmom (hf2 n).continuous hM10 (hfga n) x).2
  have his : Integrable (sg P W q B t g) μ := hbdint.mono' hmeas
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hsgb x)
  refine ⟨hig, his, ?_⟩
  have hL1 := tendsto_integral_of_dominated_convergence (μ := μ)
    (fun x : Euc d => a + M1 * (1 + C * (1 + ‖x‖ ^ 2)))
    (F := fun n x => sg P W q B t (fR n) x) (f := sg P W q B t g)
    (fun n => (hcs n).aestronglyMeasurable) hbdint
    (fun n => ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hsgbn n x)
    (ae_of_all _ hlimx)
  have hL2 := tendsto_integral_of_dominated_convergence (μ := μ)
    (fun x : Euc d => (a + M1) * (1 + ‖x‖))
    (F := fun n x => fR n x) (f := g)
    (fun n => (hf2 n).continuous.aestronglyMeasurable)
    (((integrable_const (1 : ℝ)).add (inv_integrable_norm hμ2)).const_mul (a + M1))
    (fun n => ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact (hfga n x).trans (hAle x))
    (ae_of_all _ fun x => by
      obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
      refine (tendsto_const_nhds (x := g x)).congr' ?_
      refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
      have hxn : ‖x‖ ≤ (n : ℝ) + 1 := by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      dsimp only
      rw [hfR, inv_cutR_one (by positivity : (0 : ℝ) < (n : ℝ) + 1) hxn, one_mul])
  simp_rw [hident] at hL1
  exact tendsto_nhds_unique hL1 hL2


/-- **POIS-INV.**  Let `q > 0`, `B ∈ C_b^m` (`2 ≤ m`), `(Ω, P, ℱ, W)` a Brownian filtration, and `μ` an
invariant probability measure of `Δ + b·∇`, `b x = -q x + B x` (`IsInvariantMeasure`), with finite
second moment.  Then for every `g ∈ C²` with bounded `Dg`, `D²g`:
`L g` is `μ`-integrable with `∫ L g dμ = 0`, and for every `t ≥ 0`, `g` and `P_t g` are
`μ`-integrable with `∫ P_t g dμ = ∫ g dμ`. -/
theorem pois_inv {q Mb : ℝ} (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d}
    (hB : HasCbBound m Mb B) [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    {μ : Measure (Euc d)} (hμ : IsInvariantMeasure (fun x => -q • x + B x) μ)
    (hμ2 : Integrable (fun x : Euc d => ‖x‖ ^ 2) μ) {g : Euc d → ℝ} (hg : ContDiff ℝ 2 g)
    {M1 M2 : ℝ} (hM1 : ∀ y, ‖fderiv ℝ g y‖ ≤ M1) (hM2 : ∀ y, ‖iteratedFDeriv ℝ 2 g y‖ ≤ M2) :
    (Integrable (kolmL q B g) μ ∧ ∫ x, kolmL q B g x ∂μ = 0) ∧
      ∀ t : ℝ, 0 ≤ t → Integrable g μ ∧ Integrable (sg P W q B t g) μ ∧
        ∫ x, sg P W q B t g x ∂μ = ∫ x, g x ∂μ := by
  have hM2' : ∀ y, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ M2 := fun y => by
    rw [kl_norm_fderiv_fderiv']; exact hM2 y
  have hBb : ∀ y, ‖B y‖ ≤ Mb := fun y => by simpa using hB.2 0 (Nat.zero_le _) y
  exact ⟨inv_generator hB.1.continuous hBb hμ hμ2 hg hM1 hM2',
    fun t ht => inv_semigroup hq hm hB hW hμ hμ2 hg hM1 hM2' ht⟩

end HRS.MS.PoisInv
