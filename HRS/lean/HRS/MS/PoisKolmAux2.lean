import HRS.MS.PoisKolmAux1
import HRS.MS.PoisMarkovAux2
import HRS.MC.CepH2Sde2

/-!
# POIS-KOLM: the Kolmogorov backward equation for `sg`

Supplement foundation packet POIS-KOLM.  Setting: a Brownian filtration `IsBrownianFiltration P ℱ W`,
`q > 0`, `B` with `HasCbBound m Mb B` (`2 ≤ m`), the semigroup `sg P W q B t h x = E h(X^x_t)` of
`dX = (-q X + B X) dt + √2 dW` (`PoisSgAux2`), and the generator
`L h = Δh + b·∇h`, `b x = -q x + B x` (`kolmL`, with Mathlib's `Laplacian.laplacian` and `gradient`,
as in `poissonOp` of `HRS/Whole/Thermal.lean`).

Main theorem `HRS.MS.PoisKolm.pois_kolmogorov`.  For `h ∈ C²(ℝ^d)` with bounded `Dh`, `D²h`
(`h` itself may be unbounded):
* `sg t h x = h x + ∫_0^t sg s (L h) x ds` for `t ≥ 0` (integrated Kolmogorov identity);
* `s ↦ sg s h x` has right derivative `sg t (L h) x` at every `t ≥ 0` and derivative at `t > 0`;
* `(t, x) ↦ sg t h x` is `C^{1,2}` on `[0,T] × ℝ^d` for every `T > 0` in the sense of `IsC12On`
  (jointly continuous `u, Du, D²u, ∂_t u`).

Route.  The Itô formula (`ito_formula_additive_time_independent`, packaged for `C²` functions with
bounded gradient as `HRS.MC.CepH2.h2_dynkin`) is applied to `h(X_t)` with the noise
`σ_k = √2 e_k` (`pfSigma`): the drift is `Dh(b) + ½ ∑_k D²h(σ_k,σ_k) = L h` (`kl_drift_eq`) and the
martingale remainder is the `L²` Itô integral of the bounded integrand `Dh(X_s) σ_k`
(`isProgressiveL2_itoIntegrand`, `integral_itoIntegral`), hence integrable with mean `0`.  Taking
expectations and using Fubini (second moments of the flow, `sg_second_moment`, give integrability
of `L h(X_s)`) yields the integrated identity; `s ↦ sg s (L h) x` is continuous (truncation argument
`kl_tendsto_integral_lin`), which gives the derivative.  The joint regularity in `(t, x)` comes from
the pathwise variational equations of `PoisKolmAux1` (time-Lipschitz continuity of `Dφ_t`, `D²φ_t`
uniformly in `x`) and differentiation under the expectation (`kl_sg_deriv`).

Statement adjustments relative to the packet sketch: `IsC12On` is stated for `T > 0` (for `T = 0`
the `derivWithin` on the singleton `{0}` is a junk value); `sg` for negative times is not used.
`‖D²h‖` is bounded through `iteratedFDeriv ℝ 2 h`.  The identity `P_t L h = L P_t h` (needs the Markov
property, `sg_markov`, and bounded `h`) is not part of this file.  Helper lemmas carry the prefix `kl_`.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Interval
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.PoisFlow HRS.MS.PoisSg
  HRS.MS.PoisMarkov

noncomputable section

set_option synthInstance.maxHeartbeats 200000

namespace HRS.MS.PoisKolm

variable {d : ℕ}

/-- The generator `L h = Δh + b·∇h` with `b x = -q x + B x`. -/
def kolmL (q : ℝ) (B : Euc d → Euc d) (h : Euc d → ℝ) (x : Euc d) : ℝ :=
  Laplacian.laplacian h x + inner ℝ (-q • x + B x) (gradient h x)

theorem kl_inner_gradient (h : Euc d → ℝ) (x v : Euc d) :
    inner ℝ v (gradient h x) = fderiv ℝ h x v := by
  rw [real_inner_comm]
  unfold gradient
  exact InnerProductSpace.toDual_symm_apply

theorem kl_laplacian_eq (h : Euc d → ℝ) (y : Euc d) :
    Laplacian.laplacian h y =
      ∑ i : Fin d, fderiv ℝ (fderiv ℝ h) y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
  have := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (f := h)
    (EuclideanSpace.basisFun (Fin d) ℝ)) y
  rw [this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp [EuclideanSpace.basisFun_apply]

theorem kl_L_eq (q : ℝ) (B : Euc d → Euc d) (h : Euc d → ℝ) (y : Euc d) :
    kolmL q B h y = (∑ i : Fin d, fderiv ℝ (fderiv ℝ h) y (EuclideanSpace.single i 1)
      (EuclideanSpace.single i 1)) + fderiv ℝ h y (-q • y + B y) := by
  unfold kolmL
  rw [kl_laplacian_eq, kl_inner_gradient]

theorem kl_drift_eq (q : ℝ) (B : Euc d → Euc d) (h : Euc d → ℝ) (y : Euc d) :
    fderiv ℝ h y (-q • y + B y) + (1 / 2) * ∑ k, fderiv ℝ (fderiv ℝ h) y (pfSigma d k) (pfSigma d k) =
      kolmL q B h y := by
  rw [kl_L_eq, add_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [pfSigma, map_smul, smul_apply, smul_eq_mul]
  have : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  calc _ = (1 / 2 * (Real.sqrt 2 * Real.sqrt 2)) * fderiv ℝ (fderiv ℝ h) y
        (EuclideanSpace.single k 1) (EuclideanSpace.single k 1) := by ring
    _ = _ := by rw [this]; ring

/-! ### Growth and continuity of the generator image -/

theorem kl_L_continuous (q : ℝ) {B : Euc d → Euc d} (hB : Continuous B) {h : Euc d → ℝ}
    (hh : ContDiff ℝ 2 h) : Continuous (kolmL q B h) := by
  have e : kolmL q B h = fun y => (∑ i : Fin d, fderiv ℝ (fderiv ℝ h) y (EuclideanSpace.single i 1)
      (EuclideanSpace.single i 1)) + fderiv ℝ h y (-q • y + B y) := funext (kl_L_eq q B h)
  rw [e]
  have h1 : Continuous (fderiv ℝ h) := hh.continuous_fderiv (by norm_num)
  have h2 : Continuous (fderiv ℝ (fderiv ℝ h)) :=
    (hh.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  refine (continuous_finsetSum _ fun i _ => ?_).add (h1.clm_apply ?_)
  · exact (h2.clm_apply continuous_const).clm_apply continuous_const
  · exact (continuous_id.const_smul (-q)).add hB

theorem kl_L_growth (q : ℝ) {B : Euc d → Euc d} {Mb : ℝ} (hBb : ∀ y, ‖B y‖ ≤ Mb) {h : Euc d → ℝ}
    {M1 M2 : ℝ} (hM1 : ∀ y, ‖fderiv ℝ h y‖ ≤ M1) (hM2 : ∀ y, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ M2)
    (y : Euc d) : |kolmL q B h y| ≤ (d * M2 + M1 * Mb) + (M1 * |q|) * ‖y‖ := by
  rw [kl_L_eq]
  have h1 : |∑ i : Fin d, fderiv ℝ (fderiv ℝ h) y (EuclideanSpace.single i 1)
      (EuclideanSpace.single i 1)| ≤ d * M2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ i : Fin d, |fderiv ℝ (fderiv ℝ h) y (EuclideanSpace.single i 1)
        (EuclideanSpace.single i 1)| ≤ M2 := fun i => by
      rw [← Real.norm_eq_abs]
      refine (ContinuousLinearMap.le_opNorm₂ _ _ _).trans ?_
      simpa using hM2 y
    refine (Finset.sum_le_sum fun i _ => this i).trans ?_
    simp
  have h2 : |fderiv ℝ h y (-q • y + B y)| ≤ M1 * (|q| * ‖y‖ + Mb) := by
    rw [← Real.norm_eq_abs]
    refine ((fderiv ℝ h y).le_opNorm _).trans ?_
    have hb : ‖-q • y + B y‖ ≤ |q| * ‖y‖ + Mb := by
      refine (norm_add_le _ _).trans (add_le_add ?_ (hBb y))
      rw [norm_smul, norm_neg, Real.norm_eq_abs]
    have hM1' := hM1 y
    exact mul_le_mul hM1' hb (norm_nonneg _) ((norm_nonneg _).trans hM1')
  calc _ ≤ |∑ i : Fin d, fderiv ℝ (fderiv ℝ h) y (EuclideanSpace.single i 1)
          (EuclideanSpace.single i 1)| + |fderiv ℝ h y (-q • y + B y)| := abs_add_le _ _
    _ ≤ d * M2 + M1 * (|q| * ‖y‖ + Mb) := add_le_add h1 h2
    _ = _ := by ring

/-! ### Integrals of functions of linear growth -/

theorem kl_integrable_lin {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {g : Euc d → ℝ} (hg : Measurable g) {a a' : ℝ} (ha' : 0 ≤ a') (hga : ∀ y, |g y| ≤ a + a' * ‖y‖)
    {X : Ω → Euc d} (hX : Measurable X) (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) P) :
    Integrable (fun ω => g (X ω)) P := by
  refine Integrable.mono' (g := fun ω => a + a' * (1 + ‖X ω‖ ^ 2))
    ((integrable_const a).add ((integrable_const 1).add hX2 |>.const_mul a')) (hg.comp hX).aestronglyMeasurable
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  refine (hga _).trans ?_
  have : ‖X ω‖ ≤ 1 + ‖X ω‖ ^ 2 := by nlinarith [sq_nonneg (‖X ω‖ - 1), norm_nonneg (X ω)]
  nlinarith [mul_le_mul_of_nonneg_left this ha']

/-- Convergence of `∫ g(Y_n)` for continuous `g` of linear growth, `Y_n → Y_0` pointwise with
uniformly bounded second moments (truncation of `g`). -/
theorem kl_tendsto_integral_lin {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {g : Euc d → ℝ} (hg : Continuous g) {a : ℝ} (ha : 0 ≤ a)
    (hga : ∀ y, |g y| ≤ a * (1 + ‖y‖)) {Y : ℕ → Ω → Euc d} {Y0 : Ω → Euc d}
    (hY : ∀ n, Measurable (Y n)) (hY0 : Measurable Y0) {K : ℝ}
    (hKi : ∀ n, Integrable (fun ω => ‖Y n ω‖ ^ 2) P) (hK : ∀ n, ∫ ω, ‖Y n ω‖ ^ 2 ∂P ≤ K)
    (hKi0 : Integrable (fun ω => ‖Y0 ω‖ ^ 2) P) (hK0 : ∫ ω, ‖Y0 ω‖ ^ 2 ∂P ≤ K)
    (hconv : ∀ ω, Tendsto (fun n => Y n ω) atTop (𝓝 (Y0 ω))) :
    Tendsto (fun n => ∫ ω, g (Y n ω) ∂P) atTop (𝓝 (∫ ω, g (Y0 ω) ∂P)) := by
  have hK0' : 0 ≤ K := (integral_nonneg fun ω => by positivity).trans hK0
  have hga' : ∀ y, |g y| ≤ a + a * ‖y‖ := fun y => by have := hga y; linarith
  let θ : ℝ → Euc d → ℝ := fun R y => max 0 (min 1 (R + 1 - ‖y‖))
  have hθc : ∀ R, Continuous (θ R) := fun R =>
    continuous_const.max (continuous_const.min (continuous_const.sub continuous_norm))
  have hθ0 : ∀ R y, 0 ≤ θ R y := fun R y => le_max_left _ _
  have hθ1 : ∀ R y, θ R y ≤ 1 := fun R y => max_le zero_le_one (min_le_left _ _)
  have hθin : ∀ R y, ‖y‖ ≤ R → θ R y = 1 := fun R y hy => by
    simp only [θ]; rw [min_eq_left (by linarith)]; simp
  have hθout : ∀ R y, R + 1 ≤ ‖y‖ → θ R y = 0 := fun R y hy => by
    simp only [θ]; rw [min_eq_right (by linarith)]; simp; linarith
  -- the truncation estimates
  have hbd : ∀ R : ℝ, 0 ≤ R → ∀ y, |g y * θ R y| ≤ a * (R + 2) := by
    intro R hR y
    rw [abs_mul, abs_of_nonneg (hθ0 R y)]
    by_cases hy : ‖y‖ ≤ R + 1
    · calc |g y| * θ R y ≤ |g y| * 1 := mul_le_mul_of_nonneg_left (hθ1 R y) (abs_nonneg _)
        _ ≤ a * (1 + ‖y‖) := by rw [mul_one]; exact hga y
        _ ≤ a * (R + 2) := mul_le_mul_of_nonneg_left (by linarith) ha
    · rw [hθout R y (by linarith)]; simp; positivity
  have htail : ∀ R : ℝ, 1 ≤ R → ∀ y, |g y - g y * θ R y| ≤ (2 * a / R) * ‖y‖ ^ 2 := by
    intro R hR y
    have hR0 : 0 < R := by linarith
    by_cases hy : ‖y‖ ≤ R
    · rw [hθin R y hy]; simp; positivity
    · have hy := not_le.1 hy
      have : g y - g y * θ R y = g y * (1 - θ R y) := by ring
      rw [this, abs_mul, abs_of_nonneg (by linarith [hθ1 R y] : 0 ≤ 1 - θ R y)]
      calc |g y| * (1 - θ R y) ≤ |g y| * 1 :=
            mul_le_mul_of_nonneg_left (by linarith [hθ0 R y]) (abs_nonneg _)
        _ ≤ a * (1 + ‖y‖) := by rw [mul_one]; exact hga y
        _ ≤ a * (2 * ‖y‖) := mul_le_mul_of_nonneg_left (by linarith) ha
        _ ≤ (2 * a / R) * ‖y‖ ^ 2 := by
            rw [div_mul_eq_mul_div, le_div_iff₀ hR0]
            nlinarith [norm_nonneg y, mul_nonneg ha (norm_nonneg y)]
  -- integral estimates for a measurable `Z` with integrable square norm
  have hest : ∀ (R : ℝ), 1 ≤ R → ∀ Z : Ω → Euc d, Measurable Z →
      Integrable (fun ω => ‖Z ω‖ ^ 2) P → ∫ ω, ‖Z ω‖ ^ 2 ∂P ≤ K →
      |∫ ω, g (Z ω) ∂P - ∫ ω, g (Z ω) * θ R (Z ω) ∂P| ≤ 2 * a * K / R := by
    intro R hR Z hZ hZi hZK
    have hR0 : 0 < R := by linarith
    have i1 : Integrable (fun ω => g (Z ω)) P :=
      kl_integrable_lin P hg.measurable ha hga' hZ hZi
    have i2 : Integrable (fun ω => g (Z ω) * θ R (Z ω)) P :=
      Integrable.of_bound ((hg.mul (hθc R)).measurable.comp hZ).aestronglyMeasurable (a * (R + 2))
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hbd R (by linarith) _)
    rw [← integral_sub i1 i2]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ ω, |g (Z ω) - g (Z ω) * θ R (Z ω)| ∂P ≤ ∫ ω, (2 * a / R) * ‖Z ω‖ ^ 2 ∂P :=
          integral_mono_of_nonneg (Eventually.of_forall fun ω => abs_nonneg _) (hZi.const_mul _)
            (Eventually.of_forall fun ω => htail R hR _)
      _ = (2 * a / R) * ∫ ω, ‖Z ω‖ ^ 2 ∂P := integral_const_mul _ _
      _ ≤ (2 * a / R) * K := mul_le_mul_of_nonneg_left hZK (by positivity)
      _ = 2 * a * K / R := by ring
  rw [Metric.tendsto_atTop]
  intro ε hε
  set R : ℝ := max 1 (8 * a * K / ε + 1) with hRdef
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR0 : 0 < R := by linarith
  have hRε : 2 * a * K / R < ε / 4 := by
    rw [div_lt_iff₀ hR0]
    have h1 : 8 * a * K / ε + 1 ≤ R := le_max_right _ _
    have h2 : 8 * a * K / ε < R := by linarith
    rw [div_lt_iff₀ hε] at h2
    nlinarith
  -- dominated convergence for the truncated integrands
  have hdct : Tendsto (fun n => ∫ ω, g (Y n ω) * θ R (Y n ω) ∂P) atTop
      (𝓝 (∫ ω, g (Y0 ω) * θ R (Y0 ω) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => a * (R + 2))
      (fun n => ((hg.mul (hθc R)).measurable.comp (hY n)).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact hbd R (by linarith) _)
      (Eventually.of_forall fun ω => ((hg.mul (hθc R)).continuousAt.tendsto).comp (hconv ω))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hdct (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq]
  have e1 := hest R hR1 (Y n) (hY n) (hKi n) (hK n)
  have e0 := hest R hR1 Y0 hY0 hKi0 hK0
  have e2 := hN n hn
  rw [Real.dist_eq] at e2
  have : ∫ ω, g (Y n ω) ∂P - ∫ ω, g (Y0 ω) ∂P =
      (∫ ω, g (Y n ω) ∂P - ∫ ω, g (Y n ω) * θ R (Y n ω) ∂P) +
      ((∫ ω, g (Y n ω) * θ R (Y n ω) ∂P - ∫ ω, g (Y0 ω) * θ R (Y0 ω) ∂P) -
        (∫ ω, g (Y0 ω) ∂P - ∫ ω, g (Y0 ω) * θ R (Y0 ω) ∂P)) := by ring
  rw [this]
  calc _ ≤ |∫ ω, g (Y n ω) ∂P - ∫ ω, g (Y n ω) * θ R (Y n ω) ∂P| +
        |(∫ ω, g (Y n ω) * θ R (Y n ω) ∂P - ∫ ω, g (Y0 ω) * θ R (Y0 ω) ∂P) -
          (∫ ω, g (Y0 ω) ∂P - ∫ ω, g (Y0 ω) * θ R (Y0 ω) ∂P)| := abs_add_le _ _
    _ ≤ |∫ ω, g (Y n ω) ∂P - ∫ ω, g (Y n ω) * θ R (Y n ω) ∂P| +
        (|∫ ω, g (Y n ω) * θ R (Y n ω) ∂P - ∫ ω, g (Y0 ω) * θ R (Y0 ω) ∂P| +
          |∫ ω, g (Y0 ω) ∂P - ∫ ω, g (Y0 ω) * θ R (Y0 ω) ∂P|) :=
        add_le_add le_rfl (abs_sub _ _)
    _ < ε := by linarith

/-! ### The pathwise setting of the Brownian flow -/

section Flow

open HRS.MS.FlowB (clampT continuous_clampT clampT_mem clampT_of_mem)

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → Fin d → ℝ}

/-- Pathwise `KlPath` for every sample path, uniformly. -/
theorem kl_pathω {q Mb : ℝ} (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) {T : ℝ} (hT : 0 ≤ T)
    (hW : SgNoise W) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : Euc d → Euc d, HasCbBound m Mb B → ∀ ω : Ω,
      KlPath T (fun y => -q • y + B y) (fun t => ∑ k, W (Real.toNNReal t) ω k • pfSigma d k)
        (flowMap q B (fun s => W s ω)) C C (q + Mb) Mb := by
  obtain ⟨C, hC, hpath⟩ := kl_flow_path (d := d) q Mb hq m hm T hT
  exact ⟨C, hC, fun B hB ω => hpath B hB (fun s => W s ω) (hW.cont ω) (hW.zero ω)⟩

/-- Joint continuity of `(t, x) ↦ ∫ g(φ_t x) dP` for continuous `g` of linear growth. -/
theorem kl_cont_integral {q Mb : ℝ} (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d}
    (hB : HasCbBound m Mb B) [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {T : ℝ}
    (hT : 0 ≤ T) {g : Euc d → ℝ} (hg : Continuous g) {a : ℝ} (ha : 0 ≤ a)
    (hga : ∀ y, |g y| ≤ a * (1 + ‖y‖)) :
    ContinuousOn (fun p : ℝ × Euc d => sg P W q B p.1 g p.2) (Icc 0 T ×ˢ univ) := by
  have hm1 : 1 ≤ m := by omega
  have hn := sgNoise_of_brownian hW
  obtain ⟨Cm, hCm, hmom⟩ := sg_second_moment (d := d) q Mb hq T hT
  obtain ⟨C, hC, hpath⟩ := kl_pathω (q := q) (Mb := Mb) hq hm hT hn
  have hmom' := fun t ht x => hmom P ℱ W hW m hm1 B hB t ht x
  have hcont : Continuous (fun p : ℝ × Euc d => sg P W q B (clampT T p.1) g p.2) := by
    rw [continuous_iff_seqContinuous]
    intro u p0 hu
    have hu1 : Tendsto (fun n => (u n).1) atTop (𝓝 p0.1) := (continuous_fst.tendsto p0).comp hu
    have hu2 : Tendsto (fun n => (u n).2) atTop (𝓝 p0.2) := (continuous_snd.tendsto p0).comp hu
    obtain ⟨R, hR⟩ := (hu2.norm).bddAbove_range
    set R' : ℝ := max R ‖p0.2‖ with hR'
    have hRn : ∀ n, ‖(u n).2‖ ≤ R' := fun n => (hR ⟨n, rfl⟩).trans (le_max_left _ _)
    have hR0 : ‖p0.2‖ ≤ R' := le_max_right _ _
    set K : ℝ := Cm * (1 + R' ^ 2) with hK
    have hmeas : ∀ (t : ℝ) (x : Euc d), 0 ≤ t → Measurable (fun ω => flowMap q B (fun s => W s ω) t x) :=
      fun t x ht => by
        have h1 : Measurable (fun p : Ω × Euc d => flowMap q B (fun s => W s p.1) t p.2) :=
          sg_measurable_flowMap hn hq.le hm1 hB ht
        have h2 : Measurable (fun ω : Ω => (ω, x)) := measurable_id.prodMk measurable_const
        have h3 := h1.comp h2
        exact h3
    have hKn : ∀ (p : ℝ × Euc d), ‖p.2‖ ≤ R' →
        Integrable (fun ω => ‖flowMap q B (fun s => W s ω) (clampT T p.1) p.2‖ ^ 2) P ∧
        ∫ ω, ‖flowMap q B (fun s => W s ω) (clampT T p.1) p.2‖ ^ 2 ∂P ≤ K := fun p hp => by
      obtain ⟨i1, i2⟩ := hmom' _ (clampT_mem hT p.1) p.2
      refine ⟨i1, i2.trans ?_⟩
      have : ‖p.2‖ ^ 2 ≤ R' ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hp 2
      exact mul_le_mul_of_nonneg_left (by linarith) hCm.le
    have := kl_tendsto_integral_lin P hg ha hga
      (Y := fun n ω => flowMap q B (fun s => W s ω) (clampT T (u n).1) (u n).2)
      (Y0 := fun ω => flowMap q B (fun s => W s ω) (clampT T p0.1) p0.2)
      (fun n => hmeas _ _ (clampT_mem hT _).1) (hmeas _ _ (clampT_mem hT _).1) (K := K)
      (fun n => (hKn (u n) (hRn n)).1) (fun n => (hKn (u n) (hRn n)).2)
      (hKn p0 hR0).1 (hKn p0 hR0).2 (fun ω => ?_)
    · exact this
    · have hk := hpath B hB ω
      have h1 : Continuous (fun p : ℝ × Euc d => (clampT T p.1, p.2)) :=
        ((continuous_clampT T).comp continuous_fst).prodMk continuous_snd
      have h2 := (hk.cont_phi.comp_continuous h1 (fun p => ⟨clampT_mem hT p.1, mem_univ _⟩))
      exact (h2.tendsto p0).comp hu
  refine hcont.continuousOn.congr (fun p hp => ?_)
  simp only [clampT_of_mem hp.1]

end Flow

theorem kl_lin_to_quad {g : Euc d → ℝ} {a a' : ℝ} (ha' : 0 ≤ a') (hga : ∀ y, |g y| ≤ a + a' * ‖y‖)
    (y : Euc d) : |g y| ≤ a + a' * (1 + ‖y‖ ^ 2) := by
  refine (hga y).trans ?_
  have : ‖y‖ ≤ 1 + ‖y‖ ^ 2 := by nlinarith [sq_nonneg (‖y‖ - 1), norm_nonneg y]
  nlinarith [mul_le_mul_of_nonneg_left this ha']

theorem kl_abs_le_lin {h : Euc d → ℝ} (hh : ContDiff ℝ 2 h) {M1 : ℝ} (hM1 : ∀ y, ‖fderiv ℝ h y‖ ≤ M1)
    (y : Euc d) : |h y| ≤ |h 0| + M1 * ‖y‖ := by
  have hd : Differentiable ℝ h := hh.differentiable (by norm_num)
  have := (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le
    (f := h) (C := M1) (fun x _ => hd x) (fun x _ => hM1 x) (mem_univ 0) (mem_univ y)
  rw [sub_zero, Real.norm_eq_abs] at this
  calc |h y| = |h 0 + (h y - h 0)| := by ring_nf
    _ ≤ |h 0| + |h y - h 0| := abs_add_le _ _
    _ ≤ |h 0| + M1 * ‖y‖ := by
        gcongr


/-! ### The integrated Kolmogorov identity (Itô + Fubini) -/

section Ito

open HRS.MS.FlowB (clampT continuous_clampT clampT_mem clampT_of_mem)

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → Fin d → ℝ}

set_option maxHeartbeats 1000000 in
/-- **Integrated Kolmogorov identity.**  For `h ∈ C²` with bounded `Dh`, `D²h`:
`P_t h (x) = h(x) + ∫_0^t P_s (L h)(x) ds`. -/
theorem kl_integral_identity {q Mb : ℝ} (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d}
    (hB : HasCbBound m Mb B) [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    {h : Euc d → ℝ} (hh : ContDiff ℝ 2 h) {M1 M2 : ℝ} (hM1 : ∀ y, ‖fderiv ℝ h y‖ ≤ M1)
    (hM2 : ∀ y, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ M2) {t : ℝ} (ht : 0 ≤ t) (x : Euc d) :
    sg P W q B t h x = h x + ∫ s in (0 : ℝ)..t, sg P W q B s (kolmL q B h) x := by
  have hm1 : 1 ≤ m := by omega
  have hn := sgNoise_of_brownian hW
  have hBc : Continuous B := hB.1.continuous
  have hbc : Continuous (fun y : Euc d => -q • y + B y) := (continuous_id.const_smul (-q)).add hBc
  have hH : ∀ ω, PfHyp q Mb m B (fun s => W s ω) := fun ω =>
    ⟨hq.le, hm1, hB, hn.cont ω, hn.zero ω⟩
  have hps := fun ω => pf_flowMap_isPathSolution (hH ω) x
  set Z : ℝ → Ω → Euc d := fun s ω => flowMap q B (fun r => W r ω) (max s 0) x with hZdef
  have hZ0 : ∀ s : ℝ, Measurable[ℱ s] (Z 0) := by
    intro s
    have : Z 0 = fun _ => x := funext fun ω => by simpa [hZdef] using (hps ω).1
    rw [this]; exact measurable_const
  have hZad : ∀ s : ℝ, 0 ≤ s → Measurable[ℱ s] (Z s) := by
    intro s hs
    have := mk_measurable_V hW hq.le hm1 hB s.toNNReal x
    rw [Real.coe_toNNReal s hs] at this
    have e : Z s = fun ω => flowMap q B (fun u => W u ω) s x := by
      funext ω; simp [hZdef, max_eq_left hs]
    rw [e]; exact this
  have hZc : ∀ ω, Continuous fun s => Z s ω := by
    intro ω
    rw [continuous_iff_continuousAt]
    intro s
    set T : ℝ := max (s + 1) 1 with hT
    have hT0 : 0 ≤ T := by positivity
    have hco : ContinuousOn (fun r => flowMap q B (fun u => W u ω) (max r 0) x) (Iio T) := by
      refine ((hps ω).2 T hT0 (WithTop.coe_lt_top T)).1.comp (continuous_id.max continuous_const).continuousOn
        (fun r hr => ⟨le_max_right _ _, max_le (le_of_lt hr) hT0⟩)
    exact hco.continuousAt (Iio_mem_nhds (lt_max_of_lt_left (by linarith)))
  have hZeq : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → Z s ω = Z 0 ω + (∫ r in Icc (0 : ℝ) s,
      (fun y : Euc d => -q • y + B y) (Z r ω)) +
        ∑ k, (W (Real.toNNReal s) ω k - W 0 ω k) • pfSigma d k := by
    refine Eventually.of_forall fun ω s hs => ?_
    have h1 := ((hps ω).2 s hs (WithTop.coe_lt_top s)).2.2
    have h0 : Z 0 ω = x := by simpa [hZdef] using (hps ω).1
    have e1 : Z s ω = flowMap q B (fun r => W r ω) s x := by simp [hZdef, max_eq_left hs]
    have e2 : ∫ r in Icc (0 : ℝ) s, (fun y : Euc d => -q • y + B y) (Z r ω) =
        ∫ r in Icc (0 : ℝ) s, (fun _ y => -q • y + B y) r (flowMap q B (fun u => W u ω) r x) := by
      refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
      simp [hZdef, max_eq_left hr.1]
    rw [e1, e2, h0, hn.zero ω]
    simp only [Pi.zero_apply, sub_zero]
    exact h1
  obtain ⟨M, hMi, hM0, hMeq⟩ := HRS.MC.CepH2.h2_dynkin (P := P) (ℱ := ℱ) (N := d) hW
    (σ := pfSigma d) (B := fun y : Euc d => -q • y + B y) hbc hZ0 hZad hZc hZeq hh hM1 t ht

  have hBb : ∀ y, ‖B y‖ ≤ Mb := fun y => by simpa using hB.2 0 (Nat.zero_le _) y
  have hM10 : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0)
  have hA' : 0 ≤ M1 * |q| := mul_nonneg hM10 (abs_nonneg _)
  have hLg := kl_L_growth q hBb hM1 hM2
  have hLc : Continuous (kolmL q B h) := kl_L_continuous q hBc hh
  obtain ⟨Cm, hCm, hmom⟩ := sg_second_moment (d := d) q Mb hq t ht
  have hmom' := fun s hs y => hmom P ℱ W hW m hm1 B hB s hs y
  have hZm : ∀ s, Measurable (Z s) := fun s => by
    have h1 : Measurable (fun p : Ω × Euc d => flowMap q B (fun r => W r p.1) (max s 0) p.2) :=
      sg_measurable_flowMap hn hq.le hm1 hB (le_max_right _ _)
    have h2 : Measurable (fun ω : Ω => (ω, x)) := measurable_id.prodMk measurable_const
    have h3 := h1.comp h2
    exact h3
  have hZjoint : Measurable (fun p : ℝ × Ω => Z p.1 p.2) :=
    measurable_uncurry_of_continuous_of_measurable (u := Z) (fun ω => hZc ω) hZm
  have hZ2 : ∀ s ∈ Icc (0 : ℝ) t, Integrable (fun ω => ‖Z s ω‖ ^ 2) P ∧
      ∫ ω, ‖Z s ω‖ ^ 2 ∂P ≤ Cm * (1 + ‖x‖ ^ 2) := fun s hs => by
    simpa [hZdef, max_eq_left hs.1] using hmom' s hs x
  set f : ℝ → Ω → ℝ := fun s ω => kolmL q B h (Z s ω) with hf
  have hFm : Measurable (Function.uncurry f) := hLc.measurable.comp hZjoint
  set Kg : ℝ := (↑d * M2 + M1 * Mb) + (M1 * |q|) * (1 + Cm * (1 + ‖x‖ ^ 2)) with hKg
  have hfint : ∀ s ∈ Icc (0 : ℝ) t, Integrable (fun ω => f s ω) P := fun s hs =>
    kl_integrable_lin P hLc.measurable hA' hLg (hZm s) (hZ2 s hs).1
  have hFint : Integrable (Function.uncurry f) ((volume.restrict (Icc 0 t)).prod P) := by
    rw [integrable_prod_iff hFm.aestronglyMeasurable]
    refine ⟨(ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => hfint s hs), ?_⟩
    refine Integrable.mono' (integrable_const Kg) hFm.norm.aestronglyMeasurable.integral_prod_right' ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => ?_)
    have hnn : 0 ≤ ∫ ω, ‖Function.uncurry f (s, ω)‖ ∂P := integral_nonneg fun _ => norm_nonneg _
    rw [Real.norm_of_nonneg hnn]
    have hq2 := (hZ2 s hs)
    calc ∫ ω, ‖Function.uncurry f (s, ω)‖ ∂P
        ≤ ∫ ω, ((↑d * M2 + M1 * Mb) + (M1 * |q|) * (1 + ‖Z s ω‖ ^ 2)) ∂P :=
          integral_mono (hfint s hs).norm
            ((integrable_const _).add (((integrable_const (1 : ℝ)).add hq2.1).const_mul _))
            (fun ω => by
              simp only [Function.uncurry_apply_pair, hf, Real.norm_eq_abs]
              exact kl_lin_to_quad hA' hLg _)
      _ = (↑d * M2 + M1 * Mb) + (M1 * |q|) * (1 + ∫ ω, ‖Z s ω‖ ^ 2 ∂P) := by
          have hq1 : Integrable (fun ω => 1 + ‖Z s ω‖ ^ 2) P := (integrable_const (1 : ℝ)).add hq2.1
          have hq3 : Integrable (fun ω => (M1 * |q|) * (1 + ‖Z s ω‖ ^ 2)) P := hq1.const_mul _
          rw [integral_add (integrable_const _) hq3, integral_const_mul, integral_add (integrable_const _) hq2.1]
          simp
      _ ≤ Kg := by
          rw [hKg]
          have := hq2.2
          gcongr
  have hI : Integrable (fun ω => ∫ s in Icc (0 : ℝ) t, f s ω) P := hFint.integral_prod_right
  have hht : Integrable (fun ω => h (Z t ω)) P :=
    kl_integrable_lin P hh.continuous.measurable hM10 (kl_abs_le_lin hh hM1) (hZm t)
      (hZ2 t ⟨ht, le_rfl⟩).1
  have hMeq' : ∀ᵐ ω ∂P, h (Z t ω) = h x + (∫ s in Icc (0 : ℝ) t, f s ω) + M ω := by
    filter_upwards [hMeq] with ω hω
    have h0 : Z 0 ω = x := by simpa [hZdef] using (hps ω).1
    rw [hω, h0]
    congr 3
    funext s
    exact kl_drift_eq q B h (Z s ω)
  have key : ∫ ω, h (Z t ω) ∂P = h x + ∫ ω, (∫ s in Icc (0 : ℝ) t, f s ω) ∂P := by
    have hI2 : Integrable (fun ω => h x + ∫ s in Icc (0 : ℝ) t, f s ω) P :=
      (integrable_const (h x)).add hI
    rw [integral_congr_ae hMeq', integral_add hI2 hMi, integral_add (integrable_const _) hI, hM0]
    simp
  have swap := integral_integral_swap (μ := volume.restrict (Icc (0 : ℝ) t)) (ν := P) hFint
  have hsg : ∀ s ∈ Icc (0 : ℝ) t, ∫ ω, f s ω ∂P = sg P W q B s (kolmL q B h) x := fun s hs => by
    simp only [hf, hZdef, sg, max_eq_left hs.1]
  have e1 : sg P W q B t h x = ∫ ω, h (Z t ω) ∂P := by
    simp only [hZdef, sg, max_eq_left ht]
  rw [e1, key]
  congr 1
  calc ∫ ω, (∫ s in Icc (0 : ℝ) t, f s ω) ∂P
      = ∫ s in Icc (0 : ℝ) t, ∫ ω, f s ω ∂P := swap.symm
    _ = ∫ s in Icc (0 : ℝ) t, sg P W q B s (kolmL q B h) x :=
        setIntegral_congr_fun measurableSet_Icc fun s hs => hsg s hs
    _ = _ := setIntegral_Icc_eq_interval ht

/-- Common growth constant of `L h`: `|L h y| ≤ a (1 + ‖y‖)`. -/
theorem kl_L_growth' {q Mb : ℝ} {B : Euc d → Euc d} (hBb : ∀ y, ‖B y‖ ≤ Mb) {h : Euc d → ℝ}
    {M1 M2 : ℝ} (hM1 : ∀ y, ‖fderiv ℝ h y‖ ≤ M1) (hM2 : ∀ y, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ M2) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ y, |kolmL q B h y| ≤ a * (1 + ‖y‖) := by
  have hM10 : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0)
  have hM20 : 0 ≤ M2 := (norm_nonneg (fderiv ℝ (fderiv ℝ h) 0)).trans (hM2 0)
  have hMb : 0 ≤ Mb := (norm_nonneg (B 0)).trans (hBb 0)
  refine ⟨(d * M2 + M1 * Mb) + M1 * |q|, by positivity, fun y => ?_⟩
  refine (kl_L_growth q hBb hM1 hM2 y).trans ?_
  have : 0 ≤ (d : ℝ) * M2 + M1 * Mb := by positivity
  nlinarith [mul_nonneg hM10 (abs_nonneg q), norm_nonneg y]

/-- **Kolmogorov backward equation, time derivative.**  For `h ∈ C²` with bounded `Dh`, `D²h`,
`t ↦ P_t h (x)` has right derivative `P_t (L h)(x)` at every `t ≥ 0` (and derivative for `t > 0`). -/
theorem kl_hasDerivWithinAt {q Mb : ℝ} (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d}
    (hB : HasCbBound m Mb B) [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    {h : Euc d → ℝ} (hh : ContDiff ℝ 2 h) {M1 M2 : ℝ} (hM1 : ∀ y, ‖fderiv ℝ h y‖ ≤ M1)
    (hM2 : ∀ y, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ M2) (x : Euc d) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => sg P W q B s h x) (sg P W q B t (kolmL q B h) x) (Ici 0) t := by
  have hBb : ∀ y, ‖B y‖ ≤ Mb := fun y => by simpa using hB.2 0 (Nat.zero_le _) y
  obtain ⟨a, ha, hga⟩ := kl_L_growth' (q := q) hBb hM1 hM2
  set T : ℝ := t + 1 with hT
  have hT0 : 0 ≤ T := by linarith
  have hcont : ContinuousOn (fun p : ℝ × Euc d => sg P W q B p.1 (kolmL q B h) p.2)
      (Icc 0 T ×ˢ univ) :=
    kl_cont_integral hq hm hB hW hT0 (kl_L_continuous q hB.1.continuous hh) ha hga
  have hf : Continuous (fun s : ℝ => sg P W q B (clampT T s) (kolmL q B h) x) := by
    have h1 : Continuous (fun s : ℝ => (clampT T s, x)) :=
      (continuous_clampT T).prodMk continuous_const
    have h3 := hcont.comp_continuous h1 (fun s => ⟨clampT_mem hT0 s, mem_univ _⟩)
    exact h3
  have hF : HasDerivAt (fun u : ℝ => h x + ∫ r in (0 : ℝ)..u,
      sg P W q B (clampT T r) (kolmL q B h) x) (sg P W q B (clampT T t) (kolmL q B h) x) t :=
    (hf.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add (h x)
  have hFt : (fun s : ℝ => sg P W q B s h x) =ᶠ[𝓝[Ici 0] t]
      fun s => h x + ∫ r in (0 : ℝ)..s, sg P W q B (clampT T r) (kolmL q B h) x := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (show t < T by linarith))]
      with s hs hsT
    rw [kl_integral_identity hq hm hB hW hh hM1 hM2 hs x]
    congr 1
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hs] at hr
    simp only [clampT_of_mem (⟨hr.1, hr.2.trans (le_of_lt hsT)⟩ : r ∈ Icc (0 : ℝ) T)]
  have h0 : sg P W q B t h x = h x + ∫ r in (0 : ℝ)..t, sg P W q B (clampT T r) (kolmL q B h) x := by
    rw [kl_integral_identity hq hm hB hW hh hM1 hM2 ht x]
    congr 1
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le ht] at hr
    simp only [clampT_of_mem (⟨hr.1, hr.2.trans (by linarith)⟩ : r ∈ Icc (0 : ℝ) T)]
  have := (hF.hasDerivWithinAt (s := Ici 0)).congr_of_eventuallyEq hFt h0
  rwa [show clampT T t = t from clampT_of_mem ⟨ht, by linarith⟩] at this

/-! ### Pathwise chain rule for `h ∘ φ_t` -/

/-- The second derivative of `h ∘ φ`: `D²(h∘φ)(w,v) = Dh(φ) D²φ(w,v) + D²h(φ)(Dφ w, Dφ v)`. -/
def klE2 (h : Euc d → ℝ) (φ : Euc d → Euc d) (y : Euc d) : Euc d →L[ℝ] Euc d →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ (Euc d) (Euc d) ℝ) (fderiv ℝ h (φ y))).comp
      (fderiv ℝ (fderiv ℝ φ) y) +
    ((ContinuousLinearMap.compL ℝ (Euc d) (Euc d) ℝ).flip (fderiv ℝ φ y)).comp
      ((fderiv ℝ (fderiv ℝ h) (φ y)).comp (fderiv ℝ φ y))

theorem kl_comp_fderiv {h : Euc d → ℝ} (hh : ContDiff ℝ 2 h) {φ : Euc d → Euc d}
    (hφ : ContDiff ℝ 2 φ) (y : Euc d) :
    fderiv ℝ (fun z => h (φ z)) y = (fderiv ℝ h (φ y)).comp (fderiv ℝ φ y) :=
  fderiv_comp y (hh.differentiable (by norm_num) _) (hφ.differentiable (by norm_num) y)

theorem kl_comp_hasFDerivAt2 {h : Euc d → ℝ} (hh : ContDiff ℝ 2 h) {φ : Euc d → Euc d}
    (hφ : ContDiff ℝ 2 φ) (y : Euc d) :
    HasFDerivAt (fderiv ℝ (fun z => h (φ z))) (klE2 h φ y) y := by
  have e : fderiv ℝ (fun z => h (φ z)) = fun z => (fderiv ℝ h (φ z)).comp (fderiv ℝ φ z) :=
    funext fun z => kl_comp_fderiv hh hφ z
  rw [e]
  have hφd : HasFDerivAt φ (fderiv ℝ φ y) y := (hφ.differentiable (by norm_num) y).hasFDerivAt
  have hA : HasFDerivAt (fderiv ℝ h) (fderiv ℝ (fderiv ℝ h) (φ y)) (φ y) :=
    ((hh.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) _).hasFDerivAt
  have hA' : HasFDerivAt (fun z => fderiv ℝ h (φ z))
      ((fderiv ℝ (fderiv ℝ h) (φ y)).comp (fderiv ℝ φ y)) y := hA.comp y hφd
  have hD : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) y) y :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) y).hasFDerivAt
  exact hA'.clm_comp hD

theorem kl_E2_apply (h : Euc d → ℝ) (φ : Euc d → Euc d) (y w v : Euc d) :
    klE2 h φ y w v = fderiv ℝ h (φ y) (fderiv ℝ (fderiv ℝ φ) y w v) +
      fderiv ℝ (fderiv ℝ h) (φ y) (fderiv ℝ φ y w) (fderiv ℝ φ y v) := by
  simp [klE2]

namespace KlPath

variable {T : ℝ} {b : Euc d → Euc d} {c : ℝ → Euc d} {φ : ℝ → Euc d → Euc d} {C1 C2 Λ1 Λ2 : ℝ}

theorem comp_bound1 (H : KlPath T b c φ C1 C2 Λ1 Λ2) {h : Euc d → ℝ} (hh : ContDiff ℝ 2 h)
    {M1 : ℝ} (hM1 : ∀ y, ‖fderiv ℝ h y‖ ≤ M1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (y : Euc d) :
    ‖fderiv ℝ (fun z => h (φ t z)) y‖ ≤ M1 * C1 := by
  rw [kl_comp_fderiv hh (H.c2 t ht)]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (hM1 _) (H.bd1 t ht y) (norm_nonneg _) ((norm_nonneg _).trans (hM1 0)))

theorem comp_bound2 (H : KlPath T b c φ C1 C2 Λ1 Λ2) {h : Euc d → ℝ} (hh : ContDiff ℝ 2 h)
    {M1 M2 : ℝ} (hM1 : ∀ y, ‖fderiv ℝ h y‖ ≤ M1) (hM2 : ∀ y, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ M2)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (y : Euc d) :
    ‖klE2 h (φ t) y‖ ≤ M1 * C2 + M2 * C1 ^ 2 := by
  have h0 := H.bd1_nonneg; have h1 := H.bd2_nonneg
  have hM10 : 0 ≤ M1 := (norm_nonneg (fderiv ℝ h 0)).trans (hM1 0)
  have hM20 : 0 ≤ M2 := (norm_nonneg (fderiv ℝ (fderiv ℝ h) 0)).trans (hM2 0)
  have hK : 0 ≤ M1 * C2 + M2 * C1 ^ 2 := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ hK fun w => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK (norm_nonneg w)) fun v => ?_
  rw [kl_E2_apply]
  have e1 : ‖fderiv ℝ h (φ t y) (fderiv ℝ (fderiv ℝ (φ t)) y w v)‖ ≤ M1 * (C2 * ‖w‖ * ‖v‖) := by
    refine ((fderiv ℝ h (φ t y)).le_opNorm _).trans ?_
    refine mul_le_mul (hM1 _) ?_ (norm_nonneg _) hM10
    calc ‖fderiv ℝ (fderiv ℝ (φ t)) y w v‖ ≤ ‖fderiv ℝ (fderiv ℝ (φ t)) y‖ * ‖w‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ C2 * ‖w‖ * ‖v‖ := by gcongr; exact H.bd2 t ht y
  have h1w : ‖fderiv ℝ (φ t) y w‖ ≤ C1 * ‖w‖ :=
    ((fderiv ℝ (φ t) y).le_opNorm w).trans (mul_le_mul_of_nonneg_right (H.bd1 t ht y) (norm_nonneg _))
  have h1v : ‖fderiv ℝ (φ t) y v‖ ≤ C1 * ‖v‖ :=
    ((fderiv ℝ (φ t) y).le_opNorm v).trans (mul_le_mul_of_nonneg_right (H.bd1 t ht y) (norm_nonneg _))
  have e2 : ‖fderiv ℝ (fderiv ℝ h) (φ t y) (fderiv ℝ (φ t) y w) (fderiv ℝ (φ t) y v)‖ ≤
      M2 * (C1 * ‖w‖) * (C1 * ‖v‖) := by
    calc _ ≤ ‖fderiv ℝ (fderiv ℝ h) (φ t y)‖ * ‖fderiv ℝ (φ t) y w‖ * ‖fderiv ℝ (φ t) y v‖ :=
          ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ M2 * (C1 * ‖w‖) * (C1 * ‖v‖) := by
          have := hM2 (φ t y)
          gcongr
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ M1 * (C2 * ‖w‖ * ‖v‖) + M2 * (C1 * ‖w‖) * (C1 * ‖v‖) := add_le_add e1 e2
    _ = (M1 * C2 + M2 * C1 ^ 2) * ‖w‖ * ‖v‖ := by ring

theorem comp_cont1 (H : KlPath T b c φ C1 C2 Λ1 Λ2) {h : Euc d → ℝ} (hh : ContDiff ℝ 2 h) :
    ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (fun z => h (φ p.1 z)) p.2) (Icc 0 T ×ˢ univ) := by
  refine ContinuousOn.congr ?_ (fun p hp => kl_comp_fderiv hh (H.c2 p.1 hp.1) p.2)
  exact (((hh.continuous_fderiv (by norm_num)).comp_continuousOn H.cont_phi)).clm_comp H.cont_fderiv

theorem comp_cont2 (H : KlPath T b c φ C1 C2 Λ1 Λ2) {h : Euc d → ℝ} (hh : ContDiff ℝ 2 h) :
    ContinuousOn (fun p : ℝ × Euc d => klE2 h (φ p.1) p.2) (Icc 0 T ×ˢ univ) := by
  have h1 : ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ h (φ p.1 p.2)) (Icc 0 T ×ˢ univ) :=
    (hh.continuous_fderiv (by norm_num)).comp_continuousOn H.cont_phi
  have h2 : ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (fderiv ℝ h) (φ p.1 p.2))
      (Icc 0 T ×ˢ univ) :=
    ((hh.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)).comp_continuousOn
      H.cont_phi
  set K1 : (Euc d →L[ℝ] ℝ) →L[ℝ] (Euc d →L[ℝ] Euc d) →L[ℝ] (Euc d →L[ℝ] ℝ) :=
    ContinuousLinearMap.compL ℝ (Euc d) (Euc d) ℝ with hK1
  have h3 : ContinuousOn (fun p : ℝ × Euc d => K1 (fderiv ℝ h (φ p.1 p.2))) (Icc 0 T ×ˢ univ) :=
    K1.continuous.comp_continuousOn h1
  have h4 : ContinuousOn (fun p : ℝ × Euc d => K1.flip (fderiv ℝ (φ p.1) p.2)) (Icc 0 T ×ˢ univ) :=
    K1.flip.continuous.comp_continuousOn H.cont_fderiv
  have h5 := h2.clm_comp H.cont_fderiv
  have h6 := h3.clm_comp H.cont_fderiv2
  have h7 := h4.clm_comp h5
  exact h6.add h7

end KlPath

end Ito

/-! ### Differentiation under the expectation -/

section Smooth

open HRS.MS.FlowB (clampT continuous_clampT clampT_mem clampT_of_mem)

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → Fin d → ℝ}

/-- The pathwise composite `z ↦ h (φ^ω_t z)`. -/
abbrev klG (q : ℝ) (B : Euc d → Euc d) (W : ℝ≥0 → Ω → Fin d → ℝ) (h : Euc d → ℝ) (t : ℝ)
    (ω : Ω) : Euc d → ℝ := fun z => h (flowMap q B (fun s => W s ω) t z)

theorem kl_meas_D {q Mb : ℝ} (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d}
    (hB : HasCbBound m Mb B) (hn : SgNoise W) {T : ℝ} (hT : 0 ≤ T) {h : Euc d → ℝ}
    (hh : ContDiff ℝ 2 h) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    StronglyMeasurable (fun p : Ω × Euc d => fderiv ℝ (klG q B W h t p.1) p.2) ∧
    StronglyMeasurable (fun p : Ω × Euc d => fderiv ℝ (fderiv ℝ (klG q B W h t p.1)) p.2) := by
  obtain ⟨C, hC, hpath⟩ := kl_pathω (q := q) (Mb := Mb) hq hm hT hn
  have hm1 : 1 ≤ m := by omega
  have hflow : Measurable (fun p : Ω × Euc d => flowMap q B (fun s => W s p.1) t p.2) :=
    sg_measurable_flowMap hn hq.le hm1 hB ht.1
  have hGm : StronglyMeasurable (fun p : Ω × Euc d => klG q B W h t p.1 p.2) :=
    (hh.continuous.measurable.comp hflow).stronglyMeasurable
  have hG2 : ∀ ω, ContDiff ℝ 2 (klG q B W h t ω) := fun ω => hh.comp ((hpath B hB ω).c2 t ht)
  have hS1 := sg_stronglyMeasurable_fderiv (fun ω => klG q B W h t ω) hGm
    (fun ω => (hG2 ω).differentiable (by norm_num))
  refine ⟨hS1, sg_stronglyMeasurable_fderiv (fun ω => fderiv ℝ (klG q B W h t ω)) hS1
    (fun ω => ((hG2 ω).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num))⟩

set_option maxHeartbeats 1000000 in
/-- Differentiation of `y ↦ ∫ h (φ^ω_t y) dP` twice under the integral sign. -/
theorem kl_sg_deriv {q Mb : ℝ} (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d}
    (hB : HasCbBound m Mb B) [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {T : ℝ}
    (hT : 0 ≤ T) {h : Euc d → ℝ} (hh : ContDiff ℝ 2 h) {M1 M2 : ℝ} (hM1 : ∀ y, ‖fderiv ℝ h y‖ ≤ M1)
    (hM2 : ∀ y, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ M2) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (∀ y, HasFDerivAt (sg P W q B t h) (∫ ω, fderiv ℝ (klG q B W h t ω) y ∂P) y) ∧
    ∀ y, HasFDerivAt (fun z => ∫ ω, fderiv ℝ (klG q B W h t ω) z ∂P)
      (∫ ω, fderiv ℝ (fderiv ℝ (klG q B W h t ω)) y ∂P) y := by
  have hm1 : 1 ≤ m := by omega
  have hn := sgNoise_of_brownian hW
  obtain ⟨C, hC, hpath⟩ := kl_pathω (q := q) (Mb := Mb) hq hm hT hn
  obtain ⟨Cm, hCm, hmom⟩ := sg_second_moment (d := d) q Mb hq T hT
  obtain ⟨hS1, hS2⟩ := kl_meas_D hq hm hB hn hT hh ht
  have hM10 : 0 ≤ M1 := (norm_nonneg (fderiv ℝ h 0)).trans (hM1 0)
  have hG2 : ∀ ω, ContDiff ℝ 2 (klG q B W h t ω) := fun ω => hh.comp ((hpath B hB ω).c2 t ht)
  have hflowy : ∀ y, Measurable (fun ω => flowMap q B (fun s => W s ω) t y) := fun y => by
    have h1 : Measurable (fun p : Ω × Euc d => flowMap q B (fun s => W s p.1) t p.2) :=
      sg_measurable_flowMap hn hq.le hm1 hB ht.1
    have h2 : Measurable (fun ω : Ω => (ω, y)) := measurable_id.prodMk measurable_const
    have h3 := h1.comp h2
    exact h3
  have hpt : ∀ ω y, ‖fderiv ℝ (klG q B W h t ω) y‖ ≤ M1 * C := fun ω y =>
    (hpath B hB ω).comp_bound1 hh hM1 ht y
  have hpt2 : ∀ ω y, ‖fderiv ℝ (fderiv ℝ (klG q B W h t ω)) y‖ ≤ M1 * C + M2 * C ^ 2 := fun ω y => by
    rw [(kl_comp_hasFDerivAt2 hh ((hpath B hB ω).c2 t ht) y).fderiv]
    exact (hpath B hB ω).comp_bound2 hh hM1 hM2 ht y
  constructor
  · intro y
    have := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := P) (s := univ)
      (F := fun z ω => klG q B W h t ω z) (F' := fun z ω => fderiv ℝ (klG q B W h t ω) z)
      (bound := fun _ => M1 * C) (x₀ := y) Filter.univ_mem
      (Eventually.of_forall fun z => (hh.continuous.measurable.comp (hflowy z)).aestronglyMeasurable)
      (kl_integrable_lin P hh.continuous.measurable hM10 (kl_abs_le_lin hh hM1) (hflowy y)
        (hmom P ℱ W hW m hm1 B hB t ht y).1)
      ((hS1.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
      (Eventually.of_forall fun ω z _ => hpt ω z) (integrable_const _)
      (Eventually.of_forall fun ω z _ => ((hG2 ω).differentiable (by norm_num) z).hasFDerivAt)
    exact this
  · intro y
    have := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := P) (s := univ)
      (F := fun z ω => fderiv ℝ (klG q B W h t ω) z)
      (F' := fun z ω => fderiv ℝ (fderiv ℝ (klG q B W h t ω)) z)
      (bound := fun _ => M1 * C + M2 * C ^ 2) (x₀ := y) Filter.univ_mem
      (Eventually.of_forall fun z =>
        (hS1.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
      (Integrable.of_bound
        ((hS1.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
        (M1 * C) (Eventually.of_forall fun ω => hpt ω y))
      ((hS2.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
      (Eventually.of_forall fun ω z _ => hpt2 ω z) (integrable_const _)
      (Eventually.of_forall fun ω z _ =>
        (((hG2 ω).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z).hasFDerivAt)
    exact this

set_option maxHeartbeats 1000000 in
/-- **`C^{1,2}` regularity.**  `(t, x) ↦ P_t h (x)` is `C^{1,2}` on `[0,T] × ℝ^d` in the sense of
`IsC12On` (jointly continuous `u, Du, D²u, ∂_t u`). -/
theorem kl_isC12On {q Mb : ℝ} (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d}
    (hB : HasCbBound m Mb B) [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {T : ℝ}
    (hT : 0 < T) {h : Euc d → ℝ} (hh : ContDiff ℝ 2 h) {M1 M2 : ℝ} (hM1 : ∀ y, ‖fderiv ℝ h y‖ ≤ M1)
    (hM2 : ∀ y, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ M2) :
    IsC12On T Set.univ (fun t x => sg P W q B t h x) := by
  have hT0 : 0 ≤ T := hT.le
  have hn := sgNoise_of_brownian hW
  have hm1 : 1 ≤ m := by omega
  obtain ⟨C, hC, hpath⟩ := kl_pathω (q := q) (Mb := Mb) hq hm hT0 hn
  have hM10 : 0 ≤ M1 := (norm_nonneg (fderiv ℝ h 0)).trans (hM1 0)
  have hBb : ∀ y, ‖B y‖ ≤ Mb := fun y => by simpa using hB.2 0 (Nat.zero_le _) y
  obtain ⟨a, ha, hga⟩ := kl_L_growth' (q := q) hBb hM1 hM2
  have hD := fun t (ht : t ∈ Icc (0 : ℝ) T) => kl_sg_deriv hq hm hB hW hT0 hh hM1 hM2 ht
  have hcontL : ContinuousOn (fun p : ℝ × Euc d => sg P W q B p.1 (kolmL q B h) p.2)
      (Icc 0 T ×ˢ univ) :=
    kl_cont_integral hq hm hB hW hT0 (kl_L_continuous q hB.1.continuous hh) ha hga
  have hderiv : ∀ x t, t ∈ Icc (0 : ℝ) T →
      derivWithin (fun r => sg P W q B r h x) (Icc 0 T) t = sg P W q B t (kolmL q B h) x := by
    intro x t ht
    exact ((kl_hasDerivWithinAt hq hm hB hW hh hM1 hM2 x ht.1).mono
      (fun r hr => hr.1)).derivWithin (uniqueDiffOn_Icc hT t ht)
  have hD2eq : ∀ ω t (ht : t ∈ Icc (0 : ℝ) T) y,
      fderiv ℝ (fderiv ℝ (klG q B W h t ω)) y = klE2 h (flowMap q B (fun s => W s ω) t) y :=
    fun ω t ht y => (kl_comp_hasFDerivAt2 hh ((hpath B hB ω).c2 t ht) y).fderiv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := kl_cont_integral hq hm hB hW hT0 hh.continuous (a := max |h 0| M1) (le_max_of_le_left (abs_nonneg _))
      (fun y => (kl_abs_le_lin hh hM1 y).trans (by
        have := norm_nonneg y
        nlinarith [le_max_left |h 0| M1, le_max_right |h 0| M1]))
    exact this
  · intro t ht x _
    exact ((hD t ht).1 x).differentiableAt.hasFDerivAt
  · intro t ht x _
    have e : fderiv ℝ (sg P W q B t h) = fun z => ∫ ω, fderiv ℝ (klG q B W h t ω) z ∂P :=
      funext fun z => ((hD t ht).1 z).fderiv
    rw [e]
    exact ((hD t ht).2 x).differentiableAt.hasFDerivAt
  · refine ContinuousOn.congr (f := fun p : ℝ × Euc d => ∫ ω, fderiv ℝ (klG q B W h p.1 ω) p.2 ∂P)
      ?_ (fun p hp => ((hD p.1 hp.1).1 p.2).fderiv)
    refine continuousOn_of_dominated (bound := fun _ => M1 * C) (fun p hp => ?_) (fun p hp => ?_)
      (integrable_const _) (Eventually.of_forall fun ω => (hpath B hB ω).comp_cont1 hh)
    · exact ((kl_meas_D hq hm hB hn hT0 hh hp.1).1.comp_measurable
        (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    · exact Eventually.of_forall fun ω => (hpath B hB ω).comp_bound1 hh hM1 hp.1 p.2
  · refine ContinuousOn.congr (f := fun p : ℝ × Euc d =>
      ∫ ω, fderiv ℝ (fderiv ℝ (klG q B W h p.1 ω)) p.2 ∂P) ?_ (fun p hp => ?_)
    · refine continuousOn_of_dominated (bound := fun _ => M1 * C + M2 * C ^ 2) (fun p hp => ?_)
        (fun p hp => ?_) (integrable_const _) (Eventually.of_forall fun ω => ?_)
      · exact ((kl_meas_D hq hm hB hn hT0 hh hp.1).2.comp_measurable
          (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      · exact Eventually.of_forall fun ω => by
          rw [hD2eq ω p.1 hp.1 p.2]; exact (hpath B hB ω).comp_bound2 hh hM1 hM2 hp.1 p.2
      · exact ((hpath B hB ω).comp_cont2 hh).congr fun p hp => hD2eq ω p.1 hp.1 p.2
    · have e : fderiv ℝ (sg P W q B p.1 h) = fun z => ∫ ω, fderiv ℝ (klG q B W h p.1 ω) z ∂P :=
        funext fun z => ((hD p.1 hp.1).1 z).fderiv
      show fderiv ℝ (fderiv ℝ (sg P W q B p.1 h)) p.2 = _
      rw [e]
      exact ((hD p.1 hp.1).2 p.2).fderiv
  · intro x _ t ht
    rw [hderiv x t ht]
    exact (kl_hasDerivWithinAt hq hm hB hW hh hM1 hM2 x ht.1).mono (fun r hr => hr.1)
  · exact hcontL.congr fun p hp => hderiv p.2 p.1 hp.1

end Smooth

section Main

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → Fin d → ℝ}

/-- **POIS-KOLM.**  The Kolmogorov backward equation for the semigroup `sg`: for `h ∈ C²` with bounded
`Dh`, `D²h` (see the module docstring). -/
theorem pois_kolmogorov {q Mb : ℝ} (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d}
    (hB : HasCbBound m Mb B) [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    {h : Euc d → ℝ} (hh : ContDiff ℝ 2 h) {M1 M2 : ℝ} (hM1 : ∀ y, ‖fderiv ℝ h y‖ ≤ M1)
    (hM2 : ∀ y, ‖iteratedFDeriv ℝ 2 h y‖ ≤ M2) :
    (∀ t : ℝ, 0 ≤ t → ∀ x, sg P W q B t h x =
      h x + ∫ s in (0 : ℝ)..t, sg P W q B s (kolmL q B h) x) ∧
    (∀ (x : Euc d) (t : ℝ), 0 ≤ t → HasDerivWithinAt (fun s => sg P W q B s h x)
      (sg P W q B t (kolmL q B h) x) (Ici 0) t) ∧
    (∀ (x : Euc d) (t : ℝ), 0 < t → HasDerivAt (fun s => sg P W q B s h x)
      (sg P W q B t (kolmL q B h) x) t) ∧
    (∀ T : ℝ, 0 < T → IsC12On T Set.univ (fun t x => sg P W q B t h x)) := by
  have hM2' : ∀ y, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ M2 := fun y => by
    rw [kl_norm_fderiv_fderiv']; exact hM2 y
  have hD : ∀ (x : Euc d) (t : ℝ), 0 ≤ t → HasDerivWithinAt (fun s => sg P W q B s h x)
      (sg P W q B t (kolmL q B h) x) (Ici 0) t := fun x t ht =>
    kl_hasDerivWithinAt hq hm hB hW hh hM1 hM2' x ht
  exact ⟨fun t ht x => kl_integral_identity hq hm hB hW hh hM1 hM2' ht x, hD,
    fun x t ht => (hD x t ht.le).hasDerivAt (Ici_mem_nhds ht),
    fun T hT => kl_isC12On hq hm hB hW hT hh hM1 hM2'⟩

end Main

end HRS.MS.PoisKolm
