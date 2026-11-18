import HRS.Equilibrium.QuadraticLimit.Chaos
import HRS.Equilibrium.QuadraticLimit.Features
import HRS.Equilibrium.QuadraticLimit.Spectral
import HRS.Equilibrium.QuadraticLimit.GibbsAuxO

/-!
# Lemma 7.5 `quadratic_limit`: assembly (packet Q08, sub-packet `Assembly`)

`HRS.quadratic_limit_proof` restates `HRS.quadratic_limit` verbatim and proves it from
* `Spectral`: `q08_Kmat_spec`, `q08_Hmat_spec`, `q08_coef_summable`, `q08_Cmat_spec`, `q08_bounded_family`,
* `Chaos`: `q08_chaos_exists`, `q08_chaos_l2_bound`,
* `Features`: `q08_gibbs_isProb`, `q08_measurable_energy`, `q08_integrable_energy`, `q08_weight_Lq`,
  `q08_energy_L2`, `q08_clt_quadratic`, `q08_gauss_tilt`,
* the intermediate layer `q08_gibbs_approx` below (still `sorry`: the finite-rank approximation theorem).

Everything else (existence of the probability space, `L²` limits of the finite chaos, bounded Lipschitz to
bounded continuous test functions via Portmanteau, the shift `N ↦ N+1`) is proved here.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Q08

/-- `L²`-convergence to `0` on a probability space implies `L¹`-convergence to `0`. -/
theorem q08_tendsto_lintegral_enorm {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (f : ℕ → Ω → ℝ) (hf : ∀ L, Measurable (f L))
    (h : Tendsto (fun L => ∫⁻ ω, ‖f L ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun L => ∫⁻ ω, ‖f L ω‖ₑ ∂P) atTop (𝓝 0) := by
  have h2 : Tendsto (fun L => (∫⁻ ω, ‖f L ω‖ₑ ^ 2 ∂P) ^ (1 / (2 : ℝ))) atTop (𝓝 0) := by
    have := ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ)) |>.tendsto 0
    have h0 : (0 : ℝ≥0∞) ^ (1 / (2 : ℝ)) = 0 := by
      rw [ENNReal.zero_rpow_of_pos (by norm_num)]
    rw [h0] at this
    exact this.comp h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun L => bot_le) (fun L => ?_)
  have := eLpNorm_le_eLpNorm_of_exponent_le (μ := P) (p := 1) (q := 2) (f := f L) (by norm_num)
  rw [eLpNorm_one_eq_lintegral_enorm] at this
  · refine this.trans (le_of_eq ?_)
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp
    all_goals exact (hf L).aestronglyMeasurable
  · exact (hf L).aestronglyMeasurable


/-- Passing from the finite-dimensional Gaussian chaos functionals to the limit chaos (bounded Lipschitz
test functions). -/
theorem q08_finiteChaos_tendsto {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p : ℕ} (C H : ℕ → ℕ → ℝ) (a : Fin p → ℕ → ℝ)
    (G : ℕ → Ω → ℝ) (Q : Ω → ℝ) (Lin : Fin p → Ω → ℝ)
    (hGm : ∀ i, Measurable (G i)) (hQm : Measurable Q) (hLm : ∀ b, Measurable (Lin b))
    (hlaw : ∀ n : ℕ, law P (fun ω => (WithLp.toLp 2 fun i : Fin n => G i ω : EuclideanSpace ℝ (Fin n))) =
        multivariateGaussian 0 (Matrix.of fun i j : Fin n => C i j))
    (hLin : ∀ b, Tendsto (fun L => ∫⁻ ω, ‖Lin b ω - ∑ i ∈ Finset.range L, a b i * G i ω‖ₑ ^ 2 ∂P)
        atTop (𝓝 0))
    (hQ : Tendsto (fun L => ∫⁻ ω, ‖Q ω - (1 / 2) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
          H i j * (G i ω * G j ω - C i j)‖ₑ ^ 2 ∂P) atTop (𝓝 0))
    (F : ℝ × (Fin p → ℝ) → ℝ) (M : ℝ) (hM : ∀ z, |F z| ≤ M) (K : ℝ≥0) (hF : LipschitzWith K F) :
    Tendsto (fun L : ℕ => ∫ g : EuclideanSpace ℝ (Fin L),
        F ((1 / 2) * ∑ i : Fin L, ∑ j : Fin L, H i j * (g i * g j - C i j),
          fun b => ∑ i : Fin L, a b i * g i)
        ∂(multivariateGaussian 0 (Matrix.of fun i j : Fin L => C i j))) atTop
      (𝓝 (∫ ω, F (Q ω, fun b => Lin b ω) ∂P)) := by
  -- the finite-L functionals on `Ω`
  set TQ : ℕ → Ω → ℝ := fun L ω => (1 / 2) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
    H i j * (G i ω * G j ω - C i j) with hTQ
  set TB : ℕ → Fin p → Ω → ℝ := fun L b ω => ∑ i ∈ Finset.range L, a b i * G i ω with hTB
  have hTQm : ∀ L, Measurable (TQ L) := fun L => by
    simp only [hTQ]
    refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_) _
    exact measurable_const.mul (((hGm i).mul (hGm j)).sub measurable_const)
  have hTBm : ∀ L b, Measurable (TB L b) := fun L b => by
    simp only [hTB]
    exact Finset.measurable_sum _ fun i _ => measurable_const.mul (hGm i)
  have hFc : Continuous F := hF.continuous
  have hFm : Measurable F := hFc.measurable
  have hTm : ∀ L, Measurable (fun ω => (TQ L ω, fun b => TB L b ω)) := fun L =>
    (hTQm L).prodMk (measurable_pi_iff.2 fun b => hTBm L b)
  have hT0 : Measurable (fun ω => (Q ω, fun b => Lin b ω)) :=
    hQm.prodMk (measurable_pi_iff.2 fun b => hLm b)
  -- Step 1: Gaussian integrals as integrals over `Ω`
  have step1 : ∀ L : ℕ, ∫ g : EuclideanSpace ℝ (Fin L),
        F ((1 / 2) * ∑ i : Fin L, ∑ j : Fin L, H i j * (g i * g j - C i j),
          fun b => ∑ i : Fin L, a b i * g i)
        ∂(multivariateGaussian 0 (Matrix.of fun i j : Fin L => C i j)) =
      ∫ ω, F (TQ L ω, fun b => TB L b ω) ∂P := by
    intro L
    rw [← hlaw L]
    have hGv : Measurable (fun ω => (WithLp.toLp 2 fun i : Fin L => G i ω : EuclideanSpace ℝ (Fin L))) := by
      refine (WithLp.measurable_toLp 2 (Fin L → ℝ)).comp (measurable_pi_iff.2 fun i => hGm i)
    unfold law
    rw [integral_map hGv.aemeasurable]
    · refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [hTQ, hTB, Finset.sum_range]
    · refine (hFm.comp ?_).aestronglyMeasurable
      refine Measurable.prodMk ?_ (measurable_pi_iff.2 fun b => ?_)
      · refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_) _
        exact measurable_const.mul (((measurable_pi_apply i |>.comp (PiLp.continuous_ofLp 2 _ |>.measurable)).mul
          (measurable_pi_apply j |>.comp (PiLp.continuous_ofLp 2 _ |>.measurable))).sub measurable_const)
      · exact Finset.measurable_sum _ fun i _ => measurable_const.mul
          (measurable_pi_apply i |>.comp (PiLp.continuous_ofLp 2 _ |>.measurable))
  simp_rw [step1]
  have hint : ∀ f : Ω → ℝ × (Fin p → ℝ), Measurable f → Integrable (fun ω => F (f ω)) P := fun f hf =>
    Integrable.of_bound (hFm.comp hf).aestronglyMeasurable M
      (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hM _)
  -- pointwise Lipschitz bound
  have hpt : ∀ L ω, ‖F (TQ L ω, fun b => TB L b ω) - F (Q ω, fun b => Lin b ω)‖ₑ ≤
      ENNReal.ofReal K * (‖Q ω - TQ L ω‖ₑ + ∑ b, ‖Lin b ω - TB L b ω‖ₑ) := by
    intro L ω
    have h1 : dist (F (TQ L ω, fun b => TB L b ω)) (F (Q ω, fun b => Lin b ω)) ≤
        K * dist (TQ L ω, fun b => TB L b ω) (Q ω, fun b => Lin b ω) := hF.dist_le_mul _ _
    have h2 : dist (TQ L ω, fun b => TB L b ω) (Q ω, fun b => Lin b ω) ≤
        |Q ω - TQ L ω| + ∑ b, |Lin b ω - TB L b ω| := by
      rw [Prod.dist_eq]
      refine max_le ?_ ?_
      · rw [Real.dist_eq, abs_sub_comm]
        have : 0 ≤ ∑ b, |Lin b ω - TB L b ω| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        linarith
      · rw [dist_pi_le_iff (by positivity)]
        intro b
        rw [Real.dist_eq, abs_sub_comm]
        have : |Lin b ω - TB L b ω| ≤ ∑ b, |Lin b ω - TB L b ω| :=
          Finset.single_le_sum (f := fun b => |Lin b ω - TB L b ω|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ b)
        linarith [abs_nonneg (Q ω - TQ L ω)]
    have h3 : |F (TQ L ω, fun b => TB L b ω) - F (Q ω, fun b => Lin b ω)| ≤
        K * (|Q ω - TQ L ω| + ∑ b, |Lin b ω - TB L b ω|) := by
      rw [← Real.dist_eq]; exact h1.trans (mul_le_mul_of_nonneg_left h2 K.2)
    rw [Real.enorm_eq_ofReal_abs]
    calc ENNReal.ofReal |F (TQ L ω, fun b => TB L b ω) - F (Q ω, fun b => Lin b ω)|
        ≤ ENNReal.ofReal (K * (|Q ω - TQ L ω| + ∑ b, |Lin b ω - TB L b ω|)) :=
          ENNReal.ofReal_le_ofReal h3
      _ = ENNReal.ofReal K * (‖Q ω - TQ L ω‖ₑ + ∑ b, ‖Lin b ω - TB L b ω‖ₑ) := by
          rw [ENNReal.ofReal_mul (NNReal.coe_nonneg K), ENNReal.ofReal_add (abs_nonneg _)
            (Finset.sum_nonneg fun _ _ => abs_nonneg _), ENNReal.ofReal_sum_of_nonneg
            (fun _ _ => abs_nonneg _)]
          simp [Real.enorm_eq_ofReal_abs]
  have hQ1 := q08_tendsto_lintegral_enorm P (fun L ω => Q ω - TQ L ω)
    (fun L => hQm.sub (hTQm L)) hQ
  have hL1 : ∀ b, Tendsto (fun L => ∫⁻ ω, ‖Lin b ω - TB L b ω‖ₑ ∂P) atTop (𝓝 0) := fun b =>
    q08_tendsto_lintegral_enorm P (fun L ω => Lin b ω - TB L b ω) (fun L => (hLm b).sub (hTBm L b))
      (hLin b)
  have hbound : Tendsto (fun L => ENNReal.ofReal K * (∫⁻ ω, ‖Q ω - TQ L ω‖ₑ ∂P +
      ∑ b, ∫⁻ ω, ‖Lin b ω - TB L b ω‖ₑ ∂P)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal K)
      (hQ1.add (tendsto_finsetSum (Finset.univ : Finset (Fin p)) fun b _ => hL1 b)) (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  refine tendsto_integral_of_L1 _ (hint _ hT0).aestronglyMeasurable (Eventually.of_forall fun L => hint _ (hTm L)) ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound (fun L => bot_le)
    (fun L => ?_)
  calc ∫⁻ ω, ‖F (TQ L ω, fun b => TB L b ω) - F (Q ω, fun b => Lin b ω)‖ₑ ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal K * (‖Q ω - TQ L ω‖ₑ + ∑ b, ‖Lin b ω - TB L b ω‖ₑ) ∂P :=
        lintegral_mono (hpt L)
    _ = ENNReal.ofReal K * (∫⁻ ω, ‖Q ω - TQ L ω‖ₑ ∂P + ∑ b, ∫⁻ ω, ‖Lin b ω - TB L b ω‖ₑ ∂P) := by
        have hm : Measurable (fun ω => ‖Q ω - TQ L ω‖ₑ) := (hQm.sub (hTQm L)).enorm
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hm,
          lintegral_finsetSum]
        intro b _
        exact ((hLm b).sub (hTBm L b)).enorm


/-- Convergence of integrals of bounded Lipschitz functions implies convergence of integrals of bounded
continuous functions (Portmanteau, via Mathlib's `ProbabilityMeasure` topology). -/
theorem q08_upgrade {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {X : ℕ → Type*} [∀ N, MeasurableSpace (X N)] (ν : ∀ N, Measure (X N))
    (hν : ∀ N, 1 ≤ N → IsProbabilityMeasure (ν N)) (T : ∀ N, X N → E) (hT : ∀ N, Measurable (T N))
    (lam : Measure E) [IsProbabilityMeasure lam]
    (hlip : ∀ F : E → ℝ, (∃ M, ∀ z, |F z| ≤ M) → (∃ K, LipschitzWith K F) →
      Tendsto (fun N => ∫ x, F (T N x) ∂(ν N)) atTop (𝓝 (∫ z, F z ∂lam)))
    (F : E → ℝ) (hFc : Continuous F) (hFb : ∃ M, ∀ z, |F z| ≤ M) :
    Tendsto (fun N => ∫ x, F (T N x) ∂(ν N)) atTop (𝓝 (∫ z, F z ∂lam)) := by
  have hprob : ∀ n : ℕ, IsProbabilityMeasure ((ν (n + 1)).map (T (n + 1))) := fun n => by
    have := hν (n + 1) (by omega)
    exact (Measure.isProbabilityMeasure_map_iff (hT (n + 1)).aemeasurable).2 inferInstance
  let μs : ℕ → ProbabilityMeasure E := fun n => ⟨(ν (n + 1)).map (T (n + 1)), hprob n⟩
  let L0 : ProbabilityMeasure E := ⟨lam, inferInstance⟩
  have hint : ∀ (n : ℕ) (f : E → ℝ), Continuous f → ∫ z, f z ∂(μs n : Measure E) =
      ∫ x, f (T (n + 1) x) ∂(ν (n + 1)) := fun n f hf => by
    show ∫ z, f z ∂((ν (n + 1)).map (T (n + 1))) = _
    exact integral_map (hT (n + 1)).aemeasurable hf.aestronglyMeasurable
  have hlim : Tendsto μs atTop (𝓝 L0) := by
    rw [tendsto_iff_forall_lipschitz_integral_tendsto]
    intro f hfb hfl
    obtain ⟨K, hK⟩ := hfl
    obtain ⟨C, hC⟩ := hfb
    have hb : ∃ M, ∀ z, |f z| ≤ M := by
      by_cases hE : Nonempty E
      · obtain ⟨z0⟩ := hE
        refine ⟨|f z0| + C, fun z => ?_⟩
        have := hC z z0
        rw [Real.dist_eq] at this
        have h2 : |f z| ≤ |f z0| + |f z - f z0| := by
          have := abs_sub_abs_le_abs_sub (f z) (f z0)
          linarith
        linarith
      · exact ⟨0, fun z => (hE ⟨z⟩).elim⟩
    simp_rw [hint _ _ hK.continuous]
    exact (tendsto_add_atTop_iff_nat 1).2 (hlip f hb ⟨K, hK⟩)
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hlim
  obtain ⟨M, hM⟩ := hFb
  let f' : BoundedContinuousFunction E ℝ := BoundedContinuousFunction.ofNormedAddCommGroup F hFc M
    (fun z => by simpa [Real.norm_eq_abs] using hM z)
  have := hlim f'
  simp_rw [show ∀ n, ∫ z, f' z ∂(μs n : Measure E) = ∫ x, F (T (n + 1) x) ∂(ν (n + 1)) from fun n =>
    hint n f' f'.continuous] at this
  exact (tendsto_add_atTop_iff_nat 1).1 this


/-! ### The intermediate layer and the assembly -/

variable {d : ℕ} (D : Q08Data d)

/-- The pair `(B_N(h), ζ_N(φ))` of the conclusion of Lemma 7.5 (`B_N` exactly centred under `Q_{N,β}`, the
linear statistics centred at the Gibbs first marginal `m_N`). -/
def q08Stat (N : ℕ) (X : Config d N) : ℝ × (Fin D.p → ℝ) :=
  ((N : ℝ) * (modulatedEnergy D.h X D.μ - ∫ Y, modulatedEnergy D.h Y D.μ ∂(D.Gibbs N)),
    fun a => Real.sqrt N * ((1 / (N : ℝ)) * ∑ i, D.φ a (X i) - pair (firstMarginal (D.Gibbs N)) (D.φ a)))

/-- The finite-dimensional Wick chaos functional `E F(½ ∑_{i,j<L} H_ij (G_iG_j - C_ij), (∑_{i<L} a_{ai} G_i)_a)`
for `(G_i)_{i<L} ~ N(0, C|_{L×L})`. -/
def q08FiniteChaos (L : ℕ) (F : ℝ × (Fin D.p → ℝ) → ℝ) : ℝ :=
  ∫ g : EuclideanSpace ℝ (Fin L),
    F ((1 / 2) * ∑ i : Fin L, ∑ j : Fin L, D.Hmat i j * (g i * g j - D.Cmat i j),
      fun b => ∑ i : Fin L, D.coef b i * g i)
    ∂(multivariateGaussian 0 (Matrix.of fun i j : Fin L => D.Cmat i j))

/-- **Intermediate layer** (the finite-rank approximation theorem, the heart of Lemma 7.5; to be proved
from `Spectral`, `Features` and the `Chaos` bound, see the route below): for bounded Lipschitz `F`, the law
of `(B_N, ζ_N)` under `Q_{N,β}` is within `ε` of the finite-rank Wick chaos functional `q08FiniteChaos D L`
for all large `L` and then all large `N`.

Route: (1) `q08_bounded_family` gives bounded orthonormal centred `u_{<L}`, with finite-rank (projected)
kernels `g^U, h^U` and test-coefficients within `ε` in `L²`; (2) by `q08_weight_Lq` and `q08_energy_L2`
(Hölder, `w_N ∈ L^3`, `L²` closeness of the statistics under `μ^{⊗N}`) one may replace the statistics and the
Gibbs weight by the finite-rank ones `½(SᵀH^U S - tr H^U)`, `S^N = N^{-1/2} ∑_k u(X_k)`, with
`e^{-(β/2)(SᵀK^U S - tr K^U)}`, up to `O(ε)` uniformly in `N` (the diagonal terms `(1/N)∑_k u(X_k)ᵀ K u(X_k)`
converge by the LLN, `u` bounded); the exact centring of `B_N` under `Q_N` passes to the limit because the `L²`
errors are controlled under `Q_N` by Cauchy-Schwarz with `w_N ∈ L²`; (3) `q08_clt_quadratic` gives the
`N → ∞` limit as an integral against `N(0, I_L)`, `q08_gauss_tilt` turns the tilt into `N(0, (I+βK^U)^{-1})`;
(4) the resolvent identity of `q08_Cmat_spec` and `‖K - K^U‖_{HS} ≤ ε` give `‖(I+βK^U)^{-1} - C‖ ≲ βε`, and
`q08_chaos_l2_bound` (basis change from `u` to `e`) gives closeness to `q08FiniteChaos D L` for `L` large. -/
theorem q08_gibbs_approx (F : ℝ × (Fin D.p → ℝ) → ℝ) (hb : ∃ M, ∀ z, |F z| ≤ M)
    (hl : ∃ K : ℝ≥0, LipschitzWith K F) (ε : ℝ) (hε : 0 < ε) :
    ∃ L0 : ℕ, ∀ L ≥ L0, ∀ᶠ N in atTop,
      |∫ X, F (q08Stat D N X) ∂(D.Gibbs N) - q08FiniteChaos D L F| ≤ ε :=
  q08gl_final D F hb hl ε hε

theorem q08_measurable_stat (N : ℕ) : Measurable (q08Stat D N) := by
  refine Measurable.prodMk ?_ (measurable_pi_iff.2 fun a => ?_)
  · exact measurable_const.mul ((q08_measurable_energy D N).sub measurable_const)
  · refine measurable_const.mul ?_
    refine Measurable.sub (measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)) measurable_const
    exact (D.hφ a).1.comp (measurable_pi_apply i)

end HRS.Q08

namespace HRS

open Q08 in
/-- Lemma 7.5 `M:N:lem:quadratic-limit` (statement verbatim as `HRS.quadratic_limit`), proved from the
Q08 skeleton lemmas (`HRS/Equilibrium/QuadraticLimit/*`). -/
theorem quadratic_limit_proof {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (β : ℝ)
    (hβ : 0 < β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c : ℝ)
    (hc : ∀ z, z ≠ 0 → 1 ≤ periodicRiesz d s z + c) (B : ℝ) (h : Torus d → Torus d → ℝ)
    (hmeas : Measurable (Function.uncurry h)) (hsymm : ∀ x y, h x y = h y x)
    (hB : ∀ x y, x ≠ y → |h x y| ≤ B * (periodicRiesz d s (x - y) + c))
    (e : ℕ → Torus d → ℝ) (he : IsONBL2Zero (withDensityReal ρ) e)
    (p : ℕ) (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Measurable (φ a) ∧ ∃ M, ∀ x, |φ a x| ≤ M) :
    (∀ N : ℕ, 1 ≤ N → Integrable (fun X : Config d N => modulatedEnergy h X (withDensityReal ρ))
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))) ∧
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (G : ℕ → Ω → ℝ) (Q : Ω → ℝ) (Lin : Fin p → Ω → ℝ),
      (∀ n : ℕ, law P (fun ω => (WithLp.toLp 2 fun i : Fin n => G i ω : EuclideanSpace ℝ (Fin n))) =
        multivariateGaussian 0 (Matrix.of fun i j : Fin n =>
          susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j))) ∧
      (∀ a, Tendsto (fun L => ∫⁻ ω, ‖Lin a ω - ∑ i ∈ Finset.range L,
          l2Inner (withDensityReal ρ) (φ a) (e i) * G i ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)) ∧
      Tendsto (fun L => ∫⁻ ω, ‖Q ω - (1 / 2) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
          (∫ x, ∫ y, h x y * e i x * e j y ∂(withDensityReal ρ) ∂(withDensityReal ρ)) *
            (G i ω * G j ω -
              susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j))‖ₑ ^ 2 ∂P)
        atTop (𝓝 0) ∧
      ∀ F : ℝ × (Fin p → ℝ) → ℝ, Continuous F → (∃ M, ∀ z, |F z| ≤ M) →
        Tendsto (fun N : ℕ => ∫ X, F ((N : ℝ) * (modulatedEnergy h X (withDensityReal ρ) -
              ∫ Y, modulatedEnergy h Y (withDensityReal ρ)
                ∂(modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))),
            fun a => Real.sqrt N * ((1 / (N : ℝ)) * ∑ i, φ a (X i) -
              pair (firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)))
                (φ a)))
            ∂(modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))) atTop
          (𝓝 (∫ ω, F (Q ω, fun a => Lin a ω) ∂P)) := by
  let D : Q08Data d := ⟨s, β, ρ, c, B, h, e, p, φ, hd, hs0, hs, hβ, hρ, hc, hmeas, hsymm, hB, he, hφ⟩
  obtain ⟨hCs, hCp, hCle, hCres⟩ := q08_Cmat_spec D
  obtain ⟨hHs, hHsum⟩ := q08_Hmat_spec D
  have hC : q08_IsCov D.Cmat := ⟨hCs, hCp, hCle⟩
  obtain ⟨Ω, mΩ, P, hP, G, Q, Lin, hGm, hQm, hLm, hlaw, hLin, hQ⟩ :=
    q08_chaos_exists D.Cmat D.Hmat D.coef hC hHs hHsum (q08_coef_summable D)
  refine ⟨fun N hN => q08_integrable_energy D N hN, Ω, mΩ, P, hP, G, Q, Lin, hlaw, hLin, hQ, ?_⟩
  intro F hFc hFb
  have hT0 : Measurable (fun ω => (Q ω, fun a => Lin a ω)) :=
    hQm.prodMk (measurable_pi_iff.2 fun a => hLm a)
  let lam : Measure (ℝ × (Fin p → ℝ)) := P.map (fun ω => (Q ω, fun a => Lin a ω))
  have : IsProbabilityMeasure lam := (Measure.isProbabilityMeasure_map_iff hT0.aemeasurable).2 hP
  have hint : ∀ F' : ℝ × (Fin p → ℝ) → ℝ, Continuous F' →
      ∫ z, F' z ∂lam = ∫ ω, F' (Q ω, fun a => Lin a ω) ∂P := fun F' hF' =>
    integral_map hT0.aemeasurable hF'.aestronglyMeasurable
  have hlip : ∀ F' : ℝ × (Fin p → ℝ) → ℝ, (∃ M, ∀ z, |F' z| ≤ M) → (∃ K : ℝ≥0, LipschitzWith K F') →
      Tendsto (fun N => ∫ X, F' (q08Stat D N X) ∂(D.Gibbs N)) atTop (𝓝 (∫ z, F' z ∂lam)) := by
    intro F' hb hl
    obtain ⟨M, hM⟩ := hb
    obtain ⟨K, hK⟩ := hl
    rw [hint F' hK.continuous]
    have A : Tendsto (fun L => q08FiniteChaos D L F') atTop
        (𝓝 (∫ ω, F' (Q ω, fun a => Lin a ω) ∂P)) :=
      q08_finiteChaos_tendsto P D.Cmat D.Hmat D.coef G Q Lin hGm hQm hLm hlaw hLin hQ F' M hM K hK
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨L1, hL1⟩ := Metric.tendsto_atTop.1 A (ε / 2) (by linarith)
    obtain ⟨L0, hL0⟩ := q08_gibbs_approx D F' ⟨M, hM⟩ ⟨K, hK⟩ (ε / 2) (by linarith)
    obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hL0 (max L0 L1) (le_max_left _ _))
    refine ⟨N0, fun N hN => ?_⟩
    have h1 := hN0 N hN
    have h2 := hL1 (max L0 L1) (le_max_right _ _)
    rw [Real.dist_eq] at h2 ⊢
    calc |∫ X, F' (q08Stat D N X) ∂(D.Gibbs N) - ∫ ω, F' (Q ω, fun a => Lin a ω) ∂P|
        ≤ |∫ X, F' (q08Stat D N X) ∂(D.Gibbs N) - q08FiniteChaos D (max L0 L1) F'| +
          |q08FiniteChaos D (max L0 L1) F' - ∫ ω, F' (Q ω, fun a => Lin a ω) ∂P| :=
          abs_sub_le _ _ _
      _ < ε := by linarith
  have main := q08_upgrade (X := fun N => Config d N) (fun N => D.Gibbs N)
    (fun N hN => q08_gibbs_isProb D N hN) (fun N => q08Stat D N) (q08_measurable_stat D) lam hlip
    F hFc hFb
  rw [hint F hFc] at main
  exact main

example := (@quadratic_limit_proof : type_of% @quadratic_limit)

end HRS

end
