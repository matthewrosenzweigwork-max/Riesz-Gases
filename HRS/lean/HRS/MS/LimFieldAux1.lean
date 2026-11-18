import HRS.Whole.AppendixBField
import HRS.MP.HNegInfra
import HRS.Prob.HilbertCLT
import HRS.Main.A33Aux1
import HRS.MS.SuppU10a
import HRS.MS.SuppU10aAux1
import HRS.MS.SuppU10aAux2

/-!
# SB7, part 1: the noise process of the whole-space limit field (existence half of
`limit_field_rd_duality`)

Infrastructure lemmas (prefix `sb7_`) for S.B.7(iii)(a).  Contents:

* `sb7_isonormal_hs`: a Hilbert-Schmidt image `Λ u` of an isonormal process `W` on `𝓗` has an
  `E`-valued measurable version `G` (`⟪u, G⟫ = W(Λ u)` a.s. for every `u`), `E` a separable Hilbert space;
* `sb7_Lam`: the operator `u ↦ c • [a ↦ (⟨k_j(a), u⟩)_j] ∈ L²(μ; ℝ^d)` of a bounded kernel family, with
  its Gram form and Hilbert-Schmidt property;
* `sb7_exists_noise`: on one probability space there are measurable `G_t : Ω₀ → H^{-Γ}` (`t ∈ ℝ`) whose
  pairings with smooth tests have, for every finite family of times and tests, the Gaussian law with the
  covariance `noiseCovW`; this is `G_t = √(2q) ∫_0^t K^{r,t} dW_r`.
-/
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace HRS.MS.U10

section IsoHS

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {𝓗 : Type} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]
variable {Ω : Type} [MeasurableSpace Ω] {Q : Measure Ω} {W : 𝓗 → Ω → ℝ}

/-- The properties of an isonormal process used here. -/
structure Sb7Iso (Q : Measure Ω) (W : 𝓗 → Ω → ℝ) : Prop where
  meas : ∀ h, Measurable (W h)
  memLp : ∀ h, MemLp (W h) 2 Q
  lin : ∀ (a c : ℝ) (h h' : 𝓗), W (a • h + c • h') =ᵐ[Q] fun ω => a * W h ω + c * W h' ω
  inner : ∀ h h', ∫ ω, W h ω * W h' ω ∂Q = inner ℝ h h'

theorem Sb7Iso.sq_sub [IsProbabilityMeasure Q] (hI : Sb7Iso Q W) (a b : 𝓗) :
    ∫ ω, (W a ω - W b ω) ^ 2 ∂Q = ‖a - b‖ ^ 2 := by
  have h1 : W (a - b) =ᵐ[Q] fun ω => W a ω - W b ω := by
    have := hI.lin 1 (-1) a b
    filter_upwards [this] with ω h
    simpa [sub_eq_add_neg] using h
  have h2 : ∫ ω, (W a ω - W b ω) ^ 2 ∂Q = ∫ ω, W (a - b) ω * W (a - b) ω ∂Q := by
    refine integral_congr_ae ?_
    filter_upwards [h1] with ω h
    rw [h, sq]
  rw [h2, hI.inner, real_inner_self_eq_norm_sq]

theorem Sb7Iso.zero [IsProbabilityMeasure Q] (hI : Sb7Iso Q W) : W 0 =ᵐ[Q] fun _ => 0 := by
  have := hI.lin 0 0 0 0
  simpa using this

theorem Sb7Iso.sum [IsProbabilityMeasure Q] (hI : Sb7Iso Q W) {κ : Type*} (v : κ → 𝓗)
    (c : κ → ℝ) (F : Finset κ) :
    W (∑ i ∈ F, c i • v i) =ᵐ[Q] fun ω => ∑ i ∈ F, c i * W (v i) ω := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using hI.zero
  | insert a F ha ih =>
    rw [Finset.sum_insert ha]
    have hl := hI.lin (c a) 1 (v a) (∑ i ∈ F, c i • v i)
    simp only [one_smul] at hl
    filter_upwards [hl, ih] with ω h1 h2
    rw [h1, h2, Finset.sum_insert ha]
    simp

theorem sb7_tendstoInMeasure_of_L2 [IsProbabilityMeasure Q] (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hf : ∀ n, MemLp (f n) 2 Q) (hg : MemLp g 2 Q)
    (h : Tendsto (fun n => ∫ ω, (f n ω - g ω) ^ 2 ∂Q) atTop (𝓝 0)) :
    TendstoInMeasure Q f atTop g := by
  refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_
  have e : ∀ n, eLpNorm (f n - g) 2 Q =
      ENNReal.ofReal ((∫ ω, (f n ω - g ω) ^ 2 ∂Q) ^ (1 / 2 : ℝ)) := by
    intro n
    rw [(show MemLp (f n - g) 2 Q from (hf n).sub hg).eLpNorm_eq_integral_rpow_norm (by norm_num)
      (by norm_num)]
    congr 2
    · refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp [Real.rpow_two, sq_abs]
    · norm_num
  simp_rw [e]
  have h2 : Tendsto (fun n => (∫ ω, (f n ω - g ω) ^ 2 ∂Q) ^ (1 / 2 : ℝ)) atTop
      (𝓝 (0 ^ (1 / 2 : ℝ))) :=
    h.rpow_const (Or.inr (by norm_num))
  rw [Real.zero_rpow (by norm_num)] at h2
  simpa using ENNReal.tendsto_ofReal h2

/-- A Hilbert-Schmidt image of an isonormal process has an `E`-valued version: if `Λ : E → 𝓗` is
bounded with `∑ ‖Λ b_i‖² < ∞` on a Hilbert basis `b`, there is a measurable `G : Ω → E` with
`⟪u, G⟫ = W(Λ u)` a.s. for every `u`. -/
theorem sb7_isonormal_hs [IsProbabilityMeasure Q] (hI : Sb7Iso Q W)
    (Λ : E →L[ℝ] 𝓗) {ι : Type} [Countable ι] (b : HilbertBasis ι ℝ E)
    (hHS : Summable fun i => ‖Λ (b i)‖ ^ 2) :
    ∃ G : Ω → E, Measurable G ∧ ∀ u : E, (fun ω => inner ℝ u (G ω)) =ᵐ[Q] W (Λ u) := by
  classical
  set ξ : ι → Ω → ℝ := fun i => W (Λ (b i)) with hξ
  have hξm : ∀ i, Measurable (ξ i) := fun i => hI.meas _
  have hξ2 : ∀ i, ∫ ω, ξ i ω ^ 2 ∂Q = ‖Λ (b i)‖ ^ 2 := by
    intro i
    have := hI.inner (Λ (b i)) (Λ (b i))
    rw [real_inner_self_eq_norm_sq] at this
    simpa [sq] using this
  have hξint : ∀ i, Integrable (fun ω => ξ i ω ^ 2) Q := fun i =>
    (hI.memLp (Λ (b i))).integrable_sq
  -- the a.s. finiteness of `∑ ξ_i²`
  let Good : Set Ω := {ω | ∑' i, ENNReal.ofReal (ξ i ω ^ 2) < ∞}
  have hSm : Measurable fun ω => ∑' i, ENNReal.ofReal (ξ i ω ^ 2) :=
    Measurable.ennreal_tsum fun i => ENNReal.measurable_ofReal.comp ((hξm i).pow_const 2)
  have hGoodm : MeasurableSet Good := measurableSet_lt hSm measurable_const
  have hlint : ∫⁻ ω, ∑' i, ENNReal.ofReal (ξ i ω ^ 2) ∂Q < ∞ := by
    rw [lintegral_tsum (μ := Q) (f := fun i ω => ENNReal.ofReal (ξ i ω ^ 2))
      fun i => (ENNReal.measurable_ofReal.comp ((hξm i).pow_const 2)).aemeasurable]
    have : ∀ i, ∫⁻ ω, ENNReal.ofReal (ξ i ω ^ 2) ∂Q = ENNReal.ofReal (‖Λ (b i)‖ ^ 2) := by
      intro i
      rw [← ofReal_integral_eq_lintegral_ofReal (hξint i) (ae_of_all _ fun ω => sq_nonneg _),
        hξ2 i]
    simp_rw [this]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hHS]
    exact ENNReal.ofReal_lt_top
  have hGood : ∀ᵐ ω ∂Q, ω ∈ Good := ae_lt_top hSm hlint.ne
  have hsumm : ∀ ω ∈ Good, Summable fun i => ξ i ω ^ 2 := by
    intro ω hω
    have := ENNReal.summable_toReal (f := fun i => ENNReal.ofReal (ξ i ω ^ 2)) hω.ne
    simpa [ENNReal.toReal_ofReal (sq_nonneg _)] using this
  have hmem : ∀ ω ∈ Good, Memℓp (fun i => ξ i ω) 2 := by
    intro ω hω
    refine memℓp_gen ?_
    simpa [Real.norm_eq_abs, sq_abs, Real.rpow_two] using hsumm ω hω
  let Gf : Ω → E := fun ω => if h : ω ∈ Good then b.repr.symm ⟨fun i => ξ i ω, hmem ω h⟩ else 0
  have hGsum : ∀ ω ∈ Good, HasSum (fun i => ξ i ω • b i) (Gf ω) := by
    intro ω hω
    have := b.hasSum_repr_symm ⟨fun i => ξ i ω, hmem ω hω⟩
    simpa [Gf, hω] using this
  have hGmeas : Measurable Gf := by
    refine measurable_of_tendsto_metrizable' (atTop : Filter (Finset ι))
      (f := fun (F : Finset ι) ω => if ω ∈ Good then ∑ i ∈ F, ξ i ω • b i else 0)
      (fun F => Measurable.ite hGoodm (Finset.measurable_sum _ fun i _ => (hξm i).smul_const _)
        measurable_const) ?_
    rw [tendsto_pi_nhds]
    intro ω
    by_cases hω : ω ∈ Good
    · simp only [hω, if_true]
      exact hGsum ω hω
    · simp only [hω, if_false]
      have : Gf ω = 0 := by simp [Gf, hω]
      rw [this]
      exact tendsto_const_nhds
  refine ⟨Gf, hGmeas, fun u => ?_⟩
  set cu : ι → ℝ := fun i => inner ℝ (b i) u with hcu
  have hu : HasSum (fun i => cu i • b i) u := by
    have := b.hasSum_repr u
    simpa [HilbertBasis.repr_apply_apply, hcu] using this
  have hΛu : HasSum (fun i => cu i • Λ (b i)) (Λ u) := by
    have := (Λ.hasSum hu)
    simpa using this
  -- partial sums
  let S : Finset ι → Ω → ℝ := fun F ω => ∑ i ∈ F, cu i * ξ i ω
  have hSmem : ∀ F, MemLp (S F) 2 Q := fun F =>
    memLp_finset_sum (f := fun i ω => cu i * ξ i ω) F fun i _ => (hI.memLp (Λ (b i))).const_mul (cu i)
  have hSL2 : Tendsto (fun F : Finset ι => ∫ ω, (S F ω - W (Λ u) ω) ^ 2 ∂Q) atTop (𝓝 0) := by
    have h1 : Tendsto (fun F : Finset ι => ‖∑ i ∈ F, cu i • Λ (b i) - Λ u‖ ^ 2) atTop (𝓝 0) := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 hΛu)
      have h2 := ((continuous_pow 2).tendsto (0 : ℝ)).comp this
      simpa [Function.comp_def] using h2
    refine h1.congr fun F => ?_
    rw [← hI.sq_sub]
    refine integral_congr_ae ?_
    filter_upwards [hI.sum (fun i => Λ (b i)) cu F] with ω h
    show (W (∑ i ∈ F, cu i • Λ (b i)) ω - W (Λ u) ω) ^ 2 = (S F ω - W (Λ u) ω) ^ 2
    rw [h]
  obtain ⟨Fs, hFs⟩ := Filter.exists_seq_tendsto (atTop : Filter (Finset ι))
  have hae : ∀ᵐ ω ∂Q, Tendsto (fun n => S (Fs n) ω) atTop (𝓝 (inner ℝ u (Gf ω))) := by
    filter_upwards [hGood] with ω hω
    have h1 : HasSum (fun i => inner ℝ u (ξ i ω • b i)) (inner ℝ u (Gf ω)) :=
      (innerSL ℝ u).hasSum (hGsum ω hω)
    have h2 : (fun i => inner ℝ u (ξ i ω • b i)) = fun i => cu i * ξ i ω := by
      funext i
      rw [inner_smul_right, hcu, real_inner_comm, mul_comm]
    rw [h2] at h1
    exact h1.comp hFs
  have hm1 : TendstoInMeasure Q (fun n => S (Fs n)) atTop (fun ω => inner ℝ u (Gf ω)) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hSmem (Fs n)).aestronglyMeasurable) hae
  have hm2 : TendstoInMeasure Q (fun n => S (Fs n)) atTop (W (Λ u)) :=
    sb7_tendstoInMeasure_of_L2 _ _ (fun n => hSmem (Fs n)) (hI.memLp _) (hSL2.comp hFs)
  exact tendstoInMeasure_ae_unique hm1 hm2

end IsoHS

section KerOp

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {α : Type} [MeasurableSpace α] {d : ℕ}

/-- The `ℝ^d`-valued function `a ↦ (⟨k_j(a), u⟩)_j`. -/
def sb7_vec (k : α → Fin d → H) (u : H) (a : α) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun j => inner ℝ (k a j) u

theorem sb7_vec_measurable {μ : Measure α} {k : α → Fin d → H} {B : ℝ} (hk : U10Data μ k B)
    (u : H) : Measurable (sb7_vec k u) := by
  unfold sb7_vec
  exact (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable.comp
    (measurable_pi_iff.2 fun j => (hk.meas j).inner measurable_const)

theorem sb7_vec_norm_le {k : α → Fin d → H} {B : ℝ} {a : α} (ha : ∀ j, ‖k a j‖ ≤ B) (u : H) :
    ‖sb7_vec k u a‖ ^ 2 ≤ d * (B * ‖u‖) ^ 2 := by
  unfold sb7_vec
  rw [EuclideanSpace.norm_sq_eq]
  calc ∑ j, ‖inner ℝ (k a j) u‖ ^ 2 ≤ ∑ _j : Fin d, (B * ‖u‖) ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact pow_le_pow_left₀ (norm_nonneg _)
          ((norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (ha j) (norm_nonneg _))) 2
    _ = d * (B * ‖u‖) ^ 2 := by simp

theorem sb7_vec_memLp {μ : Measure α} [IsFiniteMeasure μ] {k : α → Fin d → H} {B : ℝ}
    (hk : U10Data μ k B) (u : H) : MemLp (sb7_vec k u) 2 μ := by
  refine MemLp.of_bound (sb7_vec_measurable hk u).aestronglyMeasurable (Real.sqrt (d * (B * ‖u‖) ^ 2)) ?_
  filter_upwards [hk.bound] with a ha
  exact Real.le_sqrt_of_sq_le (sb7_vec_norm_le ha u)

section Lam

variable {μ : Measure α} [IsFiniteMeasure μ] {k : α → Fin d → H} {B : ℝ}

/-- `u ↦ c • [a ↦ (⟨k_j(a), u⟩)_j] ∈ L²(μ; ℝ^d)`. -/
def sb7_lamFun (hk : U10Data μ k B) (c : ℝ) (u : H) : Lp (EuclideanSpace ℝ (Fin d)) 2 μ :=
  ((sb7_vec_memLp hk u).const_smul c).toLp (c • sb7_vec k u)

theorem sb7_lamFun_ae (hk : U10Data μ k B) (c : ℝ) (u : H) :
    (sb7_lamFun hk c u : α → EuclideanSpace ℝ (Fin d)) =ᵐ[μ] c • sb7_vec k u :=
  MemLp.coeFn_toLp _

theorem sb7_lamFun_add (hk : U10Data μ k B) (c : ℝ) (u v : H) :
    sb7_lamFun hk c (u + v) = sb7_lamFun hk c u + sb7_lamFun hk c v := by
  refine Lp.ext ?_
  filter_upwards [sb7_lamFun_ae hk c (u + v), Lp.coeFn_add (sb7_lamFun hk c u) (sb7_lamFun hk c v),
    sb7_lamFun_ae hk c u, sb7_lamFun_ae hk c v] with a h1 h2 h3 h4
  rw [h1, h2]
  simp only [Pi.smul_apply, Pi.add_apply, h3, h4]
  ext j
  simp [sb7_vec, inner_add_right, mul_add]

theorem sb7_lamFun_smul (hk : U10Data μ k B) (c r : ℝ) (u : H) :
    sb7_lamFun hk c (r • u) = r • sb7_lamFun hk c u := by
  refine Lp.ext ?_
  filter_upwards [sb7_lamFun_ae hk c (r • u), Lp.coeFn_smul r (sb7_lamFun hk c u),
    sb7_lamFun_ae hk c u] with a h1 h2 h3
  rw [h1, h2]
  simp only [Pi.smul_apply, h3]
  ext j
  simp [sb7_vec, inner_smul_right]
  ring

theorem sb7_lamFun_inner (hk : U10Data μ k B) (c : ℝ) (u v : H) :
    inner ℝ (sb7_lamFun hk c u) (sb7_lamFun hk c v) = c ^ 2 * ∫ a, u10_S k u v a ∂μ := by
  rw [MeasureTheory.L2.inner_def, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [sb7_lamFun_ae hk c u, sb7_lamFun_ae hk c v] with a h1 h2
  rw [h1, h2]
  simp only [Pi.smul_apply, PiLp.inner_apply, u10_S, sb7_vec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mul_comm, mul_left_comm]
  ring

theorem sb7_lamFun_norm_le (hk : U10Data μ k B) (c : ℝ) (u : H) :
    ‖sb7_lamFun hk c u‖ ≤ Real.sqrt (c ^ 2 * (d * B ^ 2) * μ.real Set.univ) * ‖u‖ := by
  have h1 : ‖sb7_lamFun hk c u‖ ^ 2 = c ^ 2 * ∫ a, u10_S k u u a ∂μ := by
    rw [← real_inner_self_eq_norm_sq, sb7_lamFun_inner]
  have h2 := norm_integral_le_of_norm_le_const (μ := μ) (u10_S_bound hk u u)
  have h3 : ∫ a, u10_S k u u a ∂μ ≤ Fintype.card (Fin d) * (B ^ 2 * ‖u‖ * ‖u‖) * μ.real Set.univ :=
    (le_abs_self _).trans (by simpa using h2)
  have h4 : ‖sb7_lamFun hk c u‖ ^ 2 ≤ (Real.sqrt (c ^ 2 * (d * B ^ 2) * μ.real Set.univ) * ‖u‖) ^ 2 := by
    rw [h1, mul_pow, Real.sq_sqrt (by positivity)]
    simp only [Fintype.card_fin] at h3
    calc c ^ 2 * ∫ a, u10_S k u u a ∂μ ≤ c ^ 2 * (d * (B ^ 2 * ‖u‖ * ‖u‖) * μ.real Set.univ) :=
          mul_le_mul_of_nonneg_left h3 (sq_nonneg c)
      _ = _ := by ring
  exact le_of_sq_le_sq (by simpa using h4) (by positivity)

/-- The bounded operator `u ↦ c • [a ↦ (⟨k_j(a), u⟩)_j]` from `H` to `L²(μ; ℝ^d)`. -/
def sb7_Lam (hk : U10Data μ k B) (c : ℝ) : H →L[ℝ] Lp (EuclideanSpace ℝ (Fin d)) 2 μ :=
  LinearMap.mkContinuous
    { toFun := sb7_lamFun hk c
      map_add' := sb7_lamFun_add hk c
      map_smul' := fun r u => by simpa using sb7_lamFun_smul hk c r u }
    (Real.sqrt (c ^ 2 * (d * B ^ 2) * μ.real Set.univ)) (sb7_lamFun_norm_le hk c)

theorem sb7_Lam_apply (hk : U10Data μ k B) (c : ℝ) (u : H) :
    sb7_Lam hk c u = sb7_lamFun hk c u := rfl

theorem sb7_Lam_inner (hk : U10Data μ k B) (c : ℝ) (u v : H) :
    inner ℝ (sb7_Lam hk c u) (sb7_Lam hk c v) = c ^ 2 * ∫ a, u10_S k u v a ∂μ :=
  sb7_lamFun_inner hk c u v

theorem sb7_Lam_hs (hk : U10Data μ k B) (c : ℝ) {ι : Type} [Countable ι]
    (b : HilbertBasis ι ℝ H) : Summable fun i => ‖sb7_Lam hk c (b i)‖ ^ 2 := by
  have h := ((u10_hasSum_trace hk b).mul_left (c ^ 2)).summable
  refine h.congr fun i => ?_
  rw [← real_inner_self_eq_norm_sq, sb7_Lam_inner]

end Lam

section Lam2

variable {μ : Measure α} [IsFiniteMeasure μ]

/-- The cross integrand `∑_j ⟨k¹_j, u⟩⟨k²_j, v⟩`. -/
def sb7_S2 (k₁ k₂ : α → Fin d → H) (u v : H) (a : α) : ℝ :=
  ∑ j, inner ℝ (k₁ a j) u * inner ℝ (k₂ a j) v

theorem sb7_lamFun_inner₂ {k₁ k₂ : α → Fin d → H} {B₁ B₂ : ℝ} (hk₁ : U10Data μ k₁ B₁)
    (hk₂ : U10Data μ k₂ B₂) (c : ℝ) (u v : H) :
    inner ℝ (sb7_lamFun hk₁ c u) (sb7_lamFun hk₂ c v) = c ^ 2 * ∫ a, sb7_S2 k₁ k₂ u v a ∂μ := by
  rw [MeasureTheory.L2.inner_def, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [sb7_lamFun_ae hk₁ c u, sb7_lamFun_ae hk₂ c v] with a h1 h2
  rw [h1, h2]
  simp only [Pi.smul_apply, PiLp.inner_apply, sb7_S2, sb7_vec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mul_comm, mul_left_comm]
  ring

theorem sb7_S2_bound_pt {k₁ k₂ : α → Fin d → H} {B : ℝ} {a : α} (h₁ : ∀ j, ‖k₁ a j‖ ≤ B)
    (h₂ : ∀ j, ‖k₂ a j‖ ≤ B) (u v : H) :
    ‖sb7_S2 k₁ k₂ u v a‖ ≤ d * (B ^ 2 * ‖u‖ * ‖v‖) := by
  unfold sb7_S2
  refine (norm_sum_le _ _).trans ?_
  have : ∀ j, ‖inner ℝ (k₁ a j) u * inner ℝ (k₂ a j) v‖ ≤ B ^ 2 * ‖u‖ * ‖v‖ := by
    intro j
    rw [norm_mul]
    have e1 : ‖inner ℝ (k₁ a j) u‖ ≤ B * ‖u‖ :=
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (h₁ j) (norm_nonneg _))
    have e2 : ‖inner ℝ (k₂ a j) v‖ ≤ B * ‖v‖ :=
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (h₂ j) (norm_nonneg _))
    calc ‖inner ℝ (k₁ a j) u‖ * ‖inner ℝ (k₂ a j) v‖ ≤ (B * ‖u‖) * (B * ‖v‖) :=
          mul_le_mul e1 e2 (norm_nonneg _) ((norm_nonneg _).trans e1)
      _ = B ^ 2 * ‖u‖ * ‖v‖ := by ring
  calc ∑ j, ‖inner ℝ (k₁ a j) u * inner ℝ (k₂ a j) v‖ ≤ ∑ _j : Fin d, B ^ 2 * ‖u‖ * ‖v‖ :=
        Finset.sum_le_sum fun j _ => this j
    _ = d * (B ^ 2 * ‖u‖ * ‖v‖) := by simp

theorem sb7_S2_measurable {k₁ k₂ : α → Fin d → H} {B₁ B₂ : ℝ} (hk₁ : U10Data μ k₁ B₁)
    (hk₂ : U10Data μ k₂ B₂) (u v : H) : Measurable (sb7_S2 k₁ k₂ u v) := by
  unfold sb7_S2
  exact Finset.measurable_sum _ fun j _ =>
    ((hk₁.meas j).inner measurable_const).mul ((hk₂.meas j).inner measurable_const)

end Lam2

end KerOp


/-! ### The whole-space noise process -/

section Noise

open HRS HRS.Whole HRS.MP.HNegInfra

variable {d : ℕ} {Γ : ℝ}

/-- The kernel family of time `t`: `K^{r,t}(x)_j` for `r ≤ t` and `0` for `r > t`. -/
def sb7_kt (Kern : ℝ → ℝ → Euc d → Fin d → HNeg d Γ) (t : ℝ) :
    ℝ × Euc d → Fin d → HNeg d Γ :=
  fun p j => if p.1 ≤ t then Kern p.1 t p.2 j else 0

theorem sb7_kt_data {C : WholeCoeff d} {T B : ℝ} (hT : 0 ≤ T)
    (Kern : ℝ → ℝ → Euc d → Fin d → HNeg d Γ) (hK : IsIntrinsicKernel Γ C T B Kern) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    U10Data (u10_mu d T C.ρ) (sb7_kt Kern t) B := by
  refine ⟨fun j => ?_, ?_⟩
  · refine Measurable.ite (measurableSet_le measurable_fst measurable_const) ?_ measurable_const
    exact (hK.measurable j).comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  · have h : ∀ᵐ p ∂(u10_m d T), ∀ j, ‖sb7_kt Kern t p j‖ ≤ B := by
      filter_upwards [u10_ae_mem (d := d) T] with p hp j
      unfold sb7_kt
      split_ifs with hle
      · exact hK.bound p.1 t hp.1 hle ht.2 p.2 j
      · rw [norm_zero]
        exact (norm_nonneg _).trans (hK.bound 0 0 le_rfl le_rfl hT 0 j)
    exact (withDensity_absolutelyContinuous _ _).ae_le h

theorem sb7_inner_kt {C : WholeCoeff d} {T B : ℝ} {Kern : ℝ → ℝ → Euc d → Fin d → HNeg d Γ}
    (hK : IsIntrinsicKernel Γ C T B Kern) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) {φ : Euc d → ℝ}
    (hφ : IsSobolevTest Γ φ) {g : HNeg d Γ} (hg : ∀ F : HNeg d Γ, inner ℝ g F = HNeg.pairing φ F)
    (r : ℝ) (hr : 0 ≤ r) (x : Euc d) (j : Fin d) :
    inner ℝ (sb7_kt Kern t (r, x) j) g =
      if r ≤ t then gradient (propagatorW C r t φ) x j else 0 := by
  unfold sb7_kt
  split_ifs with hle
  · rw [real_inner_comm, hg, hK.represent r t hr hle ht.2 x j φ hφ]
  · simp

/-- The Gram identity: the covariance of the pairings of the noise is `noiseCovW`. -/
theorem sb7_gram {C : WholeCoeff d} {q T B : ℝ} (hq : 0 ≤ q) (hT : 0 ≤ T)
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (C.ρ r))
    (hρm : Measurable (Function.uncurry C.ρ)) [IsFiniteMeasure (u10_mu d T C.ρ)]
    {Kern : ℝ → ℝ → Euc d → Fin d → HNeg d Γ} (hK : IsIntrinsicKernel Γ C T B Kern)
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) (ht : t ∈ Set.Icc (0 : ℝ) T) {φ ψ : Euc d → ℝ}
    (hφ : IsSobolevTest Γ φ) (hψ : IsSobolevTest Γ ψ) {g₁ g₂ : HNeg d Γ}
    (hg₁ : ∀ F : HNeg d Γ, inner ℝ g₁ F = HNeg.pairing φ F)
    (hg₂ : ∀ F : HNeg d Γ, inner ℝ g₂ F = HNeg.pairing ψ F) :
    inner ℝ (sb7_Lam (sb7_kt_data hT Kern hK hs) (Real.sqrt (2 * q)) g₁)
        (sb7_Lam (sb7_kt_data hT Kern hK ht) (Real.sqrt (2 * q)) g₂) = noiseCovW C q s t φ ψ := by
  have hk₁ := sb7_kt_data hT Kern hK hs
  have hk₂ := sb7_kt_data hT Kern hK ht
  rw [sb7_Lam_apply, sb7_Lam_apply, sb7_lamFun_inner₂, Real.sq_sqrt (by linarith)]
  unfold noiseCovW
  congr 1
  set m := min s t with hm
  have hmT : m ≤ T := (min_le_left _ _).trans hs.2
  -- the pointwise form of the integrand
  have hpt : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x : Euc d,
      sb7_S2 (sb7_kt Kern s) (sb7_kt Kern t) g₁ g₂ (r, x) =
        if r ≤ m then inner ℝ (gradient (propagatorW C r s φ) x) (gradient (propagatorW C r t ψ) x)
        else 0 := by
    intro r hr x
    unfold sb7_S2
    simp only [sb7_inner_kt hK hs hφ hg₁ r hr.1 x, sb7_inner_kt hK ht hψ hg₂ r hr.1 x]
    by_cases hrm : r ≤ m
    · have h1 : r ≤ s := hrm.trans (min_le_left _ _)
      have h2 : r ≤ t := hrm.trans (min_le_right _ _)
      simp only [hrm, h1, h2, if_true, PiLp.inner_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [mul_comm]
    · rw [if_neg hrm]
      have : ¬ (r ≤ s ∧ r ≤ t) := fun h => hrm (le_min h.1 h.2)
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases h1 : r ≤ s
      · have h2 : ¬ r ≤ t := fun h2 => this ⟨h1, h2⟩
        simp [h2]
      · simp [h1]
  have hgm : Measurable (sb7_S2 (sb7_kt Kern s) (sb7_kt Kern t) g₁ g₂) :=
    sb7_S2_measurable hk₁ hk₂ g₁ g₂
  have hgb : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x : Euc d,
      ‖sb7_S2 (sb7_kt Kern s) (sb7_kt Kern t) g₁ g₂ (r, x)‖ ≤ d * (B ^ 2 * ‖g₁‖ * ‖g₂‖) := by
    intro r hr x
    refine sb7_S2_bound_pt (fun j => ?_) (fun j => ?_) g₁ g₂
    · unfold sb7_kt
      split_ifs with hle
      · exact hK.bound r s hr.1 hle hs.2 x j
      · rw [norm_zero]; exact (norm_nonneg _).trans (hK.bound 0 0 le_rfl le_rfl hT 0 j)
    · unfold sb7_kt
      split_ifs with hle
      · exact hK.bound r t hr.1 hle ht.2 x j
      · rw [norm_zero]; exact (norm_nonneg _).trans (hK.bound 0 0 le_rfl le_rfl hT 0 j)
  rw [(u10_integral_eq hT hρ hρm hgm hgb).2]
  have h1 : ∀ r ∈ Set.Icc (0 : ℝ) T,
      ∫ x, sb7_S2 (sb7_kt Kern s) (sb7_kt Kern t) g₁ g₂ (r, x) * C.ρ r x =
        (Set.Icc (0 : ℝ) m).indicator (fun r => ∫ x, inner ℝ (gradient (propagatorW C r s φ) x)
          (gradient (propagatorW C r t ψ) x) * C.ρ r x) r := by
    intro r hr
    by_cases hrm : r ∈ Set.Icc (0 : ℝ) m
    · rw [Set.indicator_of_mem hrm]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [hpt r hr x, if_pos hrm.2]
    · rw [Set.indicator_of_notMem hrm]
      have : ¬ r ≤ m := fun h => hrm ⟨hr.1, h⟩
      simp [hpt r hr, this]
  rw [setIntegral_congr_fun measurableSet_Icc h1, setIntegral_indicator measurableSet_Icc,
    Set.inter_eq_right.2 (Set.Icc_subset_Icc_right hmT)]

/-- The noise process `G_t = √(2q) ∫_0^t K^{r,t} dW_r` of the limit field: on one probability space,
measurable `H^{-Γ}`-valued `G_t` whose pairings with smooth tests have, for every finite family of times in
`[0,T]` and tests, a vector version `V` (measurable, a.s. equal to the pairings) with the centered Gaussian
law of covariance `noiseCovW`. -/
theorem sb7_exists_noise {C : WholeCoeff d} {q T B : ℝ} (hq : 0 ≤ q) (hT : 0 ≤ T)
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (C.ρ r))
    (hρm : Measurable (Function.uncurry C.ρ))
    {Kern : ℝ → ℝ → Euc d → Fin d → HNeg d Γ} (hK : IsIntrinsicKernel Γ C T B Kern) :
    ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (Q : Measure Ω₀) (_ : IsProbabilityMeasure Q)
      (Gt : ℝ → Ω₀ → HNeg d Γ), (∀ t, Measurable (Gt t)) ∧
      ∀ (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ), (∀ a, ts a ∈ Set.Icc (0 : ℝ) T) →
        (∀ a, IsSobolevTest Γ (φ a)) →
        ∃ V : Ω₀ → EuclideanSpace ℝ (Fin p), Measurable V ∧
          (∀ a, ∀ᵐ w ∂Q, HNeg.pairing (φ a) (Gt (ts a) w) = V w a) ∧
          law Q V = multivariateGaussian 0
            (Matrix.of fun a b => noiseCovW C q (ts a) (ts b) (φ a) (φ b)) := by
  haveI := u10_isFinite hT hρ hρm
  obtain ⟨Ω₀, mΩ, Q, hQ, W, hWm, hW2, hWlin, -, hWinner, -, hWgauss⟩ :=
    HRS.A33.a33_isonormal (Lp (Euc d) 2 (u10_mu d T C.ρ))
  have hI : Sb7Iso Q W := ⟨hWm, hW2, hWlin, hWinner⟩
  obtain ⟨ι, hc, b, -⟩ := HRS.HilbertCLTAux.exists_hilbertBasis_type (H := HNeg d Γ)
  have hG : ∀ t : ℝ, ∃ G : Ω₀ → HNeg d Γ, Measurable G ∧
      ∀ ht : t ∈ Set.Icc (0 : ℝ) T, ∀ u : HNeg d Γ,
        (fun ω => inner ℝ u (G ω)) =ᵐ[Q]
          W (sb7_Lam (sb7_kt_data hT Kern hK ht) (Real.sqrt (2 * q)) u) := by
    intro t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) T
    · obtain ⟨G, hGm, hGp⟩ := sb7_isonormal_hs hI
        (sb7_Lam (sb7_kt_data hT Kern hK ht) (Real.sqrt (2 * q))) b
        (sb7_Lam_hs (sb7_kt_data hT Kern hK ht) _ b)
      exact ⟨G, hGm, fun _ => hGp⟩
    · exact ⟨fun _ => 0, measurable_const, fun h => absurd h ht⟩
  choose Gt hGm hGp using hG
  refine ⟨Ω₀, mΩ, Q, hQ, Gt, hGm, ?_⟩
  intro p ts φ hts hφ
  choose g hg using fun a => u10_riesz (hφ a)
  let h : Fin p → Lp (Euc d) 2 (u10_mu d T C.ρ) := fun a =>
    sb7_Lam (sb7_kt_data hT Kern hK (hts a)) (Real.sqrt (2 * q)) (g a)
  refine ⟨fun w => (WithLp.toLp 2 fun a => W (h a) w : EuclideanSpace ℝ (Fin p)), ?_, ?_, ?_⟩
  · exact (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp
      (measurable_pi_iff.2 fun a => hWm (h a))
  · intro a
    filter_upwards [hGp (ts a) (hts a) (g a)] with w hw
    rw [← hg a, hw]
  · have := hWgauss (Fin p) h
    show Q.map _ = _
    rw [this]
    congr 2
    funext a b
    exact sb7_gram hq hT hρ hρm hK (hts a) (hts b) (hφ a) (hφ b) (hg a) (hg b)

end Noise


/-! ### Product extension: independence for arbitrary (possibly non-measurable) first factors -/

/-- On a product measure, an arbitrary function of the first coordinate is independent of a
measurable function of the second (no measurability of the first function is needed: the outer
measure of a product of arbitrary sets is the product of the outer measures). -/
theorem sb7_indepFun_prod {Ω Ω' β β' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace β] [MeasurableSpace β'] (P : Measure Ω) (Q : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (F : Ω → β) {V : Ω' → β'}
    (hV : Measurable V) :
    IndepFun (fun z : Ω × Ω' => F z.1) (fun z => V z.2) (P.prod Q) := by
  rw [IndepFun_iff]
  rintro t1 t2 ⟨S, hS, rfl⟩ ⟨S', hS', rfl⟩
  have e1 : (fun z : Ω × Ω' => F z.1) ⁻¹' S = (F ⁻¹' S) ×ˢ (Set.univ : Set Ω') := by
    ext z; simp
  have e2 : (fun z : Ω × Ω' => V z.2) ⁻¹' S' = (Set.univ : Set Ω) ×ˢ (V ⁻¹' S') := by
    ext z; simp
  have e3 : ((fun z : Ω × Ω' => F z.1) ⁻¹' S) ∩ ((fun z : Ω × Ω' => V z.2) ⁻¹' S') =
      (F ⁻¹' S) ×ˢ (V ⁻¹' S') := by
    ext z; simp
  rw [e3, Measure.prod_prod, e1, e2, Measure.prod_prod, Measure.prod_prod]
  simp

theorem sb7_subsingleton_measure_eq {X : Type*} [MeasurableSpace X] [Subsingleton X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : μ = ν := by
  ext s hs
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  · have : s = Set.univ := by
      ext y; simp [Subsingleton.elim y x, hx]
    rw [this]; simp

/-! ### Existence half of `limit_field_rd_duality` -/

section Existence

open HRS HRS.Whole HRS.MP.HNegInfra

variable {d : ℕ} {Γ : ℝ}

theorem sb7_duality_exists {C : WholeCoeff d} {A q T B : ℝ} (hq : 0 ≤ q)
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (C.ρ r))
    (hρm : Measurable (Function.uncurry C.ρ))
    {Kern : ℝ → ℝ → Euc d → Fin d → HNeg d Γ} (hK : IsIntrinsicKernel Γ C T B Kern)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (η₀ : Ω → (Euc d → ℝ) → ℝ) (hη : HasTransportedField P C Γ A T η₀) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (π : Ω' → Ω) (Y : ℝ → Ω' → HNeg d Γ),
      MeasurePreserving π P' P ∧ IsAdjointDualityLimitW P' C Γ A q T (fun ζ' => η₀ (π ζ')) Y := by
  by_cases hT : 0 ≤ T
  · obtain ⟨Ω₀, mΩ₀, Q, hQ, Gt, hGm, hGp⟩ := sb7_exists_noise hq hT hρ hρm hK
    have hI : ∀ t : ℝ, ∃ I : Ω → HNeg d Γ, Measurable I ∧
        (t ∈ Set.Icc (0 : ℝ) T → ∀ φ : Euc d → ℝ, IsSobolevTest Γ φ →
          ∀ᵐ ζ ∂P, HNeg.pairing φ (I ζ) = A * η₀ ζ (propagatorW C 0 t φ)) := by
      intro t
      by_cases ht : t ∈ Set.Icc (0 : ℝ) T
      · obtain ⟨I, hIm, hIp⟩ := hη t ht
        exact ⟨I, hIm, fun _ => hIp⟩
      · exact ⟨fun _ => 0, measurable_const, fun h => absurd h ht⟩
    choose It hIm hIp using hI
    refine ⟨Ω × Ω₀, inferInstance, P.prod Q, inferInstance, Prod.fst,
      fun t z => It t z.1 + Gt t z.2, measurePreserving_fst, hρm, fun t => ?_, ?_⟩
    · exact ((hIm t).comp measurable_fst).add ((hGm t).comp measurable_snd)
    · intro p ts φ hts hφ
      obtain ⟨V, hVm, hVae, hVlaw⟩ := hGp p ts φ hts hφ
      have hae : (fun z : Ω × Ω₀ => (WithLp.toLp 2 fun a =>
          HNeg.pairing (φ a) (It (ts a) z.1 + Gt (ts a) z.2) -
            A * η₀ z.1 (propagatorW C 0 (ts a) (φ a)) : EuclideanSpace ℝ (Fin p))) =ᵐ[P.prod Q]
          fun z => V z.2 := by
        have h1 : ∀ a, ∀ᵐ z ∂(P.prod Q), HNeg.pairing (φ a) (It (ts a) z.1) =
            A * η₀ z.1 (propagatorW C 0 (ts a) (φ a)) :=
          fun a => measurePreserving_fst.quasiMeasurePreserving.ae
            (hIp (ts a) (hts a) (φ a) (hφ a))
        have h2 : ∀ a, ∀ᵐ z ∂(P.prod Q), HNeg.pairing (φ a) (Gt (ts a) z.2) = V z.2 a :=
          fun a => (measurePreserving_snd (μ := P) (ν := Q)).quasiMeasurePreserving.ae (hVae a)
        filter_upwards [ae_all_iff.2 h1, ae_all_iff.2 h2] with z hz1 hz2
        ext a
        simp only [u10_pairing_add (hφ a), hz1 a, hz2 a]
        simp
      refine ⟨?_, ?_⟩
      · exact (sb7_indepFun_prod P Q (η₀) hVm).symm.congr hae.symm (Filter.EventuallyEq.refl _ _)
      · rw [show law (P.prod Q) _ = law (P.prod Q) (fun z : Ω × Ω₀ => V z.2) from
          Measure.map_congr hae]
        have : law (P.prod Q) (fun z : Ω × Ω₀ => V z.2) = law Q V := by
          show (P.prod Q).map (V ∘ Prod.snd) = _
          rw [← Measure.map_map hVm measurable_snd]
          simp
        rw [this, hVlaw]
  · -- `T < 0`: only the empty family of tests is allowed
    have hT' : T < 0 := not_le.1 hT
    refine ⟨Ω, inferInstance, P, inferInstance, id, fun _ _ => 0, MeasurePreserving.id P, hρm,
      fun _ => measurable_const, ?_⟩
    intro p ts φ hts hφ
    have hp : p = 0 := by
      by_contra hne
      have := hts ⟨0, Nat.pos_of_ne_zero hne⟩
      exact absurd (this.1.trans this.2) (not_le.2 hT')
    subst hp
    refine ⟨?_, ?_⟩
    · exact (indepFun_const_left (0 : EuclideanSpace ℝ (Fin 0)) _).congr
        (Filter.Eventually.of_forall fun _ => Subsingleton.elim _ _) (Filter.EventuallyEq.refl _ _)
    · exact sb7_subsingleton_measure_eq _ _

end Existence

end HRS.MS.U10
