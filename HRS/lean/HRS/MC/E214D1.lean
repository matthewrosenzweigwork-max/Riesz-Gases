import HRS.MC.E213N2
import HRS.MC.E213K
import HRS.Uniform.KotTrace

/-!
# E214D1: feasibility prototype of P1 (the coupled pair of Gaussian fields): the block covariation density

Plan: one Gaussian Hilbert martingale `G` on `H2 = E_r × E_r` (`WithLp 2`) with block covariation density
`[[C(ρ), C(√(ρρ'))], [C(√(ρρ')), C(ρ')]]`; `fst ∘ G`, `snd ∘ G` are `E_r`-valued Gaussian martingales with the
densities of the two single fields (`isHM_map_clm`), driven by the same noise.

Contents.
* `isDetCovDensity_formComp`, `isHM_map_clm`: image of a Hilbert martingale with deterministic covariation under a
  bounded linear map.
* `blockU`, `blockForm`: the block covariance `2q ∑_j ∫ u_j ⊗ u_j dx`, `u_j(x) = (√(2qρ(x)) b_j(x), √(2qρ'(x)) b_j(x))`;
  its diagonal blocks are `covForm ρ`, `covForm ρ'`, its off-diagonal block is `covForm √(ρρ')`.
* `blockForm_isTraceClassCov`: symmetric, nonnegative, trace class, with trace `≤ 8 q d S` (`ρ, ρ'` probability densities).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214D

open HRS HRS.Uniform HRS.Uniform.Q14

/-! ### Images of Hilbert martingales under bounded linear maps -/

section MapMart

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]

theorem isDetCovDensity_formComp {t : ℝ} {B : ℝ → H →L[ℝ] H →L[ℝ] ℝ} (hB : IsDetCovDensity t B)
    (L : K →L[ℝ] H) : IsDetCovDensity t (fun σ => Kot.formComp L (B σ)) := by
  refine ⟨fun x y => hB.meas (L x) (L y),
    fun σ hσ => Kot.isTraceClassCov_formComp (hB.traceClass σ hσ) L, ?_⟩
  have hm : Measurable fun σ => traceNormForm (Kot.formComp L (B σ)) :=
    HRS.measurable_traceNormForm _ (fun x y => hB.meas (L x) (L y))
  refine Integrable.mono' (hB.int.const_mul (‖L‖ ^ 2)) hm.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
  rw [Real.norm_of_nonneg (traceNormForm_nonneg _)]
  exact Kot.traceNormForm_formComp_le (hB.traceClass σ hσ) L

/-- The image `L ∘ M` of a Hilbert martingale with deterministic covariation density `B` is a Hilbert martingale
with covariation density `L B L^*`. -/
theorem isHM_map_clm {ℱ : Filtration ℝ mΩ} {t : ℝ} {B : ℝ → H →L[ℝ] H →L[ℝ] ℝ}
    (hB : IsDetCovDensity t B) {M : ℝ → Ω → H}
    (hM : IsHilbertMartingaleWithCovariation P ℱ t M (fun r _ => B r)) (L : H →L[ℝ] K) :
    IsHilbertMartingaleWithCovariation P ℱ t (fun τ ω => L (M τ ω))
      (fun r _ => Kot.formComp (ContinuousLinearMap.adjoint L) (B r)) where
  martingale x := by
    have := hM.martingale (ContinuousLinearMap.adjoint L x)
    simpa only [ContinuousLinearMap.adjoint_inner_right] using this
  zero := hM.zero.mono fun ω h => by simp [h]
  cont := hM.cont.mono fun ω h => L.continuous.comp_continuousOn h
  sq_int τ hτ := L.comp_memLp' (hM.sq_int τ hτ)
  sigma_meas x y := hM.sigma_meas (ContinuousLinearMap.adjoint L x) (ContinuousLinearMap.adjoint L y)
  sigma_adapted σ x y :=
    hM.sigma_adapted σ (ContinuousLinearMap.adjoint L x) (ContinuousLinearMap.adjoint L y)
  sigma_traceClass := Filter.Eventually.of_forall fun ω σ hσ =>
    Kot.isTraceClassCov_formComp (hB.traceClass σ hσ) _
  sigma_int := integrable_const _
  sigma_pathint := Filter.Eventually.of_forall fun ω =>
    (isDetCovDensity_formComp hB (ContinuousLinearMap.adjoint L)).int
  sigma_entry_int := hM.sigma_entry_int.mono fun ω h x y =>
    h (ContinuousLinearMap.adjoint L x) (ContinuousLinearMap.adjoint L y)
  covariation x y := by
    have := hM.covariation (ContinuousLinearMap.adjoint L x) (ContinuousLinearMap.adjoint L y)
    simpa only [ContinuousLinearMap.adjoint_inner_right, Kot.formComp_apply] using this

end MapMart

/-! ### The block covariance form -/

section Block

variable {d : ℕ}

/-- The product Hilbert space `E_γ × E_γ` (orthogonal sum). -/
abbrev H2 (d : ℕ) (γ : ℝ) : Type := WithLp 2 (NegSobolev d γ × NegSobolev d γ)

/-- `u_j(x) = (√(2qρ(x)) b_j(x), √(2qρ'(x)) b_j(x)) ∈ E_γ × E_γ`. -/
def blockU (γ q : ℝ) (a b : Torus d → ℝ) (j : Fin d) (x : Torus d) : H2 d γ :=
  WithLp.toLp 2 (Real.sqrt (2 * q * a x) • bVec γ j x, Real.sqrt (2 * q * b x) • bVec γ j x)

/-- The block covariance form `∑_j ∫ u_j ⊗ u_j dx` on `E_γ × E_γ`. -/
def blockForm (γ q : ℝ) (a b : Torus d → ℝ) : H2 d γ →L[ℝ] H2 d γ →L[ℝ] ℝ :=
  ∑ j : Fin d, outerCov (blockU γ q a b j) (volume : Measure (Torus d))

/-- The embedding of the first factor. -/
def inl2 (γ : ℝ) (x : NegSobolev d γ) : H2 d γ := WithLp.toLp 2 (x, 0)

/-- The embedding of the second factor. -/
def inr2 (γ : ℝ) (x : NegSobolev d γ) : H2 d γ := WithLp.toLp 2 (0, x)

theorem inner_blockU (γ q : ℝ) (a b : Torus d → ℝ) (j : Fin d) (x : Torus d) (z : H2 d γ) :
    inner ℝ (blockU γ q a b j x) z =
      Real.sqrt (2 * q * a x) * inner ℝ (bVec γ j x) z.fst +
        Real.sqrt (2 * q * b x) * inner ℝ (bVec γ j x) z.snd := by
  simp [blockU, WithLp.prod_inner_apply, inner_smul_left]

theorem norm_sq_blockU (γ q : ℝ) (a b : Torus d → ℝ) (j : Fin d) (x : Torus d)
    (ha : 0 ≤ 2 * q * a x) (hb : 0 ≤ 2 * q * b x) :
    ‖blockU γ q a b j x‖ ^ 2 = (2 * q * a x + 2 * q * b x) * ‖bVec γ j x‖ ^ 2 := by
  have h1 : (blockU γ q a b j x).fst = Real.sqrt (2 * q * a x) • bVec γ j x := rfl
  have h2 : (blockU γ q a b j x).snd = Real.sqrt (2 * q * b x) • bVec γ j x := rfl
  rw [WithLp.prod_norm_sq_eq_of_L2, h1, h2, norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs,
    Real.norm_eq_abs, sq_abs, sq_abs, Real.sq_sqrt ha, Real.sq_sqrt hb]
  ring

theorem continuous_blockU {γ : ℝ} (hγ : (d : ℝ) / 2 + 2 < γ) (q : ℝ) {a b : Torus d → ℝ}
    (ha : Continuous a) (hb : Continuous b) (j : Fin d) : Continuous (blockU γ q a b j) := by
  have hbj := q14_continuous_bVec hγ j
  have h1 : Continuous fun x => ((Real.sqrt (2 * q * a x) • bVec γ j x,
      Real.sqrt (2 * q * b x) • bVec γ j x) : NegSobolev d γ × NegSobolev d γ) :=
    (((continuous_const.mul ha).sqrt).smul hbj).prodMk (((continuous_const.mul hb).sqrt).smul hbj)
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ (NegSobolev d γ) (NegSobolev d γ)).symm.continuous.comp h1

theorem blockForm_apply {γ : ℝ} (hγ : (d : ℝ) / 2 + 2 < γ) {q : ℝ} {a b : Torus d → ℝ}
    (ha : Continuous a) (hb : Continuous b) (z w : H2 d γ) :
    blockForm γ q a b z w = ∑ j : Fin d, ∫ x, inner ℝ (blockU γ q a b j x) z *
      inner ℝ (blockU γ q a b j x) w := by
  unfold blockForm
  simp only [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc := continuous_blockU hγ q ha hb j
  obtain ⟨x0, -, hx0⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty (f := fun x => ‖blockU γ q a b j x‖ ^ 2)
    (hc.norm.pow 2).continuousOn
  exact ChartAux.outerCov_apply hc (M := ‖blockU γ q a b j x0‖ ^ 2) (fun u => hx0 (Set.mem_univ u)) _ z w

theorem blockForm_inl_inl {γ : ℝ} (hγ : (d : ℝ) / 2 + 2 < γ) {q : ℝ} (hq : 0 ≤ q) {a b : Torus d → ℝ}
    (ha : Continuous a) (ha0 : ∀ x, 0 ≤ a x) (hb : Continuous b) (x y : NegSobolev d γ) :
    blockForm γ q a b (inl2 γ x) (inl2 γ y) = covForm γ q (withDensityReal a) x y := by
  haveI := HRS.Uniform.Q48c.isFiniteMeasure_withDensityReal_of_cont ha
  rw [blockForm_apply hγ ha hb, q14_covForm_apply hγ hq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [HRS.integral_withDensityReal_eq a ha.measurable ha0]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  have e1 : Real.sqrt (2 * q * a s) ^ 2 = 2 * q * a s := Real.sq_sqrt (by have := ha0 s; positivity)
  have e2 : Real.sqrt (2 * q) ^ 2 = 2 * q := Real.sq_sqrt (by positivity)
  simp only [inner_blockU, inl2, inner_smul_left, conj_trivial]
  simp only [WithLp.fst, WithLp.snd, inner_zero_right, mul_zero, add_zero]
  linear_combination (inner ℝ (bVec γ j s) x * inner ℝ (bVec γ j s) y) * e1 -
    (a s * inner ℝ (bVec γ j s) x * inner ℝ (bVec γ j s) y) * e2

theorem blockForm_inr_inr {γ : ℝ} (hγ : (d : ℝ) / 2 + 2 < γ) {q : ℝ} (hq : 0 ≤ q) {a b : Torus d → ℝ}
    (ha : Continuous a) (hb : Continuous b) (hb0 : ∀ x, 0 ≤ b x) (x y : NegSobolev d γ) :
    blockForm γ q a b (inr2 γ x) (inr2 γ y) = covForm γ q (withDensityReal b) x y := by
  haveI := HRS.Uniform.Q48c.isFiniteMeasure_withDensityReal_of_cont hb
  rw [blockForm_apply hγ ha hb, q14_covForm_apply hγ hq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [HRS.integral_withDensityReal_eq b hb.measurable hb0]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  have e1 : Real.sqrt (2 * q * b s) ^ 2 = 2 * q * b s := Real.sq_sqrt (by have := hb0 s; positivity)
  have e2 : Real.sqrt (2 * q) ^ 2 = 2 * q := Real.sq_sqrt (by positivity)
  simp only [inner_blockU, inr2, inner_smul_left, conj_trivial]
  simp only [WithLp.fst, WithLp.snd, inner_zero_right, mul_zero, zero_add]
  linear_combination (inner ℝ (bVec γ j s) x * inner ℝ (bVec γ j s) y) * e1 -
    (b s * inner ℝ (bVec γ j s) x * inner ℝ (bVec γ j s) y) * e2

/-- The off-diagonal block is `covForm` for the geometric-mean density `√(ab)`. -/
theorem blockForm_inl_inr {γ : ℝ} (hγ : (d : ℝ) / 2 + 2 < γ) {q : ℝ} (hq : 0 ≤ q) {a b : Torus d → ℝ}
    (ha : Continuous a) (ha0 : ∀ x, 0 ≤ a x) (hb : Continuous b) (hb0 : ∀ x, 0 ≤ b x)
    (x y : NegSobolev d γ) :
    blockForm γ q a b (inl2 γ x) (inr2 γ y) =
      covForm γ q (withDensityReal fun t => Real.sqrt (a t * b t)) x y := by
  have hk : Continuous fun t => Real.sqrt (a t * b t) := (ha.mul hb).sqrt
  haveI := HRS.Uniform.Q48c.isFiniteMeasure_withDensityReal_of_cont hk
  rw [blockForm_apply hγ ha hb, q14_covForm_apply hγ hq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [HRS.integral_withDensityReal_eq _ hk.measurable (fun t => Real.sqrt_nonneg _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  have e1 : Real.sqrt (2 * q * a s) * Real.sqrt (2 * q * b s) = 2 * q * Real.sqrt (a s * b s) := by
    have h1 : 0 ≤ 2 * q * a s := by have := ha0 s; positivity
    rw [← Real.sqrt_mul h1]
    have : 2 * q * a s * (2 * q * b s) = (2 * q) ^ 2 * (a s * b s) := by ring
    rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have e2 : Real.sqrt (2 * q) ^ 2 = 2 * q := Real.sq_sqrt (by positivity)
  simp only [inner_blockU, inl2, inr2, inner_smul_left, conj_trivial]
  simp only [WithLp.fst, WithLp.snd, inner_zero_right, mul_zero, zero_add, add_zero]
  linear_combination (inner ℝ (bVec γ j s) x * inner ℝ (bVec γ j s) y) * e1 -
    (Real.sqrt (a s * b s) * inner ℝ (bVec γ j s) x * inner ℝ (bVec γ j s) y) * e2

/-- The block form is symmetric, nonnegative, trace class, with trace `≤ 8 q d S` (`a, b` probability densities). -/
theorem blockForm_trace {γ : ℝ} (hγ : (d : ℝ) / 2 + 2 < γ) {q : ℝ} {a b : Torus d → ℝ}
    (ha : Continuous a) (ha0 : ∀ x, 0 ≤ a x) (hb : Continuous b) (hb0 : ∀ x, 0 ≤ b x) (hq : 0 ≤ q)
    (hai : ∫ x, a x = 1) (hbi : ∫ x, b x = 1) :
    IsTraceClassCov (blockForm γ q a b) ∧
      traceNormForm (blockForm γ q a b) ≤ 8 * q * d * q14S d (γ - 1) := by
  have hcj := fun j => continuous_blockU hγ q ha hb j
  have hum : ∀ j, Measurable (blockU γ q a b j) := fun j => (hcj j).measurable
  have hbd : ∀ j : Fin d, ∃ C : ℝ, ∀ x : Torus d, ‖blockU γ q a b j x‖ ≤ C := fun j => by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (hcj j).norm.continuousOn
    exact ⟨C, fun x => (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hC x (Set.mem_univ x)))⟩
  choose Cj hCj using hbd
  obtain ⟨ι, hι, e, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H2 d γ)
  haveI := hι
  obtain ⟨h1, h2⟩ := q14_form_of_family (ξ := (volume : Measure (Torus d))) (u := blockU γ q a b) hum
    (M := ∑ j, |Cj j|) (fun j x => (hCj j x).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun j => |Cj j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j))))
    (C := blockForm γ q a b) (fun x y => blockForm_apply hγ ha hb x y) e
  refine ⟨h1, h2.trans_le ?_⟩
  have hint : ∀ {f : Torus d → ℝ}, Continuous f → Integrable f (volume : Measure (Torus d)) := fun hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpt : ∀ (j : Fin d) (x : Torus d), ‖blockU γ q a b j x‖ ^ 2 ≤ 4 * q * q14S d (γ - 1) * (a x + b x) := by
    intro j x
    rw [norm_sq_blockU γ q a b j x (by have := ha0 x; positivity) (by have := hb0 x; positivity)]
    have := q14_norm_bVec_sq_le hγ j x
    have h0 : 0 ≤ 2 * q * a x + 2 * q * b x := by have := ha0 x; have := hb0 x; positivity
    calc (2 * q * a x + 2 * q * b x) * ‖bVec γ j x‖ ^ 2
        ≤ (2 * q * a x + 2 * q * b x) * (2 * q14S d (γ - 1)) := mul_le_mul_of_nonneg_left this h0
      _ = 4 * q * q14S d (γ - 1) * (a x + b x) := by ring
  calc ∑ j : Fin d, ∫ x, ‖blockU γ q a b j x‖ ^ 2
      ≤ ∑ _j : Fin d, (8 * q * q14S d (γ - 1)) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hi1 : Integrable (fun x => ‖blockU γ q a b j x‖ ^ 2) (volume : Measure (Torus d)) :=
          hint ((hcj j).norm.pow 2)
        have hi2 : Integrable (fun x => 4 * q * q14S d (γ - 1) * (a x + b x)) (volume : Measure (Torus d)) :=
          (hint (ha.add hb)).const_mul _
        calc ∫ x, ‖blockU γ q a b j x‖ ^ 2 ≤ ∫ x, 4 * q * q14S d (γ - 1) * (a x + b x) :=
              integral_mono hi1 hi2 (hpt j)
          _ = 8 * q * q14S d (γ - 1) := by
              rw [integral_const_mul, integral_add (hint ha) (hint hb), hai, hbi]; ring
    _ = 8 * q * d * q14S d (γ - 1) := by simp [Finset.sum_const]; ring

/-- The global block covariation density `σ ↦ 1_{σ ≥ 0} blockForm (ρ_σ) (ρ'_σ)`. -/
def blockDens (γ q : ℝ) (ρ ρ' : ℝ → Torus d → ℝ) : ℝ → H2 d γ →L[ℝ] H2 d γ →L[ℝ] ℝ :=
  fun σ => if 0 ≤ σ then blockForm γ q (ρ σ) (ρ' σ) else 0

/-- The block density is a deterministic covariance density on every window `[0,t]`. -/
theorem isDetCovDensity_blockDens {γ : ℝ} (hγ : (d : ℝ) / 2 + 2 < γ) {q : ℝ} (hq : 0 ≤ q)
    {ρ ρ' : ℝ → Torus d → ℝ}
    (hρ : ∀ σ, 0 ≤ σ → IsProbDensity (ρ σ)) (hρc : ∀ σ, 0 ≤ σ → Continuous (ρ σ))
    (hρ' : ∀ σ, 0 ≤ σ → IsProbDensity (ρ' σ)) (hρc' : ∀ σ, 0 ≤ σ → Continuous (ρ' σ))
    (hm : Measurable fun p : ℝ × Torus d => if 0 ≤ p.1 then ρ p.1 p.2 else 0)
    (hm' : Measurable fun p : ℝ × Torus d => if 0 ≤ p.1 then ρ' p.1 p.2 else 0) :
    ∀ t : ℝ, 0 ≤ t → IsDetCovDensity t (blockDens γ q ρ ρ') := by
  intro t ht
  have hbj : ∀ j : Fin d, Measurable (bVec γ j) := fun j => (q14_continuous_bVec hγ j).measurable
  have hmeas : ∀ z w : H2 d γ, Measurable fun σ => blockDens γ q ρ ρ' σ z w := by
    intro z w
    set ρ1 : ℝ → Torus d → ℝ := fun σ x => if 0 ≤ σ then ρ σ x else 0 with hρ1
    set ρ2 : ℝ → Torus d → ℝ := fun σ x => if 0 ≤ σ then ρ' σ x else 0 with hρ2
    have key : ∀ σ, blockDens γ q ρ ρ' σ z w = ∑ j : Fin d, ∫ x,
        inner ℝ (blockU γ q (ρ1 σ) (ρ2 σ) j x) z * inner ℝ (blockU γ q (ρ1 σ) (ρ2 σ) j x) w := by
      intro σ
      by_cases hσ : 0 ≤ σ
      · have e1 : ρ1 σ = ρ σ := by funext x; simp [hρ1, hσ]
        have e2 : ρ2 σ = ρ' σ := by funext x; simp [hρ2, hσ]
        rw [e1, e2]
        simp only [blockDens, if_pos hσ]
        exact blockForm_apply hγ (hρc σ hσ) (hρc' σ hσ) z w
      · have e1 : ρ1 σ = fun _ => 0 := by funext x; simp [hρ1, hσ]
        have e2 : ρ2 σ = fun _ => 0 := by funext x; simp [hρ2, hσ]
        have hz : ∀ (j : Fin d) (x : Torus d), blockU γ q (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) j x = 0 := by
          intro j x
          simp only [blockU, mul_zero, Real.sqrt_zero, zero_smul]
          rfl
        rw [e1, e2]
        simp [blockDens, hσ, hz]
    simp_rw [key]
    refine Finset.measurable_sum _ fun j _ => ?_
    refine (StronglyMeasurable.integral_prod_right'
      (f := fun p : ℝ × Torus d => inner ℝ (blockU γ q (ρ1 p.1) (ρ2 p.1) j p.2) z *
        inner ℝ (blockU γ q (ρ1 p.1) (ρ2 p.1) j p.2) w) ?_).measurable
    simp only [inner_blockU]
    have hb1 : Measurable fun p : ℝ × Torus d => inner ℝ (bVec γ j p.2) z.fst :=
      ((hbj j).comp measurable_snd).inner measurable_const
    have hb2 : Measurable fun p : ℝ × Torus d => inner ℝ (bVec γ j p.2) z.snd :=
      ((hbj j).comp measurable_snd).inner measurable_const
    have hb3 : Measurable fun p : ℝ × Torus d => inner ℝ (bVec γ j p.2) w.fst :=
      ((hbj j).comp measurable_snd).inner measurable_const
    have hb4 : Measurable fun p : ℝ × Torus d => inner ℝ (bVec γ j p.2) w.snd :=
      ((hbj j).comp measurable_snd).inner measurable_const
    have hs1 : Measurable fun p : ℝ × Torus d => Real.sqrt (2 * q * ρ1 p.1 p.2) :=
      (measurable_const.mul hm).sqrt
    have hs2 : Measurable fun p : ℝ × Torus d => Real.sqrt (2 * q * ρ2 p.1 p.2) :=
      (measurable_const.mul hm').sqrt
    exact (((hs1.mul hb1).add (hs2.mul hb2)).mul ((hs1.mul hb3).add (hs2.mul hb4))).stronglyMeasurable
  have htr : ∀ σ ∈ Set.Icc (0 : ℝ) t, IsTraceClassCov (blockDens γ q ρ ρ' σ) ∧
      traceNormForm (blockDens γ q ρ ρ' σ) ≤ 8 * q * d * q14S d (γ - 1) := by
    intro σ hσ
    simp only [blockDens, if_pos hσ.1]
    exact blockForm_trace hγ (hρc σ hσ.1) (hρ σ hσ.1).nonneg (hρc' σ hσ.1) (hρ' σ hσ.1).nonneg hq
      (hρ σ hσ.1).integral_one (hρ' σ hσ.1).integral_one
  refine ⟨hmeas, fun σ hσ => (htr σ hσ).1, ?_⟩
  have hmt : Measurable fun σ => traceNormForm (blockDens γ q ρ ρ' σ) :=
    HRS.measurable_traceNormForm _ hmeas
  refine Measure.integrableOn_of_bounded (M := 8 * q * d * q14S d (γ - 1)) (by simp)
    hmt.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
  rw [Real.norm_of_nonneg (traceNormForm_nonneg _)]
  exact (htr σ hσ).2

end Block

end HRS.MC.E214D

end
