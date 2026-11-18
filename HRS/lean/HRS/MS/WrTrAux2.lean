import HRS.MS.WrTrAux1

/-!
# HRS.MS.WrTrAux2 -- the calibrated weak potential, Wu's inequality for `R_N`, the trace in `H`
(WR-11b, part 2)

Packet WR-11b of `docs/WR_B_PLAN.md` (T6), namespace `HRS.MS.Wr`, helper prefix `wr11b_`.
Port of `HRS/Equilibrium/CalibratedReference.lean:934-1215` (`weakPot`, `RN_eq_fieldLaw`, `var_sum_le`,
`integral_coord_sq_le`) to `Euc d` and a real Hilbert space `H`.

* `wr11b_trace_limit`: a generic fact (any probability space): if `D : Ω → H` is bounded and strongly
  measurable, `H` is separable and complete, and `∫ ∑_j ⟪e_j, D⟫² ≤ T` for every finite orthonormal family
  `e`, then `∫ ‖D‖² ≤ T`.  The trace is thus controlled without a countable Hilbert basis: the finite-dimensional
  spans `K_m = span (u_0, ..., u_{m-1})` of a dense sequence `u` have `‖P_m D‖² = ∑_j ⟪e_j, D⟫²` for an
  orthonormal basis `e` of `K_m` and `P_m D → D` (`Submodule.starProjection_tendsto_self`).
* `wr11b_weakPotE`: the weak potential `φ = β (q*μ) + ⟪t, Ξ⟫` (`M = βa + 1`, `M' = 0`, `γ = a`), valid when
  `|⟪t, Ξ⟫| ≤ 1`; `wr11b_RN_eq_fieldLaw`: `R_N = fieldLaw (weakPotE) φ (β/N) N`.
* `wr11b_evar_sum_le`: Wu's inequality `Var_{R_N}(∑ f(x_i)) ≤ 2N Var_π(f)` (`evariance` form);
  `wr11b_inner_sq_le`: `E_{R_N} ⟪v, S_N - √N Ξ̄_N⟫² ≤ 2 E_{R_N} ⟪v, Ξ(x_1)⟫²` for every `v : H`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ### The trace in a separable Hilbert space, via finite-dimensional projections -/

theorem wr11b_proj_sq [CompleteSpace H] (K : Submodule ℝ H) [FiniteDimensional ℝ K] :
    ∃ (n : ℕ) (e : Fin n → H), Orthonormal ℝ e ∧
      ∀ v : H, ‖K.starProjection v‖ ^ 2 = ∑ j, (inner ℝ (e j) v) ^ 2 := by
  haveI : K.HasOrthogonalProjection := inferInstance
  let b := stdOrthonormalBasis ℝ K
  refine ⟨_, fun j => (b j : H), b.orthonormal.comp_linearIsometry K.subtypeₗᵢ, fun v => ?_⟩
  have h1 := b.sum_sq_norm_inner_right ⟨K.starProjection v, K.starProjection_apply_mem v⟩
  have h2 : ∀ j, inner ℝ (b j : H) (K.starProjection v) = inner ℝ (b j : H) v := by
    intro j
    have hj : (b j : H) ∈ K := (b j).2
    have := K.inner_starProjection_left_eq_right (b j : H) v
    rw [K.starProjection_eq_self_iff.2 hj] at this
    rw [← this, real_inner_comm, real_inner_comm (b j : H) v]
  have h3 : ‖K.starProjection v‖ = ‖(⟨K.starProjection v, K.starProjection_apply_mem v⟩ : K)‖ := rfl
  rw [h3, ← h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Real.norm_eq_abs, sq_abs]
  show (inner ℝ (b j : H) (K.starProjection v)) ^ 2 = _
  rw [h2]

theorem wr11b_trace_limit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {D : Ω → H}
    (hD : StronglyMeasurable D) {C : ℝ} (hC : ∀ ω, ‖D ω‖ ≤ C) {T : ℝ}
    (hfin : ∀ (n : ℕ) (e : Fin n → H), Orthonormal ℝ e →
      ∫ ω, ∑ j, (inner ℝ (e j) (D ω)) ^ 2 ∂P ≤ T) :
    ∫ ω, ‖D ω‖ ^ 2 ∂P ≤ T := by
  haveI : Nonempty H := ⟨0⟩
  set u : ℕ → H := TopologicalSpace.denseSeq H with hu
  let K : ℕ → Submodule ℝ H := fun m => Submodule.span ℝ (u '' Set.Iio m)
  have hKfin : ∀ m, FiniteDimensional ℝ (K m) := fun m =>
    FiniteDimensional.span_of_finite ℝ ((Set.finite_Iio m).image u)
  haveI : ∀ m, (K m).HasOrthogonalProjection := fun m => by
    haveI := hKfin m
    infer_instance
  have hmono : Monotone K := fun m m' hmm' =>
    Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio hmm'))
  have hdense : ⊤ ≤ (⨆ m, K m).topologicalClosure := by
    intro x _
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    have hsub : Set.range u ⊆ ((⨆ m, K m : Submodule ℝ H) : Set H) := by
      rintro _ ⟨i, rfl⟩
      refine (le_iSup K (i + 1)) (Submodule.subset_span ⟨i, Set.mem_Iio.2 (Nat.lt_succ_self i), rfl⟩)
    have : closure (Set.range u) = Set.univ := (TopologicalSpace.denseRange_denseSeq H).closure_eq
    exact closure_mono hsub (this ▸ Set.mem_univ x)
  have hlim : ∀ ω, Tendsto (fun m => ‖(K m).starProjection (D ω)‖ ^ 2) atTop (𝓝 (‖D ω‖ ^ 2)) := by
    intro ω
    have := Submodule.starProjection_tendsto_self K hmono (D ω) hdense
    exact ((continuous_norm.pow 2).tendsto _).comp this
  have hmeas : ∀ m, AEStronglyMeasurable (fun ω => ‖(K m).starProjection (D ω)‖ ^ 2) P := fun m =>
    ((((K m).starProjection.continuous.comp_stronglyMeasurable hD).norm).pow 2).aestronglyMeasurable
  have hbd : ∀ m, ∀ᵐ ω ∂P, ‖‖(K m).starProjection (D ω)‖ ^ 2‖ ≤ C ^ 2 := fun m =>
    Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h1 := (K m).norm_starProjection_apply_le (D ω)
      have h2 := norm_nonneg ((K m).starProjection (D ω))
      exact pow_le_pow_left₀ h2 (h1.trans (hC ω)) 2
  have htend := tendsto_integral_of_dominated_convergence (fun _ => C ^ 2) hmeas (integrable_const _)
    hbd (Eventually.of_forall hlim)
  refine le_of_tendsto' htend fun m => ?_
  obtain ⟨n, e, he, hsq⟩ := (haveI := hKfin m; wr11b_proj_sq (K m))
  simp_rw [hsq]
  exact hfin n e he

/-! ### The calibrated weak potential and `R_N` as a field law -/

variable {d : ℕ}

section Weak

open HRS.External

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a : ℝ} {q k g : Euc d → ℝ} {Ψ : Euc d → H}
  {N : ℕ} {β : ℝ}

/-- `∫ Ξ dμ = 0`. -/
theorem wr11b_integral_Xi [CompleteSpace H] (h : TransferHyp μ a q k g Ψ) :
    ∫ x, Xi μ Ψ x ∂μ = 0 := by
  unfold Xi
  have hi : Integrable Ψ μ := h.calFeat.integrable_Ψ
  rw [integral_sub hi (integrable_const _)]
  simp

theorem wr11b_integrable_Xi [CompleteSpace H] (h : TransferHyp μ a q k g Ψ) :
    Integrable (Xi μ Ψ) μ :=
  Integrable.of_bound h.calFeat.continuous_Xi.stronglyMeasurable.aestronglyMeasurable
    (2 * Real.sqrt (k 0)) (Eventually.of_forall fun x => h.calFeat.norm_Xi_le x)

theorem wr11b_continuous_inner_Xi [CompleteSpace H] (h : TransferHyp μ a q k g Ψ) (t : H) :
    Continuous (fun x => inner ℝ t (Xi μ Ψ x)) :=
  continuous_const.inner h.calFeat.continuous_Xi

/-- The weak potential of `R_{N, t·Ξ}`: `φ = β (q*μ) + ⟪t, Ξ⟫`, pair kernel `q (x - y)`, `M = βa + 1`,
`M' = 0`, `γ = a`, provided `|⟪t, Ξ⟫| ≤ 1`. -/
def wr11b_weakPotE [CompleteSpace H] (h : TransferHyp μ a q k g Ψ) {β : ℝ} (hβ : 0 ≤ β) (t : H)
    (ht : ∀ x, |inner ℝ t (Xi μ Ψ x)| ≤ 1) : WeakPotential μ where
  φ := fun x => β * rowIntE (wr11b_dk q) μ x + inner ℝ t (Xi μ Ψ x)
  q := wr11b_dk q
  M := β * a + 1
  M' := 0
  γ := a
  measurable_φ := (h.weak.wr1_measurable_rowInt.const_mul β).add
    (wr11b_continuous_inner_Xi h t).measurable
  measurable_q := h.weak.meas
  q_nonneg := h.weak.nonneg
  q_symm := h.weak.symm
  γ_nonneg := h.a_nonneg
  φ_le := fun x => by
    have h1 : β * rowIntE (wr11b_dk q) μ x ≤ β * a :=
      mul_le_mul_of_nonneg_left (h.weak.wr1_rowInt_le h.a_nonneg x) hβ
    have h2 := (le_abs_self _).trans (ht x)
    linarith
  integrable_φ := by
    refine Integrable.of_bound ((h.weak.wr1_measurable_rowInt.const_mul β).add
      (wr11b_continuous_inner_Xi h t).measurable).aestronglyMeasurable (β * a + 1)
      (Eventually.of_forall fun x => ?_)
    have h1 : 0 ≤ β * rowIntE (wr11b_dk q) μ x := mul_nonneg hβ (h.weak.wr1_rowInt_nonneg x)
    have h1' : β * rowIntE (wr11b_dk q) μ x ≤ β * a :=
      mul_le_mul_of_nonneg_left (h.weak.wr1_rowInt_le h.a_nonneg x) hβ
    have h2 := abs_le.1 (ht x)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [h2.1, h2.2]
  neg_le_integral_φ := by
    have hi1 : Integrable (fun x => β * rowIntE (wr11b_dk q) μ x) μ :=
      Integrable.of_bound (h.weak.wr1_measurable_rowInt.const_mul β).aestronglyMeasurable (β * a)
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hβ (h.weak.wr1_rowInt_nonneg x))]
          exact mul_le_mul_of_nonneg_left (h.weak.wr1_rowInt_le h.a_nonneg x) hβ)
    have hi2 : Integrable (fun x => inner ℝ t (Xi μ Ψ x)) μ :=
      Integrable.of_bound (wr11b_continuous_inner_Xi h t).aestronglyMeasurable 1
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact ht x)
    rw [integral_add hi1 hi2, integral_inner (wr11b_integrable_Xi h) t, wr11b_integral_Xi h]
    have : 0 ≤ ∫ x, β * rowIntE (wr11b_dk q) μ x ∂μ :=
      integral_nonneg fun x => mul_nonneg hβ (h.weak.wr1_rowInt_nonneg x)
    simpa using this
  integrable_q := h.weak.wr1_integrable_row
  row_le := fun x => h.weak.wr1_rowInt_le h.a_nonneg x

theorem wr11b_fieldLaw_eq_tilted {V : WeakPotential μ} {ψ : Euc d → ℝ} {lam : ℝ} {n : ℕ}
    (hint : Integrable (fun y : Fin n → Euc d =>
      Real.exp (∑ i, ψ (y i) - lam * HRS.External.pairEnergy V y)) (Measure.pi fun _ : Fin n => μ)) :
    fieldLaw V ψ lam n = (Measure.pi fun _ : Fin n => μ).tilted
      (fun y => ∑ i, ψ (y i) - lam * HRS.External.pairEnergy V y) := by
  have hZ : ENNReal.ofReal (∫ y, Real.exp (∑ i, ψ (y i) - lam * HRS.External.pairEnergy V y)
      ∂(Measure.pi fun _ : Fin n => μ)) = fieldNorm V ψ lam n := by
    unfold fieldNorm fieldWeight
    exact ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
  have hZpos := integral_exp_pos (μ := Measure.pi fun _ : Fin n => μ)
    (f := fun y : Fin n → Euc d => ∑ i, ψ (y i) - lam * HRS.External.pairEnergy V y) hint
  unfold fieldLaw Measure.tilted
  congr 1
  funext y
  unfold fieldDensity fieldWeight
  rw [ENNReal.ofReal_div_of_pos hZpos, hZ, div_eq_mul_inv]

variable [CompleteSpace H]

theorem wr11b_RN_eq_tilted (h : TransferHyp μ a q k g Ψ) (hβ : 0 ≤ β) (hN : 0 < N) :
    RN (wr11b_dk q) μ Ψ β N = (Measure.pi fun _ : Fin N => μ).tilted
      (fun X => -β * N * modEnergyE (wr11b_dk q) X μ + Yf μ Ψ (tN (wr11b_dk q) μ Ψ β N) X) := by
  unfold RN
  rw [h.weak.wr12_eq_tilted h.a_nonneg hβ hN,
    tilted_tilted (h.weak.wr12_integrable_exp h.a_nonneg hβ hN)]
  rfl

/-- `R_N` is the field law of the calibrated weak potential. -/
theorem wr11b_RN_eq_fieldLaw (h : TransferHyp μ a q k g Ψ) (hβ : 0 ≤ β) (hN : 0 < N)
    (ht : ∀ x, |inner ℝ (tN (wr11b_dk q) μ Ψ β N) (Xi μ Ψ x)| ≤ 1) :
    RN (wr11b_dk q) μ Ψ β N =
      fieldLaw (wr11b_weakPotE h hβ (tN (wr11b_dk q) μ Ψ β N) ht)
        (wr11b_weakPotE h hβ (tN (wr11b_dk q) μ Ψ β N) ht).φ (β / N) N := by
  set P : Measure (Fin N → Euc d) := Measure.pi fun _ : Fin N => μ with hP
  set t := tN (wr11b_dk q) μ Ψ β N with htdef
  set V := wr11b_weakPotE h hβ t ht with hV
  set c0 : ℝ := β * N * (∫ x, ∫ y, wr11b_dk q x y ∂μ ∂μ) / 2 with hc0
  have hexp : ∀ X : Fin N → Euc d,
      ∑ i, V.φ (X i) - (β / N) * HRS.External.pairEnergy V X =
        (-β * N * modEnergyE (wr11b_dk q) X μ + Yf μ Ψ t X) + c0 := by
    intro X
    rw [wr1_exponent_eq (wr11b_dk q) μ β X hN]
    have hpe : HRS.External.pairEnergy V X = (1 / 2) * pairSumE (wr11b_dk q) X := rfl
    have hφ : ∑ i, V.φ (X i) = β * ∑ i, rowIntE (wr11b_dk q) μ (X i) + Yf μ Ψ t X := by
      simp only [hV, wr11b_weakPotE, Yf, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hpe, hφ]
    have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [hc0]
    field_simp
    ring
  have hint1 := wr11b_integrable_exp_Yf_add h hβ hN t
  have hint : Integrable (fun y : Fin N → Euc d =>
      Real.exp (∑ i, V.φ (y i) - (β / N) * HRS.External.pairEnergy V y)) P := by
    have := hint1.mul_const (Real.exp c0)
    refine this.congr (Eventually.of_forall fun X => ?_)
    simp only [hexp, Real.exp_add]
  rw [wr11b_fieldLaw_eq_tilted hint, wr11b_RN_eq_tilted h hβ hN]
  have e : (fun y : Fin N → Euc d => ∑ i, V.φ (y i) - (β / N) * HRS.External.pairEnergy V y) =
      fun X => (-β * N * modEnergyE (wr11b_dk q) X μ + Yf μ Ψ t X) + c0 := funext hexp
  rw [e, wr11b_tilted_add_const P (fun X => -β * N * modEnergyE (wr11b_dk q) X μ + Yf μ Ψ t X) c0]

/-- Smallness hypothesis of Wu's inequality for `R_N`: `κ = 4 e^{M+M'+βγ} βγ ≤ 1/2` with `M = βa + 1`,
`M' = 0`, `γ = a`. -/
def wr11b_KappaSmall (β a : ℝ) : Prop := 4 * Real.exp (2 * (β * a) + 1) * (β * a) ≤ 1 / 2

/-- **Wu's inequality for `R_N`** (`A:eq:weak-linear`, `evariance` form):
`Var_{R_N}(∑_i f(x_i)) ≤ 2N Var_π(f)`, `π` the one-point marginal. -/
theorem wr11b_evar_sum_le (h : TransferHyp μ a q k g Ψ) (hβ : 0 ≤ β) (hN : 0 < N)
    (ht : ∀ x, |inner ℝ (tN (wr11b_dk q) μ Ψ β N) (Xi μ Ψ x)| ≤ 1) (hκ : wr11b_KappaSmall β a)
    [NeZero N] (f : Euc d → ℝ) (hf : Measurable f) :
    evariance (fun X : Fin N → Euc d => ∑ i, f (X i)) (RN (wr11b_dk q) μ Ψ β N) ≤
      2 * N * evariance f ((RN (wr11b_dk q) μ Ψ β N).map (fun X => X 0)) := by
  obtain ⟨V, hV⟩ : ∃ V : WeakPotential μ,
      V = wr11b_weakPotE h hβ (tN (wr11b_dk q) μ Ψ β N) ht := ⟨_, rfl⟩
  have hRN := wr11b_RN_eq_fieldLaw h hβ hN ht
  rw [← hV] at hRN
  have hpin : pinnedLaw V (β / N) N (fun e : Empty => e.elim) = RN (wr11b_dk q) μ Ψ β N := by
    rw [hRN]
    unfold pinnedLaw
    congr 1
    funext z
    simp [pinField]
  have hκ' : weakKappa V β ≤ 1 / 2 := by
    have e : weakKappa V β = 4 * Real.exp ((β * a + 1) + 0 + β * a) * (β * a) := by
      rw [hV]; rfl
    rw [e]
    have : (β * a + 1) + 0 + β * a = 2 * (β * a) + 1 := by ring
    rw [this]
    exact hκ
  have key := weak_linear_variance_symm (B := Empty) (n := N) V hβ hN (by simp)
    (fun e => e.elim) hκ' f hf
  rw [hpin] at key
  exact key

/-- Real form of Wu's inequality for bounded `f`: `Var_{R_N}(∑ f(x_i)) ≤ 2N Var_π(f)`. -/
theorem wr11b_var_sum_le (h : TransferHyp μ a q k g Ψ) (hβ : 0 ≤ β) (hN : 0 < N)
    (ht : ∀ x, |inner ℝ (tN (wr11b_dk q) μ Ψ β N) (Xi μ Ψ x)| ≤ 1) (hκ : wr11b_KappaSmall β a)
    [NeZero N] (f : Euc d → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) :
    variance (fun X : Fin N → Euc d => ∑ i, f (X i)) (RN (wr11b_dk q) μ Ψ β N) ≤
      2 * N * variance f ((RN (wr11b_dk q) μ Ψ β N).map (fun X => X 0)) := by
  haveI : IsProbabilityMeasure (RN (wr11b_dk q) μ Ψ β N) := isProb_RN h.weak h.calFeat hβ hN
  have key := wr11b_evar_sum_le h hβ hN ht hκ f hf
  have hF : Measurable fun X : Fin N → Euc d => ∑ i, f (X i) :=
    Finset.measurable_sum _ fun j _ => hf.comp (measurable_pi_apply j)
  have hf2 : MemLp f 2 ((RN (wr11b_dk q) μ Ψ β N).map (fun X => X 0)) :=
    MemLp.of_bound hf.aestronglyMeasurable B
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)
  have hF2 : MemLp (fun X : Fin N → Euc d => ∑ i, f (X i)) 2 (RN (wr11b_dk q) μ Ψ β N) :=
    MemLp.of_bound hF.aestronglyMeasurable (N * B)
      (Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]
        calc |∑ i, f (X i)| ≤ ∑ i, |f (X i)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin N, B := Finset.sum_le_sum fun i _ => hB _
          _ = N * B := by simp)
  rw [← ofReal_variance hf2, ← ofReal_variance hF2] at key
  have h0 : 0 ≤ 2 * (N : ℝ) * variance f ((RN (wr11b_dk q) μ Ψ β N).map (fun X => X 0)) :=
    mul_nonneg (by positivity) (variance_nonneg _ _)
  have e : (2 : ℝ≥0∞) * N * ENNReal.ofReal (variance f ((RN (wr11b_dk q) μ Ψ β N).map (fun X => X 0))) =
      ENNReal.ofReal (2 * N * variance f ((RN (wr11b_dk q) μ Ψ β N).map (fun X => X 0))) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
    simp
  rw [e, ENNReal.ofReal_le_ofReal_iff h0] at key
  exact key

end Weak

end HRS.MS.Wr
