import HRS.Prob.EdgeworthAux

/-!
# Auxiliary results for `hilbert_edgeworth_C4`

Finite-dimensional smoothing by convolution, Hilbert-basis truncation, and the uniform
Lindeberg estimate for Lipschitz test functions.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped Convolution ENNReal NNReal BigOperators Nat

namespace HRS

namespace EdgeAux



noncomputable section

set_option linter.unusedSectionVars false

section Conv

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The smoothing `x ↦ ∫ Φ(y) ρ(x - y) dμ(y)`. -/
def smoothConv {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (Φ : E → ℝ) (ρ : E → V)
    (x : E) : V :=
  ∫ y, Φ y • ρ (x - y) ∂μ

lemma smoothConv_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (Φ : E → ℝ) (ρ : E → V) :
    smoothConv μ Φ ρ = Φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] ρ := by
  funext x
  simp [smoothConv, convolution_def]

lemma hasFDerivAt_smoothConv {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Φ : E → ℝ}
    (hΦ : Continuous Φ) {ρ : E → V} (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ) (x : E) :
    HasFDerivAt (smoothConv μ Φ ρ) (smoothConv μ Φ (fderiv ℝ ρ) x) x := by
  have h := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) (μ := μ)
    (hΦ.locallyIntegrable) hρ x
  rw [← smoothConv_eq] at h
  convert h using 1
  simp only [smoothConv, convolution_def]
  congr 1

lemma fderiv_smoothConv {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Φ : E → ℝ}
    (hΦ : Continuous Φ) {ρ : E → V} (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ) :
    fderiv ℝ (smoothConv μ Φ ρ) = smoothConv μ Φ (fderiv ℝ ρ) := by
  funext x
  exact (hasFDerivAt_smoothConv μ hΦ hc hρ x).fderiv

lemma norm_smoothConv_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [μ.IsNegInvariant]
    {Φ : E → ℝ} {B : ℝ} (hB : ∀ y, |Φ y| ≤ B) {ρ : E → V} (hc : HasCompactSupport ρ)
    (hρ : Continuous ρ) (x : E) :
    ‖smoothConv μ Φ ρ x‖ ≤ B * ∫ y, ‖ρ y‖ ∂μ := by
  have hint : Integrable (fun y => ‖ρ y‖) μ := (hρ.norm).integrable_of_hasCompactSupport hc.norm
  have hint' : Integrable (fun y => ‖ρ (x - y)‖) μ := by
    have := hint.comp_sub_left x
    exact this
  refine (norm_integral_le_integral_norm _).trans ?_
  calc ∫ y, ‖Φ y • ρ (x - y)‖ ∂μ ≤ ∫ y, B * ‖ρ (x - y)‖ ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _)
          (hint'.const_mul B) (Eventually.of_forall fun y => ?_)
        show ‖Φ y • ρ (x - y)‖ ≤ B * ‖ρ (x - y)‖
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hB y) (norm_nonneg _)
    _ = B * ∫ y, ‖ρ y‖ ∂μ := by
        rw [integral_const_mul]
        congr 1
        exact integral_sub_left_eq_self (fun y => ‖ρ y‖) μ x

lemma norm_iteratedFDeriv_smoothConv_le [μ.IsNegInvariant] {Φ : E → ℝ} (hΦ : Continuous Φ) {B : ℝ}
    (hB : ∀ y, |Φ y| ≤ B) (k : ℕ) :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (ρ : E → V), ContDiff ℝ k ρ →
      HasCompactSupport ρ → ∀ x,
      ‖iteratedFDeriv ℝ k (smoothConv μ Φ ρ) x‖ ≤ B * ∫ y, ‖iteratedFDeriv ℝ k ρ y‖ ∂μ := by
  induction k with
  | zero =>
    intro V _ _ ρ hρ hc x
    simp only [norm_iteratedFDeriv_zero]
    exact norm_smoothConv_le μ hB hc (by simpa using hρ.continuous) x
  | succ k ih =>
    intro V _ _ ρ hρ hc x
    have h1 : ContDiff ℝ 1 ρ := hρ.of_le (by exact_mod_cast Nat.le_add_left 1 k)
    rw [← norm_iteratedFDeriv_fderiv, fderiv_smoothConv μ hΦ hc h1]
    have h2 : ContDiff ℝ k (fderiv ℝ ρ) := hρ.fderiv_right (by exact_mod_cast le_rfl)
    have := ih (fderiv ℝ ρ) h2 (hc.fderiv ℝ) x
    simpa [norm_iteratedFDeriv_fderiv] using this

lemma smoothConv_approx [μ.IsNegInvariant] {Φ : E → ℝ} (hΦ : Continuous Φ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hlip : ∀ x y, |Φ x - Φ y| ≤ Λ * ‖x - y‖) (b : ContDiffBump (0 : E)) (x : E) :
    |smoothConv μ Φ (b.normed μ) x - Φ x| ≤ Λ * b.rOut := by
  set ρ := b.normed μ with hρdef
  have hc : HasCompactSupport ρ := b.hasCompactSupport_normed
  have hcont : Continuous ρ := b.continuous_normed
  have hint : Integrable ρ μ := hcont.integrable_of_hasCompactSupport hc
  have hint' : Integrable (fun y => ρ (x - y)) μ := hint.comp_sub_left x
  have hI : ∫ y, ρ (x - y) ∂μ = 1 := by
    rw [integral_sub_left_eq_self ρ μ x]; exact b.integral_normed
  have hΦint : Integrable (fun y => Φ y * ρ (x - y)) μ := by
    refine (hΦ.mul (hcont.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.mul_left ?_
    have : HasCompactSupport (fun y => ρ (x - y)) := by
      have h1 : HasCompactSupport (fun y => ρ (-y)) := hc.comp_homeomorph (Homeomorph.neg E)
      have h2 : HasCompactSupport (fun y => ρ (-(y - x))) := h1.comp_homeomorph (Homeomorph.subRight x)
      simpa using h2
    exact this
  have e : smoothConv μ Φ ρ x - Φ x = ∫ y, (Φ y - Φ x) * ρ (x - y) ∂μ := by
    have : ∫ y, (Φ y - Φ x) * ρ (x - y) ∂μ = ∫ y, Φ y * ρ (x - y) ∂μ - Φ x * ∫ y, ρ (x - y) ∂μ := by
      simp_rw [sub_mul]
      rw [integral_sub hΦint (hint'.const_mul _), integral_const_mul]
    rw [this, hI, mul_one]
    simp [smoothConv]
  rw [e, ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  calc ∫ y, ‖(Φ y - Φ x) * ρ (x - y)‖ ∂μ ≤ ∫ y, Λ * b.rOut * ρ (x - y) ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _)
          (hint'.const_mul _) (Eventually.of_forall fun y => ?_)
        show ‖(Φ y - Φ x) * ρ (x - y)‖ ≤ Λ * b.rOut * ρ (x - y)
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (b.nonneg_normed (μ := μ) (x - y))]
        by_cases h0 : ρ (x - y) = 0
        · have h0' : b.normed μ (x - y) = 0 := h0
          rw [h0]; simp [h0']
        · have hmem : x - y ∈ Function.support ρ := h0
          rw [hρdef, b.support_normed_eq] at hmem
          have hd : ‖x - y‖ < b.rOut := by simpa using hmem
          refine mul_le_mul_of_nonneg_right ?_ (b.nonneg_normed (μ := μ) (x - y))
          calc |Φ y - Φ x| ≤ Λ * ‖y - x‖ := hlip y x
            _ ≤ Λ * b.rOut := by
                rw [norm_sub_rev] at hd
                exact mul_le_mul_of_nonneg_left hd.le hΛ
    _ = Λ * b.rOut := by rw [integral_const_mul, hI, mul_one]

lemma smoothing [μ.IsNegInvariant] {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Φ : E → ℝ) (B Λ : ℝ), Continuous Φ → (∀ y, |Φ y| ≤ B) → 0 ≤ Λ →
      (∀ x y, |Φ x - Φ y| ≤ Λ * ‖x - y‖) →
      ∃ Ψ : E → ℝ, ContDiff ℝ 3 Ψ ∧ (∀ k ≤ 3, ∀ x, ‖iteratedFDeriv ℝ k Ψ x‖ ≤ B * C) ∧
        ∀ x, |Ψ x - Φ x| ≤ Λ * δ := by
  let b : ContDiffBump (0 : E) := ⟨δ / 2, δ, by positivity, by linarith⟩
  have hb : b.rOut = δ := rfl
  set ρ : E → ℝ := b.normed μ with hρ
  have hc : HasCompactSupport ρ := b.hasCompactSupport_normed
  have hρ3 : ContDiff ℝ 3 ρ := by
    have := b.contDiff_normed (μ := μ) (n := 3)
    simpa using this
  refine ⟨∑ k ∈ Finset.range 4, ∫ y, ‖iteratedFDeriv ℝ k ρ y‖ ∂μ,
    Finset.sum_nonneg fun k _ => integral_nonneg fun y => norm_nonneg _, ?_⟩
  intro Φ B Λ hΦ hB hΛ hlip
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  refine ⟨smoothConv μ Φ ρ, ?_, ?_, ?_⟩
  · rw [smoothConv_eq]
    exact hc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hΦ.locallyIntegrable hρ3
  · intro k hk x
    refine (norm_iteratedFDeriv_smoothConv_le μ hΦ hB k ρ (hρ3.of_le (by exact_mod_cast hk)) hc x).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hB0
    exact Finset.single_le_sum (f := fun k => ∫ y, ‖iteratedFDeriv ℝ k ρ y‖ ∂μ)
      (fun k _ => integral_nonneg fun y => norm_nonneg _) (Finset.mem_range.2 (by omega))
  · intro x
    have := smoothConv_approx μ hΦ hΛ hlip b x
    rwa [hb] at this

end Conv

section Trunc

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Coordinates to `H`. -/
def JJ (e : HilbertBasis ℕ ℝ H) (n : ℕ) : EuclideanSpace ℝ (Fin n) →L[ℝ] H :=
  ∑ i : Fin n, (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).smulRight (e i)

lemma JJ_apply (e : HilbertBasis ℕ ℝ H) (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    JJ e n v = ∑ i : Fin n, v i • e i := by
  simp [JJ]

lemma norm_JJ_le (e : HilbertBasis ℕ ℝ H) (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    ‖JJ e n v‖ ≤ ‖v‖ := by
  have horth : Orthonormal ℝ (fun i : Fin n => e (i : ℕ)) := e.orthonormal.comp _ Fin.val_injective
  have h1 := horth.inner_sum (fun i => v i) (fun i => v i) Finset.univ
  rw [← JJ_apply] at h1
  simp only [conj_trivial, real_inner_self_eq_norm_sq] at h1
  have h2 : ‖v‖ ^ 2 = ∑ i : Fin n, v i * v i := by
    rw [EuclideanSpace.norm_sq_eq]; simp [sq]
  have : ‖JJ e n v‖ ^ 2 = ‖v‖ ^ 2 := by rw [h1, h2]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this |>.le

/-- Coordinates from `H`. -/
def TT (e : HilbertBasis ℕ ℝ H) (n : ℕ) : H →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ContinuousLinearMap.adjoint (JJ e n)

lemma norm_TT_le (e : HilbertBasis ℕ ℝ H) (n : ℕ) : ‖TT e n‖ ≤ 1 := by
  unfold TT
  rw [LinearIsometryEquiv.norm_map]
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by simpa using norm_JJ_le e n v)

lemma TT_apply (e : HilbertBasis ℕ ℝ H) (n : ℕ) (x : H) (i : Fin n) :
    TT e n x i = inner ℝ (e i) x := by
  unfold TT
  have h := ContinuousLinearMap.adjoint_inner_right (JJ e n) (EuclideanSpace.single i (1:ℝ)) x
  rw [EuclideanSpace.inner_single_left] at h
  have e1 : JJ e n (EuclideanSpace.single i (1:ℝ)) = e i := by
    rw [JJ_apply]; simp [PiLp.single_apply]
  rw [e1] at h
  simpa using h

/-- The orthogonal projection onto the first `n` basis vectors. -/
def PP (e : HilbertBasis ℕ ℝ H) (n : ℕ) (x : H) : H := JJ e n (TT e n x)

lemma continuous_PP (e : HilbertBasis ℕ ℝ H) (n : ℕ) : Continuous (PP e n) :=
  (JJ e n).continuous.comp (TT e n).continuous

lemma inner_basis_sub_PP (e : HilbertBasis ℕ ℝ H) (n m : ℕ) (x : H) :
    inner ℝ (e m) (x - PP e n x) = if m < n then 0 else inner ℝ (e m) x := by
  have horth : Orthonormal ℝ (fun i : Fin n => e (i : ℕ)) := e.orthonormal.comp _ Fin.val_injective
  have hP : PP e n x = ∑ i : Fin n, inner ℝ (e i) x • e (i : ℕ) := by
    unfold PP; rw [JJ_apply]; simp_rw [TT_apply]
  rw [inner_sub_right, hP, inner_sum]
  simp_rw [inner_smul_right]
  have hon := (orthonormal_iff_ite.1 e.orthonormal)
  simp_rw [hon]
  by_cases hm : m < n
  · rw [if_pos hm, Finset.sum_eq_single ⟨m, hm⟩]
    · simp
    · intro b _ hb
      have : m ≠ (b : ℕ) := fun h => hb (Fin.ext h.symm)
      simp [this]
    · simp
  · rw [if_neg hm, Finset.sum_eq_zero, sub_zero]
    intro b _
    have : m ≠ (b : ℕ) := fun h => hm (h ▸ b.2)
    simp [this]

lemma norm_sub_PP_sq (e : HilbertBasis ℕ ℝ H) (n : ℕ) (x : H) :
    ‖x - PP e n x‖ ^ 2 = ∑' m : {m : ℕ // n ≤ m}, (inner ℝ (e m) x) ^ 2 := by
  have h := (e.hasSum_inner_mul_inner (x - PP e n x) (x - PP e n x))
  rw [real_inner_self_eq_norm_sq] at h
  have h2 : ∀ m : ℕ, inner ℝ (x - PP e n x) (e m) * inner ℝ (e m) (x - PP e n x) =
      Set.indicator {m : ℕ | n ≤ m} (fun m => (inner ℝ (e m) x) ^ 2) m := by
    intro m
    rw [real_inner_comm, inner_basis_sub_PP]
    by_cases hm : m < n
    · simp [hm, Set.indicator, not_le.2 hm]
    · simp [hm, Set.indicator, not_lt.1 hm, sq]
  simp_rw [h2] at h
  rw [← h.tsum_eq]
  exact (tsum_subtype {m : ℕ | n ≤ m} (fun m => (inner ℝ (e m) x) ^ 2)).symm

/-- The property of the constant `C` produced by the smoothing of a truncation. -/
def SmoothProp (e : HilbertBasis ℕ ℝ H) (n : ℕ) (δ C : ℝ) : Prop :=
  ∀ (Q : H → ℝ) (B Λ : ℝ), Continuous Q → (∀ y, |Q y| ≤ B) → 0 ≤ Λ →
      (∀ x y, |Q x - Q y| ≤ Λ * ‖x - y‖) →
      ∃ f : H → ℝ, ContDiff ℝ 3 f ∧ (∀ k ≤ 3, ∀ x, ‖iteratedFDeriv ℝ k f x‖ ≤ B * C) ∧
        ∀ x, |f x - Q (PP e n x)| ≤ Λ * δ

/-- Smoothing of the truncation of a bounded Lipschitz function. -/
lemma trunc_smooth (e : HilbertBasis ℕ ℝ H) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ SmoothProp e n δ C := by
  obtain ⟨C, hC, h⟩ := smoothing (volume : Measure (EuclideanSpace ℝ (Fin n))) hδ
  refine ⟨C, hC, fun Q B Λ hQ hB hΛ hlip => ?_⟩
  obtain ⟨Ψ, hΨ, hΨb, hΨa⟩ := h (fun v => Q (JJ e n v)) B Λ (hQ.comp (JJ e n).continuous)
    (fun y => hB _) hΛ (fun x y => by
      refine (hlip _ _).trans ?_
      rw [← map_sub]
      exact mul_le_mul_of_nonneg_left (norm_JJ_le e n _) hΛ)
  refine ⟨fun x => Ψ (TT e n x), hΨ.comp (TT e n).contDiff, ?_, ?_⟩
  · intro k hk x
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
    have e1 := (TT e n).iteratedFDeriv_comp_right (hΨ.of_le (by exact_mod_cast hk)) x le_rfl
    have e2 : (fun x => Ψ (TT e n x)) = Ψ ∘ (TT e n) := rfl
    rw [e2, e1]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have hT := norm_TT_le e n
    have : ∏ _i : Fin k, ‖TT e n‖ ≤ 1 := by
      rw [Finset.prod_const]; exact pow_le_one₀ (norm_nonneg _) hT
    calc ‖iteratedFDeriv ℝ k Ψ (TT e n x)‖ * ∏ _i : Fin k, ‖TT e n‖
        ≤ (B * C) * 1 := mul_le_mul (hΨb k hk _) this (Finset.prod_nonneg fun _ _ => norm_nonneg _)
          (mul_nonneg hB0 hC)
      _ = B * C := mul_one _
  · intro x
    exact hΨa (TT e n x)

end Trunc

section VarHyb

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
lemma integrable_of_integrable_sq {V : Ω → H} (hV : AEMeasurable V P)
    (h : Integrable (fun ω => ‖V ω‖ ^ 2) P) : Integrable V P := by
  rw [← integrable_norm_iff hV.aestronglyMeasurable]
  refine Integrable.mono' ((integrable_const (1:ℝ)).add h) hV.norm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖V ω‖ - 1)]

lemma integral_inner_indep {V W : Ω → H} (hV : Measurable V) (hW : Measurable W)
    (hind : IndepFun V W P) (hV2 : Integrable (fun ω => ‖V ω‖ ^ 2) P)
    (hW2 : Integrable (fun ω => ‖W ω‖ ^ 2) P) (hW0 : ∫ ω, W ω ∂P = 0) :
    Integrable (fun ω => inner ℝ (V ω) (W ω)) P ∧ ∫ ω, inner ℝ (V ω) (W ω) ∂P = 0 := by
  have hW1 : Integrable W P := integrable_of_integrable_sq hW.aemeasurable hW2
  have hint : Integrable (fun ω => inner ℝ (V ω) (W ω)) P := by
    refine Integrable.mono' ((hV2.add hW2).div_const 2)
      (hV.inner hW).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (‖V ω‖ - ‖W ω‖)]
  refine ⟨hint, ?_⟩
  have : IsProbabilityMeasure (P.map V) := (Measure.isProbabilityMeasure_map_iff hV.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure (P.map W) := (Measure.isProbabilityMeasure_map_iff hW.aemeasurable).2 inferInstance
  have hprod := hind.map_prod_eq_prod_map_map hV.aemeasurable hW.aemeasurable
  have hg : Continuous fun q : H × H => inner ℝ q.1 q.2 := continuous_fst.inner continuous_snd
  have h1 : ∫ ω, inner ℝ (V ω) (W ω) ∂P =
      ∫ q, inner ℝ q.1 q.2 ∂(P.map fun ω => (V ω, W ω)) := by
    rw [integral_map (hV.prodMk hW).aemeasurable hg.aestronglyMeasurable]
  have hint2 : Integrable (fun q : H × H => inner ℝ q.1 q.2) ((P.map V).prod (P.map W)) := by
    rw [← hprod]
    exact (integrable_map_measure hg.aestronglyMeasurable (hV.prodMk hW).aemeasurable).2 hint
  rw [h1, hprod, integral_prod _ hint2]
  have hW1' : Integrable (fun w : H => w) (P.map W) :=
    (integrable_map_measure aestronglyMeasurable_id hW.aemeasurable).2 hW1
  have hmean : ∫ w, w ∂(P.map W) = 0 := by
    have h : ∫ w, id w ∂(P.map W) = ∫ ω, id (W ω) ∂P := integral_map hW.aemeasurable aestronglyMeasurable_id
    simpa using h.trans hW0
  have : ∀ v : H, ∫ w, inner ℝ v w ∂(P.map W) = 0 := by
    intro v
    rw [integral_inner hW1', hmean, inner_zero_right]
  simp [this]

lemma sq_add_indep {V W : Ω → H} (hV : Measurable V) (hW : Measurable W)
    (hind : IndepFun V W P) (hV2 : Integrable (fun ω => ‖V ω‖ ^ 2) P)
    (hW2 : Integrable (fun ω => ‖W ω‖ ^ 2) P) (hW0 : ∫ ω, W ω ∂P = 0) (c : ℝ) :
    Integrable (fun ω => ‖V ω + c • W ω‖ ^ 2) P ∧
      ∫ ω, ‖V ω + c • W ω‖ ^ 2 ∂P = ∫ ω, ‖V ω‖ ^ 2 ∂P + c ^ 2 * ∫ ω, ‖W ω‖ ^ 2 ∂P := by
  obtain ⟨hi, hz⟩ := integral_inner_indep hV hW hind hV2 hW2 hW0
  have e : ∀ ω, ‖V ω + c • W ω‖ ^ 2 =
      ‖V ω‖ ^ 2 + (2 * c) * inner ℝ (V ω) (W ω) + c ^ 2 * ‖W ω‖ ^ 2 := by
    intro ω
    rw [norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hI : Integrable (fun ω => ‖V ω‖ ^ 2 + (2 * c) * inner ℝ (V ω) (W ω) + c ^ 2 * ‖W ω‖ ^ 2) P :=
    (hV2.add (hi.const_mul _)).add (hW2.const_mul _)
  simp_rw [e]
  refine ⟨hI, ?_⟩
  rw [integral_add (f := fun ω => ‖V ω‖ ^ 2 + (2 * c) * inner ℝ (V ω) (W ω))
      (g := fun ω => c ^ 2 * ‖W ω‖ ^ 2) (hV2.add (hi.const_mul _)) (hW2.const_mul _),
    integral_add (f := fun ω => ‖V ω‖ ^ 2) (g := fun ω => (2 * c) * inner ℝ (V ω) (W ω))
      hV2 (hi.const_mul _), integral_const_mul, integral_const_mul, hz]
  ring


lemma law_facts {W : Ω → H} (hW : Measurable W) {ν : Measure H} (hν : P.map W = ν)
    (hint2 : Integrable (fun a : H => ‖a‖ ^ 2) ν) (hint1 : Integrable (fun a : H => ‖a‖) ν)
    (h0 : ∫ a, a ∂ν = 0) (T : H →L[ℝ] H) :
    Integrable (fun ω => ‖T (W ω)‖ ^ 2) P ∧ ∫ ω, ‖T (W ω)‖ ^ 2 ∂P = ∫ a, ‖T a‖ ^ 2 ∂ν ∧
      ∫ ω, T (W ω) ∂P = 0 := by
  have hTc : Continuous fun a : H => ‖T a‖ ^ 2 := by fun_prop
  have hint : Integrable (fun a : H => ‖T a‖ ^ 2) ν := by
    refine Integrable.mono' (hint2.const_mul (‖T‖ ^ 2)) hTc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖T a‖ ^ 2 ≤ (‖T‖ * ‖a‖) ^ 2 := by
          gcongr; exact T.le_opNorm a
      _ = ‖T‖ ^ 2 * ‖a‖ ^ 2 := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [← hν] at hint
    exact (integrable_map_measure hTc.aestronglyMeasurable hW.aemeasurable).1 hint
  · rw [← hν, integral_map hW.aemeasurable hTc.aestronglyMeasurable]
  · have hid : Integrable (fun a : H => a) ν := by
      refine ⟨aestronglyMeasurable_id, ?_⟩
      simpa [HasFiniteIntegral] using hint1.2
    rw [← hν] at hid h0
    have h1 : ∫ ω, T (W ω) ∂P = ∫ a, T a ∂(P.map W) := by
      rw [integral_map hW.aemeasurable T.continuous.aestronglyMeasurable]
    rw [h1, ContinuousLinearMap.integral_comp_comm T hid, h0, map_zero]

lemma Matching.tau_eq {μ γ : Measure H} (M : Matching μ γ) (T : H →L[ℝ] H) :
    ∫ a, ‖T a‖ ^ 2 ∂μ = ∫ a, ‖T a‖ ^ 2 ∂γ := by
  have := M.eqB ((innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ).bilinearComp T T)
  simpa [real_inner_self_eq_norm_sq] using this

variable {N : ℕ} {Y Z : Fin N → Ω → H} {μ γ : Measure H}

lemma var_hyb (S : Setup P Y Z μ γ) (M : Matching μ γ) (T : H →L[ℝ] H) (c : ℝ)
    (A I : Finset (Fin N)) :
    Integrable (fun ω => ‖T (hyb Y Z c A I ω)‖ ^ 2) P ∧
      ∫ ω, ‖T (hyb Y Z c A I ω)‖ ^ 2 ∂P = c ^ 2 * I.card * ∫ a, ‖T a‖ ^ 2 ∂μ := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    have : ∀ ω, hyb Y Z c A ∅ ω = 0 := fun ω => by simp [hyb]
    simp [this]
  | insert i I hi ih =>
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨hindY, hindZ⟩ := indep_hyb S.measY S.measZ S.indep c A I hi
    have hμ2 := M.intμ 2 (by norm_num)
    have hμ1 : Integrable (fun a : H => ‖a‖) μ := by simpa using M.intμ 1 (by norm_num)
    have hγ2 := M.intγ 2 (by norm_num)
    have hγ1 : Integrable (fun a : H => ‖a‖) γ := by simpa using M.intγ 1 (by norm_num)
    have hmeasR : Measurable fun ω => T (hyb Y Z c A I ω) :=
      T.continuous.measurable.comp (S.measurable_hyb' c A I)
    have hsplit : ∀ ω, T (hyb Y Z c A (insert i I) ω) =
        T (hyb Y Z c A I ω) + c • T (if i ∈ A then Y i ω else Z i ω) := by
      intro ω
      have : hyb Y Z c A (insert i I) ω = hyb Y Z c A I ω + c • (if i ∈ A then Y i ω else Z i ω) := by
        unfold hyb
        rw [Finset.sum_insert hi, smul_add, add_comm]
      rw [this, map_add, map_smul]
    simp_rw [hsplit]
    rw [Finset.card_insert_of_notMem hi]
    by_cases hiA : i ∈ A
    · simp only [hiA, ↓reduceIte]
      obtain ⟨a1, a2, a3⟩ := law_facts (P := P) (S.measY i) (S.lawY i) hμ2 hμ1 M.cenμ T
      have hind' : IndepFun (fun ω => T (hyb Y Z c A I ω)) (fun ω => T (Y i ω)) P :=
        hindY.comp T.continuous.measurable T.continuous.measurable
      obtain ⟨b1, b2⟩ := sq_add_indep hmeasR (T.continuous.measurable.comp (S.measY i)) hind' ih1 a1 a3 c
      simp only [Function.comp_apply] at b1 b2
      refine ⟨b1, ?_⟩
      rw [b2, a2, ih2]; push_cast; ring
    · simp only [hiA, ↓reduceIte]
      obtain ⟨a1, a2, a3⟩ := law_facts (P := P) (S.measZ i) (S.lawZ i) hγ2 hγ1 M.cenγ T
      have hind' : IndepFun (fun ω => T (hyb Y Z c A I ω)) (fun ω => T (Z i ω)) P :=
        hindZ.comp T.continuous.measurable T.continuous.measurable
      obtain ⟨b1, b2⟩ := sq_add_indep hmeasR (T.continuous.measurable.comp (S.measZ i)) hind' ih1 a1 a3 c
      simp only [Function.comp_apply] at b1 b2
      refine ⟨b1, ?_⟩
      rw [b2, a2, ih2, M.tau_eq T]; push_cast; ring

end VarHyb

section West

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {N : ℕ} {Y Z : Fin N → Ω → H} {μ γ : Measure H}

/-- The truncation `x - PP x` as a continuous linear map. -/
def tailCLM (e : HilbertBasis ℕ ℝ H) (n : ℕ) : H →L[ℝ] H :=
  ContinuousLinearMap.id ℝ H - (JJ e n).comp (TT e n)

lemma tailCLM_apply (e : HilbertBasis ℕ ℝ H) (n : ℕ) (x : H) : tailCLM e n x = x - PP e n x := rfl

/-- Uniform Lindeberg estimate for Lipschitz bounded test functions, for hybrid sums. -/
lemma W_est (e : HilbertBasis ℕ ℝ H) (n : ℕ) {δ C : ℝ} (hδ : 0 < δ) (hC : SmoothProp e n δ C)
    (S : Setup P Y Z μ γ) (M : Matching μ γ) {Q : H → ℝ} {B Λ : ℝ} (hQ : Continuous Q)
    (hB : ∀ y, |Q y| ≤ B) (hΛ : 0 ≤ Λ) (hlip : ∀ x y, |Q x - Q y| ≤ Λ * ‖x - y‖)
    (hτ : ∫ a, ‖a - PP e n a‖ ^ 2 ∂μ ≤ δ ^ 2) {c : ℝ} (hc : 0 ≤ c) (hcN : c ^ 2 * N ≤ 1)
    (A I : Finset (Fin N)) (hAI : A ⊆ I) :
    |∫ ω, Q (hyb Y Z c A I ω) ∂P - ∫ ω, Q (hyb Y Z c ∅ I ω) ∂P| ≤
      4 * Λ * δ + A.card * ((B * C) * c ^ (2 + 1) *
        ((∫ a, ‖a‖ ^ (2 + 1) ∂μ) + ∫ a, ‖a‖ ^ (2 + 1) ∂γ) / ((2 + 1)! : ℝ)) := by
  obtain ⟨f, hf, hfb, hfa⟩ := hC Q B Λ hQ hB hΛ hlip
  have hf3 : ContDiff ℝ (2 + 1) f := by norm_num; exact hf
  have hfB : ∀ x, |f x| ≤ B * C := fun x => by
    have := hfb 0 (by norm_num) x
    simpa [norm_iteratedFDeriv_zero] using this
  have hind3 := ind3 S M hf3 (L := B * C) (fun x => by simpa using hfb 3 le_rfl x) (B := B * C) hfB
    (K := B * C) (fun x => hfb 2 (by norm_num) x) hc A I hAI
  have hfc : Continuous f := hf.continuous
  -- approximation for a general hybrid
  have happ : ∀ A' I' : Finset (Fin N),
      |∫ ω, Q (hyb Y Z c A' I' ω) ∂P - ∫ ω, f (hyb Y Z c A' I' ω) ∂P| ≤ 2 * Λ * δ := by
    intro A' I'
    have hmeas := S.measurable_hyb' c A' I'
    obtain ⟨hv1, hv2⟩ := var_hyb S M (tailCLM e n) c A' I'
    have hcard : (I'.card : ℝ) ≤ N := by
      have : I'.card ≤ N := by
        calc I'.card ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_univ _
          _ = N := by simp
      exact_mod_cast this
    have hτ' : ∫ a, ‖tailCLM e n a‖ ^ 2 ∂μ ≤ δ ^ 2 := by simpa [tailCLM_apply] using hτ
    have hvar : ∫ ω, ‖tailCLM e n (hyb Y Z c A' I' ω)‖ ^ 2 ∂P ≤ δ ^ 2 := by
      rw [hv2]
      have hnn : 0 ≤ ∫ a, ‖tailCLM e n a‖ ^ 2 ∂μ := integral_nonneg fun a => by positivity
      calc c ^ 2 * I'.card * ∫ a, ‖tailCLM e n a‖ ^ 2 ∂μ
          ≤ 1 * ∫ a, ‖tailCLM e n a‖ ^ 2 ∂μ := by
            refine mul_le_mul_of_nonneg_right ?_ hnn
            calc c ^ 2 * I'.card ≤ c ^ 2 * N := mul_le_mul_of_nonneg_left hcard (by positivity)
              _ ≤ 1 := hcN
        _ ≤ δ ^ 2 := by linarith
    have hQi : Integrable (fun ω => Q (hyb Y Z c A' I' ω)) P :=
      Integrable.of_bound (hQ.measurable.comp hmeas).aestronglyMeasurable B
        (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hB _)
    have hfi : Integrable (fun ω => f (hyb Y Z c A' I' ω)) P :=
      Integrable.of_bound (hfc.measurable.comp hmeas).aestronglyMeasurable (B * C)
        (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hfB _)
    rw [← integral_sub hQi hfi, ← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hpt : ∀ ω, ‖Q (hyb Y Z c A' I' ω) - f (hyb Y Z c A' I' ω)‖ ≤
        (3 / 2) * Λ * δ + (Λ / (2 * δ)) * ‖tailCLM e n (hyb Y Z c A' I' ω)‖ ^ 2 := by
      intro ω
      set R := hyb Y Z c A' I' ω
      have h1 := hlip R (PP e n R)
      have h2 := hfa R
      have h3 : ‖R - PP e n R‖ ≤ δ / 2 + ‖R - PP e n R‖ ^ 2 / (2 * δ) := by
        rw [div_add_div _ _ (by norm_num) (by positivity), le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (‖R - PP e n R‖ - δ)]
      rw [tailCLM_apply, Real.norm_eq_abs]
      have h4 : |Q R - f R| ≤ |Q R - Q (PP e n R)| + |f R - Q (PP e n R)| := by
        have := abs_sub_le (Q R) (Q (PP e n R)) (f R)
        rw [abs_sub_comm (Q (PP e n R)) (f R)] at this
        exact this
      have h5 : Λ * ‖R - PP e n R‖ ≤ Λ * (δ / 2 + ‖R - PP e n R‖ ^ 2 / (2 * δ)) :=
        mul_le_mul_of_nonneg_left h3 hΛ
      calc |Q R - f R| ≤ Λ * ‖R - PP e n R‖ + Λ * δ := h4.trans (add_le_add h1 h2)
        _ ≤ Λ * (δ / 2 + ‖R - PP e n R‖ ^ 2 / (2 * δ)) + Λ * δ := by linarith
        _ = (3 / 2) * Λ * δ + (Λ / (2 * δ)) * ‖R - PP e n R‖ ^ 2 := by
            field_simp; ring
    calc ∫ ω, ‖Q (hyb Y Z c A' I' ω) - f (hyb Y Z c A' I' ω)‖ ∂P
        ≤ ∫ ω, ((3 / 2) * Λ * δ + (Λ / (2 * δ)) * ‖tailCLM e n (hyb Y Z c A' I' ω)‖ ^ 2) ∂P := by
          refine integral_mono (hQi.sub hfi).norm
            ((integrable_const _).add (hv1.const_mul _)) hpt
      _ = (3 / 2) * Λ * δ + (Λ / (2 * δ)) * ∫ ω, ‖tailCLM e n (hyb Y Z c A' I' ω)‖ ^ 2 ∂P := by
          rw [integral_add (integrable_const _) (hv1.const_mul _),
            integral_const_mul (Λ / (2 * δ))]
          simp
      _ ≤ (3 / 2) * Λ * δ + (Λ / (2 * δ)) * δ ^ 2 := by
          gcongr
      _ = 2 * Λ * δ := by field_simp; ring
  have h1 := happ A I
  have h2 := happ ∅ I
  set a1 := ∫ ω, Q (hyb Y Z c A I ω) ∂P
  set a2 := ∫ ω, Q (hyb Y Z c ∅ I ω) ∂P
  set b1 := ∫ ω, f (hyb Y Z c A I ω) ∂P
  set b2 := ∫ ω, f (hyb Y Z c ∅ I ω) ∂P
  have e1 : a1 - a2 = (a1 - b1) + (b1 - b2) + (b2 - a2) := by ring
  rw [e1]
  have := abs_add_three (a1 - b1) (b1 - b2) (b2 - a2)
  rw [abs_sub_comm b2 a2] at this
  linarith

end West

section QRed

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {N : ℕ} {Y Z : Fin N → Ω → H} {μ γ : Measure H}

lemma Q_estimate4 (e : HilbertBasis ℕ ℝ H) (n : ℕ) {δ C : ℝ} (hδ : 0 < δ) (hC0 : 0 ≤ C)
    (hC : SmoothProp e n δ C) (S : Setup P Y Z μ γ) (M : Matching μ γ) {Q : H → ℝ} {B Λ : ℝ}
    (hQc : Continuous Q) (hQd : Differentiable ℝ Q) (hB : ∀ y, |Q y| ≤ B) (hΛ : 0 ≤ Λ)
    (hL1 : ∀ x, ‖fderiv ℝ Q x‖ ≤ Λ) (hτ : ∫ a, ‖a - PP e n a‖ ^ 2 ∂μ ≤ δ ^ 2)
    {c : ℝ} (hc : 0 ≤ c) (hcN : c ^ 2 * N ≤ 1) (hlaw : P.map (hyb Y Z c ∅ Finset.univ) = γ)
    (j : Fin N) :
    |∫ ω, Q (hyb Y Z c (pref N j) (Finset.univ.erase j) ω) ∂P - ∫ z, Q z ∂γ| ≤
      4 * Λ * δ + N * ((B * C) * c ^ (2 + 1) *
        ((∫ a, ‖a‖ ^ (2 + 1) ∂μ) + ∫ a, ‖a‖ ^ (2 + 1) ∂γ) / ((2 + 1)! : ℝ))
        + Λ * c * ∫ b, ‖b‖ ∂γ := by
  have hsub : pref N j ⊆ Finset.univ.erase j := by
    intro i hi
    simp only [pref, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro h; subst h; omega
  have hlipQ : ∀ x y, |Q x - Q y| ≤ Λ * ‖x - y‖ := fun x y => by
    have := lipschitz_of_fderiv hQd hL1 x (y - x)
    rw [add_sub_cancel, abs_sub_comm] at this
    rw [norm_sub_rev]
    exact this
  have h3 := W_est e n hδ hC S M hQc hB hΛ hlipQ hτ hc hcN (pref N j) (Finset.univ.erase j) hsub
  have hδn : 0 ≤ (B * C) * c ^ (2 + 1) * ((∫ a, ‖a‖ ^ (2 + 1) ∂μ) + ∫ a, ‖a‖ ^ (2 + 1) ∂γ) / ((2 + 1)! : ℝ) := by
    have n1 : 0 ≤ ∫ a, ‖a‖ ^ (2 + 1) ∂μ := integral_nonneg fun a => by positivity
    have n2 : 0 ≤ ∫ a, ‖a‖ ^ (2 + 1) ∂γ := integral_nonneg fun a => by positivity
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
    have : 0 ≤ C := hC0
    positivity
  have hcard : ((pref N j).card : ℝ) ≤ N := by
    have : (pref N j).card ≤ N := by
      calc (pref N j).card ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_univ _
        _ = N := by simp
    exact_mod_cast this
  have h3' : |∫ ω, Q (hyb Y Z c (pref N j) (Finset.univ.erase j) ω) ∂P -
      ∫ ω, Q (hyb Y Z c ∅ (Finset.univ.erase j) ω) ∂P| ≤ 4 * Λ * δ + N * ((B * C) * c ^ (2 + 1) *
        ((∫ a, ‖a‖ ^ (2 + 1) ∂μ) + ∫ a, ‖a‖ ^ (2 + 1) ∂γ) / ((2 + 1)! : ℝ)) :=
    h3.trans (by have := mul_le_mul_of_nonneg_right hcard hδn; linarith)
  -- compare `hyb ∅ (univ.erase j)` with `hyb ∅ univ`
  have hdiff : ∀ ω, hyb Y Z c ∅ Finset.univ ω =
      hyb Y Z c ∅ (Finset.univ.erase j) ω + c • Z j ω := by
    intro ω
    have := hyb_Z Y Z c (A := ∅) (I := Finset.univ) (i := j) (Finset.mem_univ _) ω
    simpa using this
  have hmeasE := S.measurable_hyb' c ∅ (Finset.univ.erase j)
  have hint1 : Integrable (fun ω => Q (hyb Y Z c ∅ (Finset.univ.erase j) ω)) P :=
    Integrable.of_bound (hQc.measurable.comp hmeasE).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hB _)
  have hint2 : Integrable (fun ω => Q (hyb Y Z c ∅ Finset.univ ω)) P :=
    Integrable.of_bound (hQc.measurable.comp (S.measurable_hyb' c ∅ Finset.univ)).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hB _)
  have hZint : Integrable (fun ω => ‖Z j ω‖) P := by
    have : Integrable (fun b : H => ‖b‖) γ := by
      simpa using M.intγ 1 (by norm_num)
    have h' : Integrable (fun b : H => ‖b‖) (P.map (Z j)) := by rw [S.lawZ j]; exact this
    exact (integrable_map_measure h'.aestronglyMeasurable (S.measZ j).aemeasurable).1 h'
  have hlip : |∫ ω, Q (hyb Y Z c ∅ Finset.univ ω) ∂P - ∫ ω, Q (hyb Y Z c ∅ (Finset.univ.erase j) ω) ∂P|
      ≤ Λ * c * ∫ b, ‖b‖ ∂γ := by
    rw [← integral_sub hint2 hint1]
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hI : ∫ ω, ‖Z j ω‖ ∂P = ∫ b, ‖b‖ ∂γ := by
      rw [← S.lawZ j, integral_map (S.measZ j).aemeasurable (by fun_prop : Continuous fun b : H => ‖b‖).aestronglyMeasurable]
    calc ∫ ω, ‖Q (hyb Y Z c ∅ Finset.univ ω) - Q (hyb Y Z c ∅ (Finset.univ.erase j) ω)‖ ∂P
        ≤ ∫ ω, Λ * c * ‖Z j ω‖ ∂P := by
          refine integral_mono (hint2.sub hint1).norm (hZint.const_mul _) fun ω => ?_
          rw [hdiff ω, Real.norm_eq_abs]
          have := lipschitz_of_fderiv hQd hL1 (hyb Y Z c ∅ (Finset.univ.erase j) ω) (c • Z j ω)
          simp only [add_sub_cancel_left] at this ⊢
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc] at this
          simpa [mul_assoc] using this
      _ = Λ * c * ∫ b, ‖b‖ ∂γ := by rw [integral_const_mul, hI]
  have hEγ : ∫ ω, Q (hyb Y Z c ∅ Finset.univ ω) ∂P = ∫ z, Q z ∂γ := by
    rw [← hlaw, integral_map (S.measurable_hyb' c ∅ Finset.univ).aemeasurable hQc.aestronglyMeasurable]
  rw [← hEγ]
  have := abs_add_le (∫ ω, Q (hyb Y Z c (pref N j) (Finset.univ.erase j) ω) ∂P -
      ∫ ω, Q (hyb Y Z c ∅ (Finset.univ.erase j) ω) ∂P)
    (∫ ω, Q (hyb Y Z c ∅ (Finset.univ.erase j) ω) ∂P - ∫ ω, Q (hyb Y Z c ∅ Finset.univ ω) ∂P)
  have e : ∫ ω, Q (hyb Y Z c (pref N j) (Finset.univ.erase j) ω) ∂P -
      ∫ ω, Q (hyb Y Z c ∅ Finset.univ ω) ∂P =
      (∫ ω, Q (hyb Y Z c (pref N j) (Finset.univ.erase j) ω) ∂P -
        ∫ ω, Q (hyb Y Z c ∅ (Finset.univ.erase j) ω) ∂P) +
      (∫ ω, Q (hyb Y Z c ∅ (Finset.univ.erase j) ω) ∂P - ∫ ω, Q (hyb Y Z c ∅ Finset.univ ω) ∂P) := by
    ring
  rw [e]
  rw [abs_sub_comm] at hlip
  linarith


end QRed

section Core4

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {N : ℕ} {Y Z : Fin N → Ω → H} {μ γ : Measure H}

/-- Core Lindeberg estimate for the `C_b^4` form: the explicit bound with free smoothing
parameters. -/
lemma core4 (e : HilbertBasis ℕ ℝ H) (n : ℕ) {δ C : ℝ} (hδ : 0 < δ) (hC0 : 0 ≤ C)
    (hC : SmoothProp e n δ C) (S : Setup P Y Z μ γ) (M : Matching μ γ) {c : ℝ} (hc : 0 < c)
    (hN : 0 < N) (hcN : c ^ 2 * N = 1) (hlaw : P.map (hyb Y Z c ∅ Finset.univ) = γ) {F : H → ℝ}
    (hF : ContDiff ℝ 4 F) (hFb : ∀ j ≤ 4, ∀ x, ‖iteratedFDeriv ℝ j F x‖ ≤ 1)
    (hτ : ∫ a, ‖a - PP e n a‖ ^ 2 ∂μ ≤ δ ^ 2) :
    |∫ ω, F (hyb Y Z c Finset.univ Finset.univ ω) ∂P - ∫ z, F z ∂γ -
        (1 / 6) * c * ∫ z, Qf μ F z ∂γ| ≤
      ((∫ a, ‖a‖ ^ 4 ∂μ) + ∫ a, ‖a‖ ^ 4 ∂γ) / 24 / N + (2 / 3) * c * (∫ a, ‖a‖ ^ 3 ∂μ) * δ +
        ((∫ a, ‖a‖ ^ 3 ∂μ) * C * ((∫ a, ‖a‖ ^ 3 ∂μ) + ∫ a, ‖a‖ ^ 3 ∂γ) / 36 +
          (∫ a, ‖a‖ ^ 3 ∂μ) * (∫ b, ‖b‖ ∂γ) / 6) / N := by
  have hint3 := M.intμ 3 (by norm_num)
  set Λ := momCLM μ hint3 with hΛ
  set m3 : ℝ := ∫ a, ‖a‖ ^ 3 ∂μ with hm3
  have hm3nn : 0 ≤ m3 := integral_nonneg fun a => by positivity
  have hΛn : ‖Λ‖ ≤ m3 := norm_momCLM_le μ hint3
  have hQdef : Qf μ F = fun z => Λ (iteratedFDeriv ℝ 3 F z) := rfl
  have hF' : ContDiff ℝ (1 + 3) F := by norm_num; exact hF
  have hQ : ContDiff ℝ 1 (Qf μ F) := by
    rw [hQdef]
    exact contDiff_clm_iteratedFDeriv Λ (n := 1) hF'
  have hQb : ∀ i ≤ 1, ∀ x, ‖iteratedFDeriv ℝ i (Qf μ F) x‖ ≤ m3 := by
    intro i hi x
    rw [hQdef]
    refine (norm_iteratedFDeriv_clm_iteratedFDeriv Λ (n := 1) hF' hi x).trans ?_
    calc ‖Λ‖ * ‖iteratedFDeriv ℝ (i + 3) F x‖ ≤ m3 * 1 :=
          mul_le_mul hΛn (hFb _ (by omega) x) (norm_nonneg _) hm3nn
      _ = m3 := mul_one _
  have hF4 : ContDiff ℝ (3 + 1) F := by norm_num; exact hF
  have h4 := ind4 S M hF4 (L := 1) (fun x => by simpa using hFb 4 (by norm_num) x) (B := 1)
    (fun x => by simpa using hFb 0 (by norm_num) x) (K := 1) (fun x => hFb 3 (by norm_num) x)
    hc.le N le_rfl
  rw [pref_self] at h4
  set m3γ : ℝ := ∫ a, ‖a‖ ^ 3 ∂γ with hm3γ
  set m4μ : ℝ := ∫ a, ‖a‖ ^ 4 ∂μ with hm4μ
  set m4γ : ℝ := ∫ a, ‖a‖ ^ 4 ∂γ with hm4γ
  set m1γ : ℝ := ∫ b, ‖b‖ ∂γ with hm1γ
  set I : ℝ := ∫ z, Qf μ F z ∂γ with hI
  have hQd : Differentiable ℝ (Qf μ F) := hQ.differentiable (by norm_num)
  have hQc : Continuous (Qf μ F) := hQ.continuous
  have hj : ∀ j : Fin N, |∫ ω, Qf μ F (hyb Y Z c (pref N j) (Finset.univ.erase j) ω) ∂P - I| ≤
      4 * m3 * δ + N * ((m3 * C) * c ^ (2 + 1) * (m3 + m3γ) / ((2 + 1)! : ℝ)) + m3 * c * m1γ := by
    intro j
    exact Q_estimate4 e n hδ hC0 hC S M hQc hQd (fun x => by simpa using hQb 0 (by norm_num) x) hm3nn
      (fun x => by simpa using hQb 1 (by norm_num) x) hτ hc.le hcN.le hlaw j
  have hEγ : ∫ ω, F (hyb Y Z c ∅ Finset.univ ω) ∂P = ∫ z, F z ∂γ := by
    rw [← hlaw, integral_map (S.measurable_hyb' c ∅ Finset.univ).aemeasurable
      hF.continuous.aestronglyMeasurable]
  rw [hEγ] at h4
  set X1 := ∫ ω, F (hyb Y Z c Finset.univ Finset.univ ω) ∂P with hX1
  set X0 := ∫ z, F z ∂γ with hX0
  set Tj : Fin N → ℝ := fun j =>
    ∫ ω, Qf μ F (hyb Y Z c (pref N j) (Finset.univ.erase j) ω) ∂P with hTj
  set D : ℝ := 4 * m3 * δ + N * ((m3 * C) * c ^ (2 + 1) * (m3 + m3γ) / ((2 + 1)! : ℝ)) + m3 * c * m1γ
    with hD
  have hsumT : |∑ j : Fin N, Tj j - N * I| ≤ N * D := by
    have : ∑ j : Fin N, Tj j - N * I = ∑ j : Fin N, (Tj j - I) := by
      rw [Finset.sum_sub_distrib]; simp
    rw [this]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j : Fin N, |Tj j - I| ≤ ∑ _j : Fin N, D := Finset.sum_le_sum fun j _ => hj j
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hc2 : c ^ 2 = 1 / (N : ℝ) := by
    have : (N : ℝ) ≠ 0 := by positivity
    field_simp; linarith
  have hq : (3 ! : ℝ)⁻¹ * c ^ 3 * (N * I) = (1 / 6) * c * I := by
    have : c ^ 3 * N = c := by
      have : c ^ 3 * N = c * (c ^ 2 * N) := by ring
      rw [this, hcN, mul_one]
    simp only [Nat.factorial]; push_cast
    linear_combination (1 / 6 * I) * this
  have h5 : |(3 ! : ℝ)⁻¹ * c ^ 3 * ∑ j : Fin N, Tj j - (1 / 6) * c * I| ≤
      (3 ! : ℝ)⁻¹ * c ^ 3 * (N * D) := by
    rw [← hq, ← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (3 ! : ℝ)⁻¹ * c ^ 3)]
    exact mul_le_mul_of_nonneg_left hsumT (by positivity)
  have h6 := abs_add_le (X1 - X0 - (3 ! : ℝ)⁻¹ * c ^ 3 * ∑ j : Fin N, Tj j)
    ((3 ! : ℝ)⁻¹ * c ^ 3 * ∑ j : Fin N, Tj j - (1 / 6) * c * I)
  have e : X1 - X0 - (1 / 6) * c * I = (X1 - X0 - (3 ! : ℝ)⁻¹ * c ^ 3 * ∑ j : Fin N, Tj j) +
      ((3 ! : ℝ)⁻¹ * c ^ 3 * ∑ j : Fin N, Tj j - (1 / 6) * c * I) := by ring
  rw [e]
  refine h6.trans ?_
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hc4 : c ^ 4 = (1 / (N:ℝ)) ^ 2 := by rw [← hc2]; ring
  have hc6 : c ^ 6 = (1 / (N:ℝ)) ^ 3 := by rw [← hc2]; ring
  have hc3N : c ^ 3 * N = c := by
    have : c ^ 3 * N = c * (c ^ 2 * N) := by ring
    rw [this, hcN, mul_one]
  have hnum : (N:ℝ) * (1 * c ^ (3 + 1) * (m4μ + m4γ) / ((3 + 1)! : ℝ)) +
      (3 ! : ℝ)⁻¹ * c ^ 3 * (N * D) =
      (m4μ + m4γ) / 24 / N + (2 / 3) * c * m3 * δ +
        (m3 * C * (m3 + m3γ) / 36 + m3 * m1γ / 6) / N := by
    have e1 : c ^ (3 + 1) = c ^ 4 := rfl
    have e2 : c ^ (2 + 1) = c ^ 3 := rfl
    have hlhs : (N:ℝ) * (1 * c ^ (3 + 1) * (m4μ + m4γ) / ((3 + 1)! : ℝ)) +
        (3 ! : ℝ)⁻¹ * c ^ 3 * (N * D) = (N * c ^ 4 * (m4μ + m4γ)) / 24 +
          (c ^ 3 * N) * (4 * m3 * δ) / 6 + (N ^ 2 * c ^ 6 * m3 * C * (m3 + m3γ)) / 36
          + (c ^ 3 * N) * (m3 * c * m1γ) / 6 := by
      simp only [hD, e1, e2, Nat.factorial]; push_cast; ring
    have hcc : c * (m3 * c * m1γ) = m3 * m1γ * (1 / (N:ℝ)) := by rw [← hc2]; ring
    rw [hlhs, hc3N, hc4, hc6, hcc]
    field_simp
    ring
  refine (add_le_add h4 h5).trans (le_of_eq ?_)
  rw [← hnum]

end Core4

section C4Core

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

set_option maxHeartbeats 1600000 in
lemma c4_core (e : HilbertBasis ℕ ℝ H) (nt : ℕ) {δ C : ℝ} (hδ : 0 < δ) (hC0 : 0 ≤ C)
    (hC : SmoothProp e nt δ C) {N : ℕ} (hN : 1 ≤ N) {X₀ : Ω → H} (hmeas₀ : AEMeasurable X₀ P)
    (hcent : ∫ ω, X₀ ω ∂P = 0) (h4 : Integrable (fun ω => ‖X₀ ω‖ ^ 4) P)
    {X : Fin N → Ω → H} (hind : iIndepFun X P) (hmeas : ∀ i, AEMeasurable (X i) P)
    (hlaw : ∀ i, P.map (X i) = P.map X₀) {G : Ω → H}
    (hG : IsCenteredGaussianRV P G (fun x y => ProbabilityTheory.covarianceBilin (law P X₀) x y))
    {F : H → ℝ} (hF : F ∈ CbUnitBall H 4)
    (hτ : ∫ ω, ‖X₀ ω - PP e nt (X₀ ω)‖ ^ 2 ∂P ≤ δ ^ 2) {Sb : ℝ}
    (ha2 : ∫ ω, ‖X₀ ω‖ ^ 2 ∂P ≤ Sb) (hm3S : ∫ ω, ‖X₀ ω‖ ^ 3 ∂P ≤ Sb) (hm4S : ∫ ω, ‖X₀ ω‖ ^ 4 ∂P ≤ Sb) :
    |∫ ω, F ((Real.sqrt N)⁻¹ • ∑ i, X i ω) ∂P - ∫ ω, F (G ω) ∂P -
        (1 / (6 * Real.sqrt N)) * thirdMomentPairing P F G X₀| ≤
      (Sb + 3 * Sb ^ 2) / 24 / N + (2 / 3) * (Real.sqrt N)⁻¹ * Sb * δ +
        (Sb * C * (Sb + (Sb + 3 * Sb ^ 2) / 2) / 36 + Sb * ((1 + Sb) / 2) / 6) / N := by
  obtain ⟨hF4, hFb⟩ := unit_ball_bound hF
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  set μ := P.map X₀ with hμ
  set γ := P.map G with hγ
  haveI := prob_map hmeas₀
  haveI := prob_map hG.1
  have M := matching_of_data hmeas₀ hcent h4 hG
  set c : ℝ := (Real.sqrt N)⁻¹ with hc
  have hsq : (0:ℝ) < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hcpos : 0 < c := inv_pos.2 hsq
  have hcN : c ^ 2 * N = 1 := by
    rw [hc, inv_pow, Real.sq_sqrt hNpos.le]; field_simp
  have S := setup_prod N μ γ
  -- the Gaussian endpoint
  have hlawZ : (prodMeasure N μ γ).map (hyb (coordY (H := H) N)
      (coordZ (H := H) N) c ∅ Finset.univ) = γ := by
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    rw [S.law_sumZ c]
    have := gaussian_stable hG.2.1 n
    simpa [hc] using this
  have hτ' : ∫ a, ‖a - PP e nt a‖ ^ 2 ∂μ ≤ δ ^ 2 := by
    have hcont : Continuous fun a : H => ‖a - PP e nt a‖ ^ 2 :=
      (continuous_norm.comp (continuous_id.sub (continuous_PP e nt))).pow 2
    rw [hμ, integral_map hmeas₀ hcont.aestronglyMeasurable]
    exact hτ
  have hcore := core4 e nt hδ hC0 hC S M hcpos (by omega) hcN hlawZ hF4 hFb hτ'
  -- transfer the main term to `P`
  have hX1 : ∫ ω, F (c • ∑ i, X i ω) ∂P =
      ∫ ω, F (hyb (coordY (H := H) N)
      (coordZ (H := H) N) c Finset.univ Finset.univ ω)
        ∂(prodMeasure N μ γ) := by
    have h1 := map_sum_eq_of_iid hmeas hind hlaw c
    have h2 := S.law_sumY c
    have hm : Measurable fun z : Fin N → H => c • ∑ i, z i := by fun_prop
    have e1 : ∫ ω, F (c • ∑ i, X i ω) ∂P = ∫ z, F z ∂(P.map fun ω => c • ∑ i, X i ω) := by
      rw [integral_map (aemeasurable_pi_iff.2 hmeas |> fun h => by
        exact (hm.comp_aemeasurable h)) hF4.continuous.aestronglyMeasurable]
    have e2 : ∫ ω, F (hyb (coordY (H := H) N)
      (coordZ (H := H) N) c Finset.univ Finset.univ ω)
        ∂(prodMeasure N μ γ) =
        ∫ z, F z ∂((prodMeasure N μ γ).map (hyb (coordY (H := H) N)
      (coordZ (H := H) N) c Finset.univ Finset.univ)) := by
      rw [integral_map (S.measurable_hyb' c _ _).aemeasurable hF4.continuous.aestronglyMeasurable]
    rw [e1, e2, h1, h2]
  have hEG : ∫ ω, F (G ω) ∂P = ∫ z, F z ∂γ := by
    rw [hγ, integral_map hG.1 hF4.continuous.aestronglyMeasurable]
  have h3 : Integrable (fun ω => ‖X₀ ω‖ ^ 3) P := integrable_norm_pow_le_four hmeas₀ h4 (by norm_num)
  have hF3 : ContDiff ℝ 3 F := hF4.of_le (by norm_num)
  have hpair := pairing_eq (P := P) hF3 (K := 1)
    (fun x => hFb 3 (by norm_num) x) hmeas₀ hG.1 h3
  -- moments
  have hmom : ∀ j : ℕ, ∫ a, ‖a‖ ^ j ∂μ = ∫ ω, ‖X₀ ω‖ ^ j ∂P := fun j => by
    rw [hμ, integral_map hmeas₀ (by fun_prop : Continuous fun a : H => ‖a‖ ^ j).aestronglyMeasurable]
  have hm2 : ∫ b, ‖b‖ ^ 2 ∂γ = ∫ ω, ‖X₀ ω‖ ^ 2 ∂P := by
    rw [hγ, second_moment_eq hmeas₀ hcent h4 hG, ← hmom 2]
  have hm4 : ∫ b, ‖b‖ ^ 4 ∂γ ≤ 3 * (∫ ω, ‖X₀ ω‖ ^ 2 ∂P) ^ 2 := by
    rw [← hm2]; exact gaussian_fourth_le hG.2.1
  have hm3 : ∫ b, ‖b‖ ^ 3 ∂γ ≤ ((∫ ω, ‖X₀ ω‖ ^ 2 ∂P) + 3 * (∫ ω, ‖X₀ ω‖ ^ 2 ∂P) ^ 2) / 2 := by
    have hle : ∫ b, ‖b‖ ^ 3 ∂γ ≤ ∫ b, ((‖b‖ ^ 2 + ‖b‖ ^ 4) / 2) ∂γ := by
      refine integral_mono (gaussian_integrable_pow hG.2.1 3)
        (((gaussian_integrable_pow hG.2.1 2).add (gaussian_integrable_pow hG.2.1 4)).div_const 2) ?_
      intro b
      simp only
      nlinarith [sq_nonneg (‖b‖ * (1 - ‖b‖)), norm_nonneg b]
    rw [integral_div, integral_add (gaussian_integrable_pow hG.2.1 2) (gaussian_integrable_pow hG.2.1 4), hm2] at hle
    linarith
  have hm1 : ∫ b, ‖b‖ ∂γ ≤ (1 + ∫ ω, ‖X₀ ω‖ ^ 2 ∂P) / 2 := by
    have hle : ∫ b, ‖b‖ ∂γ ≤ ∫ b, ((1 + ‖b‖ ^ 2) / 2) ∂γ := by
      refine integral_mono (by simpa using gaussian_integrable_pow hG.2.1 1)
        (((integrable_const (1:ℝ)).add (gaussian_integrable_pow hG.2.1 2)).div_const 2) ?_
      intro b
      simp only
      nlinarith [sq_nonneg (‖b‖ - 1)]
    rw [integral_div, integral_add (integrable_const _) (gaussian_integrable_pow hG.2.1 2), hm2] at hle
    simpa using hle
  -- moments
  have hmom : ∀ j : ℕ, ∫ a, ‖a‖ ^ j ∂μ = ∫ ω, ‖X₀ ω‖ ^ j ∂P := fun j => by
    rw [hμ, integral_map hmeas₀ (by fun_prop : Continuous fun a : H => ‖a‖ ^ j).aestronglyMeasurable]
  have hm2 : ∫ b, ‖b‖ ^ 2 ∂γ = ∫ ω, ‖X₀ ω‖ ^ 2 ∂P := by
    rw [hγ, second_moment_eq hmeas₀ hcent h4 hG, ← hmom 2]
  have hm4 : ∫ b, ‖b‖ ^ 4 ∂γ ≤ 3 * (∫ ω, ‖X₀ ω‖ ^ 2 ∂P) ^ 2 := by
    rw [← hm2]; exact gaussian_fourth_le hG.2.1
  have hm3 : ∫ b, ‖b‖ ^ 3 ∂γ ≤ ((∫ ω, ‖X₀ ω‖ ^ 2 ∂P) + 3 * (∫ ω, ‖X₀ ω‖ ^ 2 ∂P) ^ 2) / 2 := by
    have hle : ∫ b, ‖b‖ ^ 3 ∂γ ≤ ∫ b, ((‖b‖ ^ 2 + ‖b‖ ^ 4) / 2) ∂γ := by
      refine integral_mono (gaussian_integrable_pow hG.2.1 3)
        (((gaussian_integrable_pow hG.2.1 2).add (gaussian_integrable_pow hG.2.1 4)).div_const 2) ?_
      intro b
      simp only
      nlinarith [sq_nonneg (‖b‖ * (1 - ‖b‖)), norm_nonneg b]
    rw [integral_div, integral_add (gaussian_integrable_pow hG.2.1 2) (gaussian_integrable_pow hG.2.1 4), hm2] at hle
    linarith
  have hm1 : ∫ b, ‖b‖ ∂γ ≤ (1 + ∫ ω, ‖X₀ ω‖ ^ 2 ∂P) / 2 := by
    have hle : ∫ b, ‖b‖ ∂γ ≤ ∫ b, ((1 + ‖b‖ ^ 2) / 2) ∂γ := by
      refine integral_mono (by simpa using gaussian_integrable_pow hG.2.1 1)
        (((integrable_const (1:ℝ)).add (gaussian_integrable_pow hG.2.1 2)).div_const 2) ?_
      intro b
      simp only
      nlinarith [sq_nonneg (‖b‖ - 1)]
    rw [integral_div, integral_add (integrable_const _) (gaussian_integrable_pow hG.2.1 2), hm2] at hle
    simpa using hle
  have hm3nn : 0 ≤ ∫ a, ‖a‖ ^ 3 ∂μ := integral_nonneg fun a => by positivity
  have ha2nn : 0 ≤ ∫ ω, ‖X₀ ω‖ ^ 2 ∂P := integral_nonneg fun a => by positivity
  have hm3γnn : 0 ≤ ∫ b, ‖b‖ ^ 3 ∂γ := integral_nonneg fun a => by positivity
  have hm1nn : 0 ≤ ∫ b, ‖b‖ ∂γ := integral_nonneg fun a => by positivity
  have hcc : 1 / (6 * Real.sqrt N) = (1 / 6) * c := by rw [hc]; field_simp
  rw [hX1, hEG, hpair, hcc]
  refine hcore.trans ?_
  rw [hmom 4, hmom 3] at *
  have hsq2 : (∫ ω, ‖X₀ ω‖ ^ 2 ∂P) ^ 2 ≤ Sb ^ 2 := pow_le_pow_left₀ ha2nn ha2 2
  have hm3P : 0 ≤ ∫ ω, ‖X₀ ω‖ ^ 3 ∂P := integral_nonneg fun a => by positivity
  have hm4P : 0 ≤ ∫ ω, ‖X₀ ω‖ ^ 4 ∂P := integral_nonneg fun a => by positivity
  have hm4' : ∫ b, ‖b‖ ^ 4 ∂γ ≤ 3 * Sb ^ 2 := by linarith
  have hm3' : ∫ b, ‖b‖ ^ 3 ∂γ ≤ (Sb + 3 * Sb ^ 2) / 2 := by linarith
  have hm1' : ∫ b, ‖b‖ ∂γ ≤ (1 + Sb) / 2 := by linarith
  have hSb0 : 0 ≤ Sb := ha2nn.trans ha2
  have t1 : ((∫ ω, ‖X₀ ω‖ ^ 4 ∂P) + ∫ b, ‖b‖ ^ 4 ∂γ) / 24 / N ≤ (Sb + 3 * Sb ^ 2) / 24 / N := by
    gcongr
  have t2 : (∫ ω, ‖X₀ ω‖ ^ 3 ∂P) * C * ((∫ ω, ‖X₀ ω‖ ^ 3 ∂P) + ∫ b, ‖b‖ ^ 3 ∂γ) / 36 ≤
      Sb * C * (Sb + (Sb + 3 * Sb ^ 2) / 2) / 36 := by
    gcongr
  have t3 : (∫ ω, ‖X₀ ω‖ ^ 3 ∂P) * (∫ b, ‖b‖ ∂γ) / 6 ≤ Sb * ((1 + Sb) / 2) / 6 := by
    gcongr
  have t4 : (2 / 3) * c * (∫ ω, ‖X₀ ω‖ ^ 3 ∂P) * δ ≤ (2 / 3) * c * Sb * δ := by
    have : 0 ≤ c := hcpos.le
    gcongr
  have t5 := div_le_div_of_nonneg_right (add_le_add t2 t3) hNpos.le
  calc _ ≤ (Sb + 3 * Sb ^ 2) / 24 / N + (2 / 3) * c * Sb * δ +
        (Sb * C * (Sb + (Sb + 3 * Sb ^ 2) / 2) / 36 + Sb * ((1 + Sb) / 2) / 6) / N := by
          linarith
    _ = _ := by rw [hc]

end C4Core

section C4Main

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

lemma moment_le_of_fourth {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → H} (hX : AEMeasurable X P) (h4 : Integrable (fun ω => ‖X ω‖ ^ 4) P) {M₄ : ℝ}
    (hM : ∫ ω, ‖X ω‖ ^ 4 ∂P ≤ M₄) {j : ℕ} (hj : j ≤ 4) :
    ∫ ω, ‖X ω‖ ^ j ∂P ≤ 1 + max M₄ 0 := by
  have hj' := integrable_norm_pow_le_four hX h4 hj
  have hle : ∫ ω, ‖X ω‖ ^ j ∂P ≤ ∫ ω, (1 + ‖X ω‖ ^ 4) ∂P := by
    refine integral_mono hj' ((integrable_const (1:ℝ)).add h4) fun ω => ?_
    simp only
    have h0 : 0 ≤ ‖X ω‖ := norm_nonneg _
    by_cases h1 : ‖X ω‖ ≤ 1
    · have : ‖X ω‖ ^ j ≤ 1 := pow_le_one₀ h0 h1
      have : 0 ≤ ‖X ω‖ ^ 4 := by positivity
      linarith
    · push Not at h1
      have : ‖X ω‖ ^ j ≤ ‖X ω‖ ^ 4 := pow_le_pow_right₀ h1.le hj
      linarith
  rw [integral_add (integrable_const _) h4] at hle
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hle
  have := le_max_left M₄ 0
  linarith

theorem c4_main (e : HilbertBasis ℕ ℝ H) {ι : Type*}
    {Ω : ι → Type} [∀ a, MeasurableSpace (Ω a)] (P : ∀ a, Measure (Ω a))
    [∀ a, IsProbabilityMeasure (P a)] (X : ∀ a, Ω a → H) (hmeas : ∀ a, AEMeasurable (X a) (P a))
    (hcent : ∀ a, ∫ ω, X a ω ∂(P a) = 0) (M₄ : ℝ)
    (hint4 : ∀ a, Integrable (fun ω => ‖X a ω‖ ^ 4) (P a))
    (h4 : ∀ a, ∫ ω, ‖X a ω‖ ^ 4 ∂(P a) ≤ M₄)
    (htail : ∀ ε > 0, ∃ n₀ : ℕ, ∀ a, ∫ ω, ∑' n : {n : ℕ // n₀ ≤ n}, (inner ℝ (e n) (X a ω)) ^ 2 ∂(P a) ≤ ε)
    (G : ∀ a, Ω a → H)
    (hG : ∀ a, IsCenteredGaussianRV (P a) (G a) fun x y => ProbabilityTheory.covarianceBilin (law (P a) (X a)) x y) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a, ∀ (Xs : Fin N → Ω a → H), (∀ i, AEMeasurable (Xs i) (P a)) →
      IsIIDCopies (P a) Xs → (∀ i, law (P a) (Xs i) = law (P a) (X a)) →
      ∀ F : H → ℝ, F ∈ CbUnitBall H 4 →
        |∫ ω, F ((Real.sqrt N)⁻¹ • ∑ i, Xs i ω) ∂(P a) - ∫ ω, F (G a ω) ∂(P a) -
            (1 / (6 * Real.sqrt N)) * thirdMomentPairing (P a) F (G a) (X a)| ≤
          ε / Real.sqrt N := by
  intro ε hε
  set Sb : ℝ := 1 + max M₄ 0 with hSb
  have hSb1 : 1 ≤ Sb := by have := le_max_right M₄ 0; linarith
  have hSbpos : 0 < Sb := by linarith
  set δ : ℝ := 3 * ε / (4 * Sb) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨n₀, hn₀⟩ := htail (δ ^ 2) (by positivity)
  obtain ⟨C, hC0, hC⟩ := trunc_smooth e n₀ hδ
  set K : ℝ := (Sb + 3 * Sb ^ 2) / 24 +
    (Sb * C * (Sb + (Sb + 3 * Sb ^ 2) / 2) / 36 + Sb * ((1 + Sb) / 2) / 6) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨⌈(2 * K / ε) ^ 2⌉₊ + 1, ?_⟩
  intro N hN a Xs hmeasX hiid hlaw F hF
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN1
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hsqN : 2 * K / ε ≤ Real.sqrt N := by
    have h1 : (2 * K / ε) ^ 2 ≤ N := by
      have := Nat.le_ceil ((2 * K / ε) ^ 2)
      have h2 : ((⌈(2 * K / ε) ^ 2⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : ⌈(2 * K / ε) ^ 2⌉₊ ≤ N)
      linarith
    calc 2 * K / ε = Real.sqrt ((2 * K / ε) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt N := Real.sqrt_le_sqrt h1
  have hτ : ∫ ω, ‖X a ω - PP e n₀ (X a ω)‖ ^ 2 ∂(P a) ≤ δ ^ 2 := by
    have := hn₀ a
    simpa [norm_sub_PP_sq] using this
  have hcore := c4_core e n₀ hδ hC0 hC hN1 (hmeas a) (hcent a) (hint4 a) hiid.1 hmeasX
    (fun i => hlaw i) (hG a) hF hτ (Sb := Sb)
    (moment_le_of_fourth (hmeas a) (hint4 a) (h4 a) (by norm_num))
    (moment_le_of_fourth (hmeas a) (hint4 a) (h4 a) (by norm_num))
    (moment_le_of_fourth (hmeas a) (hint4 a) (h4 a) le_rfl)
  refine hcore.trans ?_
  have e1 : (2 / 3) * (Real.sqrt N)⁻¹ * Sb * δ = ε / 2 / Real.sqrt N := by
    rw [hδdef]; field_simp; ring
  have e2 : ((Sb + 3 * Sb ^ 2) / 24 / N + (Sb * C * (Sb + (Sb + 3 * Sb ^ 2) / 2) / 36 + Sb * ((1 + Sb) / 2) / 6) / N) =
      K / N := by rw [hK]; ring
  have e3 : K / N ≤ ε / 2 / Real.sqrt N := by
    have this : 2 * K ≤ ε * Real.sqrt N := by
      have := (div_le_iff₀ hε).1 hsqN
      nlinarith
    have hK2 : K / Real.sqrt N ≤ ε / 2 := by
      rw [div_le_iff₀ hsq]; linarith
    calc K / N = (K / Real.sqrt N) / Real.sqrt N := by
          rw [div_div, Real.mul_self_sqrt hNpos.le]
      _ ≤ ε / 2 / Real.sqrt N := div_le_div_of_nonneg_right hK2 hsq.le
  calc _ = ((Sb + 3 * Sb ^ 2) / 24 / N + (Sb * C * (Sb + (Sb + 3 * Sb ^ 2) / 2) / 36 + Sb * ((1 + Sb) / 2) / 6) / N)
        + (2 / 3) * (Real.sqrt N)⁻¹ * Sb * δ := by ring
    _ ≤ ε / 2 / Real.sqrt N + ε / 2 / Real.sqrt N := by rw [e2, e1]; linarith
    _ = ε / Real.sqrt N := by ring

end C4Main

end

end EdgeAux

end HRS
