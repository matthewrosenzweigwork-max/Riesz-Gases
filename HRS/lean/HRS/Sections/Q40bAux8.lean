import HRS.Sections.Sec5
import HRS.Stochastic.DualityProof
import HRS.Stochastic.QuadraticVariation
import HRS.Sections.Q40bAux1
import HRS.Sections.Q40bAux2
import HRS.Sections.Q40bAux3
import HRS.Sections.Q40bAux4
import HRS.Sections.Q40bAux5
import HRS.Sections.Q40bAux6
import HRS.Sections.Q40bAux7

/-!
# Packet Q40b, part 8: the martingale bracket and its error

For the vector `(√N M_N(t_a, φ_a))_a` of empirical martingales (`qPhi`), the covariation density is
`Σ_N(σ)_{ab} = 2β⁻¹ μ_N^σ(∇U^{σ,t_a}φ_a · ∇U^{σ,t_b}φ_b) 1_{σ ≤ t_a ∧ t_b}` (`q40b_sigma_formula`), to be compared
with `Σ̄(σ)_{ab} = 2β⁻¹ μ^σ(...)` (`qsb`, `q40b_integratedCov`: its integral is `noiseCovMatrix`).
`q40b_cov_bound`: `E ∫_0^T ‖Σ_N - Σ̄‖_{S₁} ≤ C √(2(H + log 2)/N)`, with `C` independent of `T` and `N`
(Hoeffding + Donsker–Varadhan, `q40b_dv_sqrt`, and the exponential gradient decay of the adjoint).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section
namespace HRS.Q40b

variable {d N : ℕ}

section Bracket

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {p : ℕ}

/-- The scaled noise integrands `√N · Ψ_a` of the `p` tests. -/
def qPhi (D : DynData d) (t : Fin p → ℝ) (F : Fin p → ℝ → Torus d → ℝ) (X : ℝ≥0 → Ω → Config d N) :
    Fin p → ℝ → Ω → (Fin N × Fin d) → ℝ :=
  fun a s ω => Real.sqrt N • empiricalNoiseIntegrand D (t a) (F a) X s ω

theorem q40b_sigma_formula (hN : 0 < N) (D : DynData d) (t : Fin p → ℝ)
    (F : Fin p → ℝ → Torus d → ℝ) (X : ℝ≥0 → Ω → Config d N) (σ : ℝ) (ω : Ω) (a b : Fin p) :
    covMatrixProcess (qPhi D t F X) σ ω a b =
      if σ ∈ Set.Icc 0 (min (t a) (t b)) then
        2 * D.invβ * ((1 / (N : ℝ)) * ∑ i, inner ℝ (Torus.grad (F a σ) (X σ.toNNReal ω i))
          (Torus.grad (F b σ) (X σ.toNNReal ω i))) else 0 := by
  unfold covMatrixProcess qPhi empiricalNoiseIntegrand
  have hmin : σ ∈ Set.Icc 0 (min (t a) (t b)) ↔ σ ∈ Set.Icc 0 (t a) ∧ σ ∈ Set.Icc 0 (t b) := by
    simp only [Set.mem_Icc, le_min_iff]; tauto
  by_cases hσ : σ ∈ Set.Icc 0 (min (t a) (t b))
  · obtain ⟨ha, hb⟩ := hmin.1 hσ
    simp only [hσ, ha, hb, if_true, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
    rw [Fintype.sum_prod_type]
    have hNn : (N : ℝ) ≠ 0 := by positivity
    have hc : ∀ (i : Fin N) (j : Fin d),
        Real.sqrt N * (Real.sqrt (2 * D.invβ) / N * (Torus.grad (F a σ) (X σ.toNNReal ω i)) j) *
          (Real.sqrt N * (Real.sqrt (2 * D.invβ) / N * (Torus.grad (F b σ) (X σ.toNNReal ω i)) j)) =
        2 * D.invβ * (1 / (N : ℝ)) * ((Torus.grad (F a σ) (X σ.toNNReal ω i)) j *
          (Torus.grad (F b σ) (X σ.toNNReal ω i)) j) := by
      intro i j
      have h1 : Real.sqrt N ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
      have h2 : Real.sqrt (2 * D.invβ) ^ 2 = 2 * D.invβ := Real.sq_sqrt (by linarith [D.hβ])
      calc _ = (Real.sqrt N ^ 2) * (Real.sqrt (2 * D.invβ) ^ 2) / (N : ℝ) ^ 2 *
            ((Torus.grad (F a σ) (X σ.toNNReal ω i)) j * (Torus.grad (F b σ) (X σ.toNNReal ω i)) j) := by
            field_simp
        _ = _ := by rw [h1, h2]; field_simp
    simp_rw [hc]
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    rw [mul_assoc, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · simp only [hσ, if_false]
    rcases hmin.not.1 hσ |> not_and_or.1 with h | h
    · simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul, if_neg h, mul_zero, zero_mul,
        Finset.sum_const_zero, smul_zero]
    · simp only [Matrix.of_apply, Pi.smul_apply, smul_eq_mul, if_neg h, mul_zero, zero_mul,
        Finset.sum_const_zero, smul_zero]


/-- The deterministic covariance density `Σ̄_σ = 2β⁻¹ μ^σ(∇U^{σ,t_a}φ_a · ∇U^{σ,t_b}φ_b)` on `[0, t_a ∧ t_b]`. -/
def qsb (D : DynData d) (ρ : ℝ → Torus d → ℝ) (t : Fin p → ℝ) (F : Fin p → ℝ → Torus d → ℝ) :
    ℝ → Matrix (Fin p) (Fin p) ℝ := fun σ =>
  Matrix.of fun a b => if σ ∈ Set.Icc 0 (min (t a) (t b)) then
    2 * D.invβ * ∫ x, inner ℝ (Torus.grad (F a σ) x) (Torus.grad (F b σ) x) * ρ σ x else 0

theorem q40b_qsb_meas (D : DynData d) {ρ : ℝ → Torus d → ℝ} {t : Fin p → ℝ}
    {F ft : Fin p → ℝ → Torus d → ℝ} (ht : ∀ a, 0 ≤ t a) (hF : ∀ a, IsC12Test (t a) (F a) (ft a))
    (hρJ : ∀ T, ContinuousOn (fun q : ℝ × Torus d => ρ q.1 q.2) (Set.Icc 0 T ×ˢ Set.univ)) :
    Measurable (qsb D ρ t F) := by
  refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => ?_
  have hm : (0 : ℝ) ≤ min (t a) (t b) := le_min (ht a) (ht b)
  have hGa := measurable_grad_clamp (ht a) (hF a)
  have hGb := measurable_grad_clamp (ht b) (hF b)
  have hρc := q40b_rho_clamp_meas hm (hρJ (min (t a) (t b)))
  have hint : StronglyMeasurable (fun q : ℝ × Torus d =>
      inner ℝ (Torus.grad (F a (clampTI (t a) q.1)) q.2) (Torus.grad (F b (clampTI (t b) q.1)) q.2) *
        ρ (clampTI (min (t a) (t b)) q.1) q.2) := by
    refine Measurable.stronglyMeasurable ?_
    exact (hGa.inner hGb).mul hρc
  have hI := (hint.integral_prod_right' (ν := volume)).measurable
  have heq : (fun σ : ℝ => qsb D ρ t F σ a b) =
      fun σ => if σ ∈ Set.Icc 0 (min (t a) (t b)) then 2 * D.invβ * ∫ x,
        inner ℝ (Torus.grad (F a (clampTI (t a) σ)) x) (Torus.grad (F b (clampTI (t b) σ)) x) *
          ρ (clampTI (min (t a) (t b)) σ) x else 0 := by
    funext σ
    unfold qsb
    rw [Matrix.of_apply]
    by_cases hσ : σ ∈ Set.Icc 0 (min (t a) (t b))
    · have h1 : σ ∈ Set.Icc 0 (t a) := ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩
      have h2 : σ ∈ Set.Icc 0 (t b) := ⟨hσ.1, hσ.2.trans (min_le_right _ _)⟩
      rw [if_pos hσ, if_pos hσ, clampTI_of_mem h1, clampTI_of_mem h2, clampTI_of_mem hσ]
    · rw [if_neg hσ, if_neg hσ]
  rw [heq]
  exact Measurable.ite measurableSet_Icc (measurable_const.mul hI) measurable_const


theorem q40b_gram_psd (u : Fin p → Torus d → Euc d) (hu : ∀ a, Continuous (u a)) {ρ : Torus d → ℝ}
    (hρ : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (c : ℝ) (hc : 0 ≤ c) (w : Fin p → ℝ) :
    (Matrix.of fun a b => c * (w a * w b * ∫ x, inner ℝ (u a x) (u b x) * ρ x)).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun ξ => ?_⟩
  · ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    have : ∫ x, inner ℝ (u b x) (u a x) * ρ x = ∫ x, inner ℝ (u a x) (u b x) * ρ x := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [real_inner_comm]
    rw [this]; ring
  · have hg := PDE.MFLinear.gram_pointwise (fun a x => (ξ a * w a) • u a x) ρ
      (fun a => (hu a).const_smul (ξ a * w a)) hρ hρ0
    have hexp : ∀ a b, ∫ x, inner ℝ ((ξ a * w a) • u a x) ((ξ b * w b) • u b x) * ρ x =
        (ξ a * w a) * (ξ b * w b) * ∫ x, inner ℝ (u a x) (u b x) * ρ x := by
      intro a b
      have : ∀ x, inner ℝ ((ξ a * w a) • u a x) ((ξ b * w b) • u b x) * ρ x =
          ((ξ a * w a) * (ξ b * w b)) * (inner ℝ (u a x) (u b x) * ρ x) := by
        intro x; rw [real_inner_smul_left, real_inner_smul_right]; ring
      simp_rw [this]
      rw [integral_const_mul]
    simp_rw [hexp] at hg
    have : dotProduct (star ξ) (Matrix.mulVec (Matrix.of fun a b =>
        c * (w a * w b * ∫ x, inner ℝ (u a x) (u b x) * ρ x)) ξ) =
        c * ∑ a, ∑ b, (ξ a * w a) * (ξ b * w b) * ∫ x, inner ℝ (u a x) (u b x) * ρ x := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, star_trivial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    rw [this]
    exact mul_nonneg hc hg


/-- The analytic data used for the bracket estimate. -/
structure Br (D : DynData d) (ρ : ℝ → Torus d → ℝ) (t : Fin p → ℝ) (F ft : Fin p → ℝ → Torus d → ℝ)
    (Ca : Fin p → ℝ) (m : ℝ) : Prop where
  t0 : ∀ a, 0 ≤ t a
  hF : ∀ a, IsC12Test (t a) (F a) (ft a)
  hC0 : ∀ a, 0 ≤ Ca a
  hm : 0 < m
  grad : ∀ a, ∀ σ ∈ Set.Icc 0 (t a), ∀ x, ‖Torus.grad (F a σ) x‖ ≤ Ca a * Real.exp (-m * (t a - σ))
  rhoJ : ∀ T, ContinuousOn (fun q : ℝ × Torus d => ρ q.1 q.2) (Set.Icc 0 T ×ˢ Set.univ)
  rhoP : ∀ σ, 0 ≤ σ → IsProbDensity (ρ σ)
  rhoC : ∀ σ, 0 ≤ σ → Continuous (ρ σ)

theorem q40b_qsb_psd {D : DynData d} {ρ : ℝ → Torus d → ℝ} {t : Fin p → ℝ}
    {F ft : Fin p → ℝ → Torus d → ℝ} {Ca : Fin p → ℝ} {m : ℝ} (h : Br D ρ t F ft Ca m)
    {σ : ℝ} (hσ : 0 ≤ σ) : (qsb D ρ t F σ).PosSemidef := by
  set w : Fin p → ℝ := fun a => if σ ≤ t a then 1 else 0 with hw
  set u : Fin p → Torus d → Euc d := fun a => Torus.grad (F a (clampTI (t a) σ)) with hu
  have hpsd := q40b_gram_psd u (fun a => Duality.grad_continuous ((h.hF a).c2 _ (clampTI_mem (h.t0 a) σ)))
    (h.rhoC σ hσ) (h.rhoP σ hσ).nonneg (2 * D.invβ) (by linarith [D.hβ]) w
  convert hpsd using 1
  ext a b
  unfold qsb
  simp only [Matrix.of_apply]
  by_cases hab : σ ∈ Set.Icc 0 (min (t a) (t b))
  · have h1 : σ ≤ t a := hab.2.trans (min_le_left _ _)
    have h2 : σ ≤ t b := hab.2.trans (min_le_right _ _)
    rw [if_pos hab]
    simp only [hw, hu, if_pos h1, if_pos h2, one_mul, clampTI_of_mem (⟨hσ, h1⟩ : σ ∈ Set.Icc 0 (t a)),
      clampTI_of_mem (⟨hσ, h2⟩ : σ ∈ Set.Icc 0 (t b))]
  · rw [if_neg hab]
    have : ¬ (σ ≤ t a ∧ σ ≤ t b) := fun ⟨h1, h2⟩ => hab ⟨hσ, le_min h1 h2⟩
    rw [not_and_or] at this
    rcases this with h1 | h1
    · simp [hw, h1]
    · simp [hw, h1]


theorem q40b_qsb_entry_bound {D : DynData d} {ρ : ℝ → Torus d → ℝ} {t : Fin p → ℝ}
    {F ft : Fin p → ℝ → Torus d → ℝ} {Ca : Fin p → ℝ} {m : ℝ} (h : Br D ρ t F ft Ca m)
    (σ : ℝ) (a b : Fin p) :
    |qsb D ρ t F σ a b| ≤ 2 * D.invβ * Ca a * Ca b * (Real.exp (-m * (t a - σ)) *
      Real.exp (-m * (t b - σ))) ∧ |qsb D ρ t F σ a b| ≤ 2 * D.invβ * Ca a * Ca b := by
  have hq : 0 ≤ 2 * D.invβ := by linarith [D.hβ]
  have hCa := h.hC0 a
  have hCb := h.hC0 b
  by_cases hσ : σ ∈ Set.Icc 0 (min (t a) (t b))
  · have h1 : σ ∈ Set.Icc 0 (t a) := ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩
    have h2 : σ ∈ Set.Icc 0 (t b) := ⟨hσ.1, hσ.2.trans (min_le_right _ _)⟩
    have hρ := h.rhoP σ hσ.1
    have hρint : Integrable (ρ σ) := by
      by_contra hni
      have := hρ.integral_one
      rw [integral_undef hni] at this; norm_num at this
    have hbd : |∫ x, inner ℝ (Torus.grad (F a σ) x) (Torus.grad (F b σ) x) * ρ σ x| ≤
        (Ca a * Real.exp (-m * (t a - σ))) * (Ca b * Real.exp (-m * (t b - σ))) := by
      rw [← Real.norm_eq_abs]
      have := norm_integral_le_of_norm_le (μ := volume)
        (f := fun x => inner ℝ (Torus.grad (F a σ) x) (Torus.grad (F b σ) x) * ρ σ x)
        (g := fun x => ((Ca a * Real.exp (-m * (t a - σ))) * (Ca b * Real.exp (-m * (t b - σ)))) * ρ σ x)
        (hρint.const_mul _) (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ.nonneg x)]
          refine mul_le_mul_of_nonneg_right ?_ (hρ.nonneg x)
          refine (abs_real_inner_le_norm _ _).trans ?_
          exact mul_le_mul (h.grad a σ h1 x) (h.grad b σ h2 x) (norm_nonneg _)
            (mul_nonneg hCa (Real.exp_pos _).le))
      rw [integral_const_mul, hρ.integral_one, mul_one] at this
      exact this
    unfold qsb
    rw [Matrix.of_apply, if_pos hσ, abs_mul, abs_of_nonneg hq]
    have hex1 : Real.exp (-m * (t a - σ)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [h.hm, h1.2])
    have hex2 : Real.exp (-m * (t b - σ)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [h.hm, h2.2])
    have he1 := (Real.exp_pos (-m * (t a - σ)))
    have he2 := (Real.exp_pos (-m * (t b - σ)))
    refine ⟨?_, ?_⟩
    · calc 2 * D.invβ * |∫ x, inner ℝ (Torus.grad (F a σ) x) (Torus.grad (F b σ) x) * ρ σ x|
          ≤ 2 * D.invβ * ((Ca a * Real.exp (-m * (t a - σ))) * (Ca b * Real.exp (-m * (t b - σ)))) :=
            mul_le_mul_of_nonneg_left hbd hq
        _ = _ := by ring
    · calc 2 * D.invβ * |∫ x, inner ℝ (Torus.grad (F a σ) x) (Torus.grad (F b σ) x) * ρ σ x|
          ≤ 2 * D.invβ * ((Ca a * Real.exp (-m * (t a - σ))) * (Ca b * Real.exp (-m * (t b - σ)))) :=
            mul_le_mul_of_nonneg_left hbd hq
        _ ≤ 2 * D.invβ * ((Ca a * 1) * (Ca b * 1)) := by gcongr
        _ = _ := by ring
  · unfold qsb
    rw [Matrix.of_apply, if_neg hσ, abs_zero]
    refine ⟨by positivity, by positivity⟩


theorem q40b_isDet {D : DynData d} {ρ : ℝ → Torus d → ℝ} {t : Fin p → ℝ}
    {F ft : Fin p → ℝ → Torus d → ℝ} {Ca : Fin p → ℝ} {m : ℝ} (h : Br D ρ t F ft Ca m)
    (T : ℝ) : IsDetCovMatrix T (qsb D ρ t F) where
  meas := q40b_qsb_meas D h.t0 h.hF h.rhoJ
  psd := fun σ hσ => q40b_qsb_psd h hσ.1
  int := by
    have hmeas : Measurable (fun σ => s1Norm (qsb D ρ t F σ)) := by
      refine measurable_traceNormMatrix _ fun i j => ?_
      exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (q40b_qsb_meas D h.t0 h.hF h.rhoJ))
    refine Measure.integrableOn_of_bounded (M := ∑ a, ∑ b, 2 * D.invβ * Ca a * Ca b)
      measure_Icc_lt_top.ne hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun σ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (traceNormMatrix_nonneg _)]
    refine (PDE.MFLinear.traceNormMatrix_le_sum _).trans ?_
    exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => (q40b_qsb_entry_bound h σ a b).2


theorem q40b_integratedCov (D : DynData d) (ρ : ℝ → Torus d → ℝ) (t : Fin p → ℝ)
    (F : Fin p → ℝ → Torus d → ℝ) {T : ℝ} (hT : ∀ a, t a ≤ T) {φ : Fin p → Torus d → ℝ}
    (hFp : ∀ a, ∀ r ∈ Set.Icc 0 (t a), propagator D ρ r (t a) (φ a) = F a r) :
    integratedCov T (qsb D ρ t F) = noiseCovMatrix D ρ D.invβ t φ := by
  ext a b
  unfold integratedCov noiseCovMatrix qsb
  simp only [Matrix.of_apply]
  have hsub : Set.Icc (0 : ℝ) (min (t a) (t b)) ⊆ Set.Icc 0 T := fun σ hσ =>
    ⟨hσ.1, hσ.2.trans ((min_le_left _ _).trans (hT a))⟩
  have h1 : ∫ σ in Set.Icc (0 : ℝ) T, (if σ ∈ Set.Icc 0 (min (t a) (t b)) then
      2 * D.invβ * ∫ x, inner ℝ (Torus.grad (F a σ) x) (Torus.grad (F b σ) x) * ρ σ x else 0) =
      ∫ σ in Set.Icc (0 : ℝ) (min (t a) (t b)), 2 * D.invβ * ∫ x,
        inner ℝ (Torus.grad (F a σ) x) (Torus.grad (F b σ) x) * ρ σ x := by
    have := setIntegral_indicator (μ := volume) (s := Set.Icc (0 : ℝ) T)
      (t := Set.Icc (0 : ℝ) (min (t a) (t b))) measurableSet_Icc
      (f := fun σ => 2 * D.invβ * ∫ x, inner ℝ (Torus.grad (F a σ) x) (Torus.grad (F b σ) x) * ρ σ x)
    rw [Set.inter_eq_right.2 hsub] at this
    simpa [Set.indicator] using this
  rw [h1, integral_const_mul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
  have e1 : propagator D ρ σ (t a) (φ a) = F a σ :=
    hFp a σ ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩
  have e2 : propagator D ρ σ (t b) (φ b) = F b σ :=
    hFp b σ ⟨hσ.1, hσ.2.trans (min_le_right _ _)⟩
  simp only [e1, e2]


theorem q40b_Sg_bound {D : DynData d} {ρ : ℝ → Torus d → ℝ} {t : Fin p → ℝ}
    {F ft : Fin p → ℝ → Torus d → ℝ} {Ca : Fin p → ℝ} {m : ℝ} (h : Br D ρ t F ft Ca m)
    (hN : 0 < N) (X : ℝ≥0 → Ω → Config d N) (σ : ℝ) (ω : Ω) (a b : Fin p) :
    |covMatrixProcess (qPhi D t F X) σ ω a b| ≤ 2 * D.invβ * Ca a * Ca b := by
  have hq : 0 ≤ 2 * D.invβ := by linarith [D.hβ]
  have hCa := h.hC0 a
  have hCb := h.hC0 b
  rw [q40b_sigma_formula hN]
  by_cases hσ : σ ∈ Set.Icc 0 (min (t a) (t b))
  · have h1 : σ ∈ Set.Icc 0 (t a) := ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩
    have h2 : σ ∈ Set.Icc 0 (t b) := ⟨hσ.1, hσ.2.trans (min_le_right _ _)⟩
    rw [if_pos hσ, abs_mul, abs_of_nonneg hq, abs_mul]
    have hNn : (0 : ℝ) < N := by exact_mod_cast hN
    rw [abs_of_pos (by positivity : (0 : ℝ) < 1 / N)]
    have hex1 : Real.exp (-m * (t a - σ)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [h.hm, h1.2])
    have hex2 : Real.exp (-m * (t b - σ)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [h.hm, h2.2])
    have hterm : ∀ i : Fin N, |inner ℝ (Torus.grad (F a σ) (X σ.toNNReal ω i))
        (Torus.grad (F b σ) (X σ.toNNReal ω i))| ≤ Ca a * Ca b := by
      intro i
      refine (abs_real_inner_le_norm _ _).trans ?_
      have g1 := h.grad a σ h1 (X σ.toNNReal ω i)
      have g2 := h.grad b σ h2 (X σ.toNNReal ω i)
      have e1 : Ca a * Real.exp (-m * (t a - σ)) ≤ Ca a := by nlinarith
      have e2 : Ca b * Real.exp (-m * (t b - σ)) ≤ Ca b := by nlinarith
      exact mul_le_mul (g1.trans e1) (g2.trans e2) (norm_nonneg _) hCa
    have hsum : |∑ i, inner ℝ (Torus.grad (F a σ) (X σ.toNNReal ω i))
        (Torus.grad (F b σ) (X σ.toNNReal ω i))| ≤ N * (Ca a * Ca b) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc _ ≤ ∑ _i : Fin N, Ca a * Ca b := Finset.sum_le_sum fun i _ => hterm i
        _ = _ := by simp
    calc 2 * D.invβ * (1 / (N : ℝ) * |∑ i, inner ℝ (Torus.grad (F a σ) (X σ.toNNReal ω i))
          (Torus.grad (F b σ) (X σ.toNNReal ω i))|)
        ≤ 2 * D.invβ * (1 / (N : ℝ) * (N * (Ca a * Ca b))) := by gcongr
      _ = 2 * D.invβ * Ca a * Ca b := by field_simp
  · rw [if_neg hσ, abs_zero]; positivity


theorem q40b_Q_L1 {D : DynData d} {ρ : ℝ → Torus d → ℝ} {t : Fin p → ℝ}
    {F ft : Fin p → ℝ → Torus d → ℝ} {Ca : Fin p → ℝ} {m : ℝ} (h : Br D ρ t F ft Ca m)
    (hN : 0 < N) {a b : Fin p} {P : Measure Ω} [IsProbabilityMeasure P] {X : ℝ≥0 → Ω → Config d N}
    (hXm : ∀ r : ℝ≥0, Measurable (X r)) {H : ℝ} (hH0 : 0 ≤ H)
    (hent : ∀ σ, 0 ≤ σ → relEntropy (P.map (X σ.toNNReal))
      (Measure.pi fun _ : Fin N => withDensityReal (ρ σ)) ≤ ENNReal.ofReal H)
    {σ : ℝ} (hσ : σ ∈ Set.Icc 0 (min (t a) (t b))) :
    ∫ ω, |covMatrixProcess (qPhi D t F X) σ ω a b - qsb D ρ t F σ a b| ∂P ≤
      2 * D.invβ * ((Ca a * Real.exp (-m * (t a - σ))) * (Ca b * Real.exp (-m * (t b - σ)))) *
        Real.sqrt (2 * (H + Real.log 2) / N) := by
  have hq : 0 ≤ 2 * D.invβ := by linarith [D.hβ]
  have h1 : σ ∈ Set.Icc 0 (t a) := ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩
  have h2 : σ ∈ Set.Icc 0 (t b) := ⟨hσ.1, hσ.2.trans (min_le_right _ _)⟩
  have hρ := h.rhoP σ hσ.1
  haveI : IsProbabilityMeasure (withDensityReal (ρ σ)) := isProb_withDensityReal hρ
  set ν := withDensityReal (ρ σ) with hν
  set g : Torus d → ℝ := fun x => inner ℝ (Torus.grad (F a σ) x) (Torus.grad (F b σ) x) with hgdef
  have hgc : Continuous g := (Duality.grad_continuous ((h.hF a).c2 σ h1)).inner
    (Duality.grad_continuous ((h.hF b).c2 σ h2))
  set B : ℝ := (Ca a * Real.exp (-m * (t a - σ))) * (Ca b * Real.exp (-m * (t b - σ))) with hB
  have hgB : ∀ x, |g x| ≤ B := fun x => by
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul (h.grad a σ h1 x) (h.grad b σ h2 x) (norm_nonneg _)
      (mul_nonneg (h.hC0 a) (Real.exp_pos _).le)
  have hpt : ∀ ω, covMatrixProcess (qPhi D t F X) σ ω a b - qsb D ρ t F σ a b =
      2 * D.invβ * q40bY ν g (X σ.toNNReal ω) := by
    intro ω
    rw [q40b_sigma_formula hN, if_pos hσ]
    unfold qsb q40bY
    rw [Matrix.of_apply, if_pos hσ]
    have hint : ∫ y, g y ∂ν = ∫ x, inner ℝ (Torus.grad (F a σ) x) (Torus.grad (F b σ) x) * ρ σ x := by
      rw [hν, PDE.MFPairing.integral_withDensityReal hρ.measurable hρ.nonneg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hgdef]; ring
    rw [hint]
    ring
  have hmeas : Measurable (fun x : Config d N => |q40bY ν g x|) :=
    (q40b_measurable_Y ν hgc.measurable).abs
  have hKL : InformationTheory.klDiv (P.map (X σ.toNNReal))
      (Measure.pi fun _ : Fin N => ν) ≤ ENNReal.ofReal H := hent σ hσ.1
  have hdv := q40b_dv_sqrt ν (P.map (X σ.toNNReal)) hgc.measurable hgB hN hH0 hKL
  have hcv : ∫ ω, |q40bY ν g (X σ.toNNReal ω)| ∂P = ∫ x, |q40bY ν g x| ∂(P.map (X σ.toNNReal)) :=
    (integral_map (hXm _).aemeasurable hmeas.aestronglyMeasurable).symm
  have hpt2 : ∀ ω, |covMatrixProcess (qPhi D t F X) σ ω a b - qsb D ρ t F σ a b| =
      2 * D.invβ * |q40bY ν g (X σ.toNNReal ω)| := fun ω => by
    rw [hpt ω, abs_mul, abs_of_nonneg hq]
  simp_rw [hpt2]
  rw [integral_const_mul, hcv]
  have := mul_le_mul_of_nonneg_left hdv hq
  calc 2 * D.invβ * ∫ x, |q40bY ν g x| ∂(P.map (X σ.toNNReal))
      ≤ 2 * D.invβ * (B * Real.sqrt (2 * (H + Real.log 2) / N)) := this
    _ = _ := by rw [hB]; ring


theorem q40b_exp_int {m : ℝ} (hm : 0 < m) {mn ta tb : ℝ} (hmn : 0 ≤ mn) (h1 : mn ≤ ta) (h2 : mn ≤ tb) :
    ∫ σ in Set.Icc (0 : ℝ) mn, Real.exp (-m * (ta - σ)) * Real.exp (-m * (tb - σ)) ≤ 1 / (2 * m) := by
  have hle : ∀ σ ∈ Set.Icc (0 : ℝ) mn, Real.exp (-m * (ta - σ)) * Real.exp (-m * (tb - σ)) ≤
      Real.exp (-(2 * m) * (mn - σ)) := by
    intro σ hσ
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith [hσ.1, hσ.2]
  have hcont : Continuous fun σ : ℝ => Real.exp (-(2 * m) * (mn - σ)) := by fun_prop
  calc ∫ σ in Set.Icc (0 : ℝ) mn, Real.exp (-m * (ta - σ)) * Real.exp (-m * (tb - σ))
      ≤ ∫ σ in Set.Icc (0 : ℝ) mn, Real.exp (-(2 * m) * (mn - σ)) := by
        refine setIntegral_mono_on ?_ hcont.integrableOn_Icc measurableSet_Icc hle
        exact (by fun_prop : Continuous fun σ : ℝ => Real.exp (-m * (ta - σ)) *
          Real.exp (-m * (tb - σ))).integrableOn_Icc
    _ = ∫ σ in (0 : ℝ)..mn, Real.exp (-(2 * m) * (mn - σ)) := by
        rw [intervalIntegral.integral_of_le hmn, integral_Icc_eq_integral_Ioc]
    _ = (1 - Real.exp (-(2 * m) * mn)) / (2 * m) := by
        have hd : ∀ σ ∈ Set.uIcc (0 : ℝ) mn, HasDerivAt (fun σ : ℝ =>
            Real.exp (-(2 * m) * (mn - σ)) / (2 * m)) (Real.exp (-(2 * m) * (mn - σ))) σ := by
          intro σ _
          have h1 : HasDerivAt (fun σ : ℝ => -(2 * m) * (mn - σ)) (2 * m) σ := by
            have := ((hasDerivAt_id σ).const_sub mn).const_mul (-(2 * m))
            simpa using this
          have := (h1.exp).div_const (2 * m)
          convert this using 1
          field_simp
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _)]
        simp
        ring
    _ ≤ 1 / (2 * m) := by
        have := Real.exp_pos (-(2 * m) * mn)
        rw [div_le_div_iff_of_pos_right (by positivity)]
        linarith


theorem q40b_cov_bound {D : DynData d} {ρ : ℝ → Torus d → ℝ} {t : Fin p → ℝ}
    {F ft : Fin p → ℝ → Torus d → ℝ} {Ca : Fin p → ℝ} {m : ℝ} (h : Br D ρ t F ft Ca m)
    (hN : 0 < N) {P : Measure Ω} [IsProbabilityMeasure P] {X : ℝ≥0 → Ω → Config d N}
    (hXm : ∀ r : ℝ≥0, Measurable (X r))
    (hSgm : Measurable (Function.uncurry (covMatrixProcess (qPhi D t F X))))
    {H : ℝ} (hH0 : 0 ≤ H)
    (hent : ∀ σ, 0 ≤ σ → relEntropy (P.map (X σ.toNNReal))
      (Measure.pi fun _ : Fin N => withDensityReal (ρ σ)) ≤ ENNReal.ofReal H)
    {T : ℝ} (hT0 : 0 ≤ T) (hT : ∀ a, t a ≤ T) :
    covDiscrepancyMatrix P T (covMatrixProcess (qPhi D t F X)) (qsb D ρ t F) ≤
      (∑ a, ∑ b, 2 * D.invβ * Ca a * Ca b / (2 * m)) * Real.sqrt (2 * (H + Real.log 2) / N) := by
  set Sg := covMatrixProcess (qPhi D t F X) with hSg
  set sb := qsb D ρ t F with hsb
  set Δ : ℝ := Real.sqrt (2 * (H + Real.log 2) / N) with hΔ
  have hΔ0 : 0 ≤ Δ := Real.sqrt_nonneg _
  have hq : 0 ≤ 2 * D.invβ := by linarith [D.hβ]
  have hsbm := q40b_qsb_meas D h.t0 h.hF h.rhoJ
  -- the entrywise absolute error, jointly measurable and bounded
  set E : Fin p → Fin p → ℝ × Ω → ℝ := fun a b q => |Sg q.1 q.2 a b - sb q.1 a b| with hE
  have hEm : ∀ a b, Measurable (E a b) := by
    intro a b
    refine Measurable.abs (Measurable.sub ?_ ?_)
    · exact (measurable_pi_apply b).comp ((measurable_pi_apply a).comp hSgm)
    · exact (measurable_pi_apply b).comp ((measurable_pi_apply a).comp hsbm) |>.comp measurable_fst
  have hEb : ∀ a b q, E a b q ≤ 2 * (2 * D.invβ * Ca a * Ca b) := by
    intro a b q
    have h1 := q40b_Sg_bound h hN X q.1 q.2 a b
    have h2 := (q40b_qsb_entry_bound h q.1 a b).2
    calc E a b q ≤ |Sg q.1 q.2 a b| + |sb q.1 a b| := abs_sub _ _
      _ ≤ _ := by linarith
  have hE0 : ∀ a b q, 0 ≤ E a b q := fun a b q => abs_nonneg _
  set Gs : ℝ × Ω → ℝ := fun q => ∑ a, ∑ b, E a b q with hGs
  have hGsm : Measurable Gs := Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => hEm a b
  set Bs : ℝ := ∑ a : Fin p, ∑ b : Fin p, 2 * (2 * D.invβ * Ca a * Ca b) with hBs
  have hGsb : ∀ q, |Gs q| ≤ Bs := by
    intro q
    rw [abs_of_nonneg (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hE0 a b q)]
    exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hEb a b q
  have hGs0 : ∀ q, 0 ≤ Gs q := fun q =>
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => hE0 a b q
  -- inner integrability in `σ`
  have hinner : ∀ ω, Integrable (fun σ => Gs (σ, ω)) (volume.restrict (Set.Icc 0 T)) := fun ω =>
    Measure.integrableOn_of_bounded (M := Bs) measure_Icc_lt_top.ne
      (hGsm.comp measurable_prodMk_right).aestronglyMeasurable
      (Filter.Eventually.of_forall fun σ => by simpa using hGsb (σ, ω))
  -- step 1: pointwise in `ω`
  have step1 : ∀ ω, ∫ σ in Set.Icc 0 T, s1Norm (Sg σ ω - sb σ) ≤ ∫ σ in Set.Icc 0 T, Gs (σ, ω) := by
    intro ω
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun σ => traceNormMatrix_nonneg _)
      (hinner ω) (Filter.Eventually.of_forall fun σ => ?_)
    refine (PDE.MFLinear.traceNormMatrix_le_sum _).trans (le_of_eq ?_)
    simp only [hGs, hE, Matrix.sub_apply]
  -- step 2: integrate in `ω`
  have hOutM : Measurable (fun ω => ∫ σ in Set.Icc 0 T, Gs (σ, ω)) :=
    measurable_setIntegral_Icc (fun q : ℝ × Ω => Gs q) hGsm 0 T
  have hOutI : Integrable (fun ω => ∫ σ in Set.Icc 0 T, Gs (σ, ω)) P := by
    refine Integrable.of_bound (C := Bs * (T - 0)) hOutM.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc (0 : ℝ) T) (C := Bs)
      (f := fun σ => Gs (σ, ω)) measure_Icc_lt_top (fun σ _ => by simpa using hGsb (σ, ω))
    rw [Real.norm_eq_abs] at this
    simpa [Real.volume_real_Icc_of_le hT0] using this
  have step2 : covDiscrepancyMatrix P T Sg sb ≤ ∫ ω, (∫ σ in Set.Icc 0 T, Gs (σ, ω)) ∂P := by
    unfold covDiscrepancyMatrix
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
      setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormMatrix_nonneg _) hOutI
      (Filter.Eventually.of_forall step1)
  -- step 3: swap the integrals
  have hprodI : Integrable (fun q : ℝ × Ω => Gs q) ((volume.restrict (Set.Icc 0 T)).prod P) :=
    Integrable.of_bound (C := Bs) hGsm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => by simpa using hGsb q)
  have step3 : ∫ ω, (∫ σ in Set.Icc 0 T, Gs (σ, ω)) ∂P = ∫ σ in Set.Icc 0 T, (∫ ω, Gs (σ, ω) ∂P) :=
    (integral_integral_swap (f := fun σ ω => Gs (σ, ω)) hprodI).symm
  -- step 4: the bound for fixed `σ`
  set Kab : Fin p → Fin p → ℝ → ℝ := fun a b σ => (Set.Icc 0 (min (t a) (t b))).indicator
    (fun σ => 2 * D.invβ * ((Ca a * Real.exp (-m * (t a - σ))) * (Ca b * Real.exp (-m * (t b - σ)))) * Δ) σ
    with hKab
  have hEint : ∀ a b σ, Integrable (fun ω => E a b (σ, ω)) P := fun a b σ =>
    Integrable.of_bound (C := 2 * (2 * D.invβ * Ca a * Ca b))
      ((hEm a b).comp measurable_prodMk_left).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hE0 a b _)]; exact hEb a b _)
  have hKpt : ∀ a b σ, ∫ ω, E a b (σ, ω) ∂P ≤ Kab a b σ := by
    intro a b σ
    by_cases hσ : σ ∈ Set.Icc 0 (min (t a) (t b))
    · simp only [hKab, Set.indicator_of_mem hσ]
      exact q40b_Q_L1 h hN hXm hH0 hent hσ
    · simp only [hKab, Set.indicator_of_notMem hσ]
      have : ∀ ω, E a b (σ, ω) = 0 := by
        intro ω
        simp only [hE, hSg]
        rw [q40b_sigma_formula hN, if_neg hσ]
        simp only [hsb, qsb, Matrix.of_apply, if_neg hσ, sub_zero, abs_zero]
      simp [this]
  -- step 5: integrate in `σ`
  have hSsub : ∀ a b, Set.Icc (0 : ℝ) (min (t a) (t b)) ⊆ Set.Icc 0 T := fun a b σ hσ =>
    ⟨hσ.1, hσ.2.trans ((min_le_left _ _).trans (hT a))⟩
  have hKint : ∀ a b, Integrable (Kab a b) (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    intro a b
    have hfc : Continuous fun σ : ℝ => 2 * D.invβ * ((Ca a * Real.exp (-m * (t a - σ))) *
        (Ca b * Real.exp (-m * (t b - σ)))) * Δ := by fun_prop
    exact ((hfc.integrableOn_Icc (a := 0) (b := min (t a) (t b))).integrable_indicator
      measurableSet_Icc).integrableOn
  have step4 : ∫ σ in Set.Icc 0 T, (∫ ω, Gs (σ, ω) ∂P) ≤
      ∫ σ in Set.Icc 0 T, ∑ a, ∑ b, Kab a b σ := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun σ =>
      integral_nonneg fun ω => hGs0 _) ?_ (Filter.Eventually.of_forall fun σ => ?_)
    · exact integrable_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ => hKint a b
    · have : ∫ ω, Gs (σ, ω) ∂P = ∑ a, ∑ b, ∫ ω, E a b (σ, ω) ∂P := by
        simp only [hGs]
        rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ fun b _ => hEint a b σ)]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [integral_finset_sum _ (fun b _ => hEint a b σ)]
      show ∫ ω, Gs (σ, ω) ∂P ≤ ∑ a, ∑ b, Kab a b σ
      rw [this]
      exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hKpt a b σ
  have step5 : ∀ a b, ∫ σ in Set.Icc 0 T, Kab a b σ ≤ 2 * D.invβ * Ca a * Ca b / (2 * m) * Δ := by
    intro a b
    have hsub := hSsub a b
    have e1 : ∫ σ in Set.Icc 0 T, Kab a b σ = ∫ σ in Set.Icc (0 : ℝ) (min (t a) (t b)),
        2 * D.invβ * ((Ca a * Real.exp (-m * (t a - σ))) * (Ca b * Real.exp (-m * (t b - σ)))) * Δ := by
      have := setIntegral_indicator (μ := volume) (s := Set.Icc (0 : ℝ) T)
        (t := Set.Icc (0 : ℝ) (min (t a) (t b))) measurableSet_Icc
        (f := fun σ => 2 * D.invβ * ((Ca a * Real.exp (-m * (t a - σ))) *
          (Ca b * Real.exp (-m * (t b - σ)))) * Δ)
      rw [Set.inter_eq_right.2 hsub] at this
      exact this
    rw [e1]
    have e2 : ∀ σ : ℝ, 2 * D.invβ * ((Ca a * Real.exp (-m * (t a - σ))) *
        (Ca b * Real.exp (-m * (t b - σ)))) * Δ =
        (2 * D.invβ * Ca a * Ca b * Δ) * (Real.exp (-m * (t a - σ)) * Real.exp (-m * (t b - σ))) := by
      intro σ; ring
    simp_rw [e2]
    rw [integral_const_mul]
    have hmn : (0 : ℝ) ≤ min (t a) (t b) := le_min (h.t0 a) (h.t0 b)
    have := q40b_exp_int h.hm hmn (min_le_left (t a) (t b)) (min_le_right (t a) (t b))
    have hc : 0 ≤ 2 * D.invβ * Ca a * Ca b * Δ := by
      have := h.hC0 a; have := h.hC0 b; positivity
    calc (2 * D.invβ * Ca a * Ca b * Δ) * ∫ σ in Set.Icc (0 : ℝ) (min (t a) (t b)),
          Real.exp (-m * (t a - σ)) * Real.exp (-m * (t b - σ))
        ≤ (2 * D.invβ * Ca a * Ca b * Δ) * (1 / (2 * m)) := mul_le_mul_of_nonneg_left this hc
      _ = _ := by field_simp
  calc covDiscrepancyMatrix P T Sg sb ≤ ∫ ω, (∫ σ in Set.Icc 0 T, Gs (σ, ω)) ∂P := step2
    _ = ∫ σ in Set.Icc 0 T, (∫ ω, Gs (σ, ω) ∂P) := step3
    _ ≤ ∫ σ in Set.Icc 0 T, ∑ a, ∑ b, Kab a b σ := step4
    _ = ∑ a, ∑ b, ∫ σ in Set.Icc 0 T, Kab a b σ := by
        rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ fun b _ => hKint a b)]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [integral_finset_sum _ (fun b _ => hKint a b)]
    _ ≤ ∑ a, ∑ b, 2 * D.invβ * Ca a * Ca b / (2 * m) * Δ :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => step5 a b
    _ = _ := by rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun a _ => ?_; rw [Finset.sum_mul]

end Bracket

end HRS.Q40b
