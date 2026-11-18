import HRS.Uniform.Q54cAux2
import HRS.Prob.HilbertMartingale

/-!
# Q54c, part 3: the pathwise noise functional and its Riesz element

`PathData` is the deterministic interface between the PDE (propagators) and the probability (a continuous
`E_a`-valued martingale `G`): for a test function `φ` and a terminal time `t`, a `C¹` path
`y t φ : [0,t] → E_a` (the propagated test function `σ ↦ U^{σ,t} φ` viewed in `E_a`), its derivative `y'`
(`σ ↦ 𝓛_σ U^{σ,t} φ`), and `w t φ ∈ E_{a+2}` (the representer of `φ ↦ U^{0,t}φ`, acting on the initial datum).
The pathwise stochastic convolution is the functional
`Λ_t(φ) = ⟨G_t, y_t(t)⟩ - ∫_0^t ⟨G_σ, y'_t(σ)⟩ dσ + A ⟨η, w_t⟩`
(integration by parts of `∫_0^t ⟨dG_σ, U^{σ,t}φ⟩`); `Yelt` is its Riesz element in `E_{a+4}`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q54c

open HRS HRS.Uniform.Q48b HRS.Uniform.Q54

variable {d : ℕ}

/-- The deterministic interface (see the module docstring). -/
structure PathData (d : ℕ) (a : ℝ) where
  y : ℝ → (Torus d → ℝ) → ℝ → NegSobolev d a
  y' : ℝ → (Torus d → ℝ) → ℝ → NegSobolev d a
  w : ℝ → (Torus d → ℝ) → NegSobolev d (a + 2)

variable {a : ℝ}

/-- Properties of `PathData` on `[0,T]` with constant `K`, for smooth test functions. -/
structure PathData.Spec (P : PathData d a) (T K : ℝ) : Prop where
  hK : 0 ≤ K
  hT : 0 ≤ T
  lin_y : ∀ t ∈ Set.Icc 0 T, ∀ σ ∈ Set.Icc 0 t, ∀ φ ψ : Torus d → ℝ, Torus.IsSmooth φ → Torus.IsSmooth ψ →
    ∀ α β : ℝ, P.y t (fun x => α * φ x + β * ψ x) σ = α • P.y t φ σ + β • P.y t ψ σ
  lin_y' : ∀ t ∈ Set.Icc 0 T, ∀ σ ∈ Set.Icc 0 t, ∀ φ ψ : Torus d → ℝ, Torus.IsSmooth φ → Torus.IsSmooth ψ →
    ∀ α β : ℝ, P.y' t (fun x => α * φ x + β * ψ x) σ = α • P.y' t φ σ + β • P.y' t ψ σ
  lin_w : ∀ t ∈ Set.Icc 0 T, ∀ φ ψ : Torus d → ℝ, Torus.IsSmooth φ → Torus.IsSmooth ψ →
    ∀ α β : ℝ, P.w t (fun x => α * φ x + β * ψ x) = α • P.w t φ + β • P.w t ψ
  const_y : ∀ t ∈ Set.Icc 0 T, ∀ σ ∈ Set.Icc 0 t, ∀ c : ℝ, P.y t (fun _ => c) σ = 0
  const_y' : ∀ t ∈ Set.Icc 0 T, ∀ σ ∈ Set.Icc 0 t, ∀ c : ℝ, P.y' t (fun _ => c) σ = 0
  const_w : ∀ t ∈ Set.Icc 0 T, ∀ c : ℝ, P.w t (fun _ => c) = 0
  bd_y : ∀ t ∈ Set.Icc 0 T, ∀ σ ∈ Set.Icc 0 t, ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
    ‖P.y t φ σ‖ ≤ K * sobolevNorm (a + 4) φ
  bd_y' : ∀ t ∈ Set.Icc 0 T, ∀ σ ∈ Set.Icc 0 t, ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
    ‖P.y' t φ σ‖ ≤ K * sobolevNorm (a + 4) φ
  bd_w : ∀ t ∈ Set.Icc 0 T, ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
    ‖P.w t φ‖ ≤ K * sobolevNorm (a + 4) φ
  deriv : ∀ t ∈ Set.Icc 0 T, ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → ∀ σ ∈ Set.Icc 0 t,
    HasDerivWithinAt (fun s => P.y t φ s) (P.y' t φ σ) (Set.Icc 0 t) σ
  cont_y' : ∀ t ∈ Set.Icc 0 T, ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → ContinuousOn (P.y' t φ) (Set.Icc 0 t)
  lip_y : ∀ t ∈ Set.Icc 0 T, ∀ t' ∈ Set.Icc 0 T, ∀ σ ∈ Set.Icc 0 (min t t'), ∀ φ : Torus d → ℝ,
    Torus.IsSmooth φ → ‖P.y t φ σ - P.y t' φ σ‖ ≤ K * |t - t'| * sobolevNorm (a + 4) φ
  lip_y' : ∀ t ∈ Set.Icc 0 T, ∀ t' ∈ Set.Icc 0 T, ∀ σ ∈ Set.Icc 0 (min t t'), ∀ φ : Torus d → ℝ,
    Torus.IsSmooth φ → ‖P.y' t φ σ - P.y' t' φ σ‖ ≤ K * |t - t'| * sobolevNorm (a + 4) φ
  lip_w : ∀ t ∈ Set.Icc 0 T, ∀ t' ∈ Set.Icc 0 T, ∀ φ : Torus d → ℝ,
    Torus.IsSmooth φ → ‖P.w t φ - P.w t' φ‖ ≤ K * |t - t'| * sobolevNorm (a + 4) φ
  /-- at time `0` the propagator is the identity -/
  w_zero : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → ∀ z : NegSobolev d (a + 2),
    inner ℝ z (P.w 0 φ) = NegSobolev.eval z φ

/-- The pathwise noise functional `⟨G_t, y_t(t)⟩ - ∫_0^t ⟨G_σ, y'_t(σ)⟩ dσ`. -/
def PathData.noiseF (P : PathData d a) (G : ℝ → NegSobolev d a) (t : ℝ) (φ : Torus d → ℝ) : ℝ :=
  inner ℝ (G t) (P.y t φ t) - ∫ σ in Set.Icc 0 t, inner ℝ (G σ) (P.y' t φ σ)

/-- The initial-datum functional `⟨η, w_t(φ)⟩`. -/
def PathData.initF (P : PathData d a) (η : NegSobolev d (a + 2)) (t : ℝ) (φ : Torus d → ℝ) : ℝ :=
  inner ℝ η (P.w t φ)

/-- The total functional `Λ_t(φ) = noiseF + A · initF`. -/
def PathData.lam (P : PathData d a) (A : ℝ) (η : NegSobolev d (a + 2)) (G : ℝ → NegSobolev d a)
    (t : ℝ) (φ : Torus d → ℝ) : ℝ :=
  P.noiseF G t φ + A * P.initF η t φ

/-- The `E_{a+4}`-valued process `Ŷ_t = Riesz(Λ_t)`. -/
def PathData.Yelt (P : PathData d a) (A : ℝ) (η : NegSobolev d (a + 2)) (G : ℝ → NegSobolev d a)
    (t : ℝ) : NegSobolev d (a + 4) :=
  rieszElt (a + 4) (P.lam A η G t)

section Bounds

variable {P : PathData d a} {T K : ℝ} (hP : P.Spec T K) {G : ℝ → NegSobolev d a}

include hP

/-- the integrand of the noise functional is continuous on `[0,t]`. -/
theorem integrand_continuousOn (hG : ContinuousOn G (Set.Icc 0 T)) {t : ℝ} (ht : t ∈ Set.Icc 0 T)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ContinuousOn (fun σ => inner ℝ (G σ) (P.y' t φ σ)) (Set.Icc 0 t) := by
  refine ContinuousOn.inner (hG.mono (Set.Icc_subset_Icc_right ht.2)) (hP.cont_y' t ht φ hφ)

theorem integrand_integrableOn (hG : ContinuousOn G (Set.Icc 0 T)) {t : ℝ} (ht : t ∈ Set.Icc 0 T)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    IntegrableOn (fun σ => inner ℝ (G σ) (P.y' t φ σ)) (Set.Icc 0 t) :=
  (integrand_continuousOn hP hG ht hφ).integrableOn_Icc

/-- `G` is bounded on `[0,T]` by `M`. -/
theorem noiseF_bd {M : ℝ} (hG : ContinuousOn G (Set.Icc 0 T)) (hM : ∀ σ ∈ Set.Icc 0 T, ‖G σ‖ ≤ M)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    |P.noiseF G t φ| ≤ (M * K + T * (M * K)) * sobolevNorm (a + 4) φ := by
  unfold PathData.noiseF
  have hn0 : 0 ≤ sobolevNorm (a + 4) φ := Real.sqrt_nonneg _
  have h1 : |inner ℝ (G t) (P.y t φ t)| ≤ M * K * sobolevNorm (a + 4) φ := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    have := hP.bd_y t ht t ⟨ht.1, le_rfl⟩ φ hφ
    have hGt := hM t ht
    calc ‖G t‖ * ‖P.y t φ t‖ ≤ M * (K * sobolevNorm (a + 4) φ) :=
          mul_le_mul hGt this (norm_nonneg _) ((norm_nonneg _).trans hGt)
      _ = _ := by ring
  have h2 : |∫ σ in Set.Icc 0 t, inner ℝ (G σ) (P.y' t φ σ)| ≤ T * (M * K * sobolevNorm (a + 4) φ) := by
    rw [← Real.norm_eq_abs]
    have hb : ∀ σ ∈ Set.Icc 0 t, ‖inner ℝ (G σ) (P.y' t φ σ)‖ ≤ M * K * sobolevNorm (a + 4) φ := by
      intro σ hσ
      rw [Real.norm_eq_abs]
      refine (abs_real_inner_le_norm _ _).trans ?_
      have h3 := hP.bd_y' t ht σ hσ φ hφ
      have hGs := hM σ ⟨hσ.1, hσ.2.trans ht.2⟩
      calc ‖G σ‖ * ‖P.y' t φ σ‖ ≤ M * (K * sobolevNorm (a + 4) φ) :=
            mul_le_mul hGs h3 (norm_nonneg _) ((norm_nonneg _).trans hGs)
        _ = _ := by ring
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc (0 : ℝ) t)
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top) hb
    refine this.trans ?_
    rw [Real.volume_real_Icc_of_le ht.1, sub_zero]
    have hM0 : 0 ≤ M * K * sobolevNorm (a + 4) φ := by
      have := hM 0 ⟨le_rfl, hP.hT⟩
      have h0M : 0 ≤ M := (norm_nonneg _).trans this
      have := hP.hK
      positivity
    rw [mul_comm (M * K * sobolevNorm (a + 4) φ) t]
    exact mul_le_mul_of_nonneg_right ht.2 hM0
  calc |inner ℝ (G t) (P.y t φ t) - ∫ σ in Set.Icc 0 t, inner ℝ (G σ) (P.y' t φ σ)|
      ≤ |inner ℝ (G t) (P.y t φ t)| + |∫ σ in Set.Icc 0 t, inner ℝ (G σ) (P.y' t φ σ)| := abs_sub _ _
    _ ≤ M * K * sobolevNorm (a + 4) φ + T * (M * K * sobolevNorm (a + 4) φ) := add_le_add h1 h2
    _ = _ := by ring

theorem initF_bd (η : NegSobolev d (a + 2)) {t : ℝ} (ht : t ∈ Set.Icc 0 T) {φ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) :
    |P.initF η t φ| ≤ ‖η‖ * K * sobolevNorm (a + 4) φ := by
  unfold PathData.initF
  refine (abs_real_inner_le_norm _ _).trans ?_
  calc ‖η‖ * ‖P.w t φ‖ ≤ ‖η‖ * (K * sobolevNorm (a + 4) φ) :=
        mul_le_mul_of_nonneg_left (hP.bd_w t ht φ hφ) (norm_nonneg _)
    _ = _ := by ring

theorem noiseF_lin (hG : ContinuousOn G (Set.Icc 0 T)) {t : ℝ} (ht : t ∈ Set.Icc 0 T)
    {φ ψ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (hψ : Torus.IsSmooth ψ) (α β : ℝ) :
    P.noiseF G t (fun x => α * φ x + β * ψ x) = α * P.noiseF G t φ + β * P.noiseF G t ψ := by
  unfold PathData.noiseF
  have hy := hP.lin_y t ht t ⟨ht.1, le_rfl⟩ φ ψ hφ hψ α β
  rw [hy, inner_add_right, inner_smul_right, inner_smul_right]
  have hint : (∫ σ in Set.Icc 0 t, inner ℝ (G σ) (P.y' t (fun x => α * φ x + β * ψ x) σ)) =
      α * (∫ σ in Set.Icc 0 t, inner ℝ (G σ) (P.y' t φ σ)) +
        β * (∫ σ in Set.Icc 0 t, inner ℝ (G σ) (P.y' t ψ σ)) := by
    rw [setIntegral_congr_fun measurableSet_Icc (g := fun σ => α * inner ℝ (G σ) (P.y' t φ σ) +
      β * inner ℝ (G σ) (P.y' t ψ σ)) (fun σ hσ => by
        simp only []
        rw [hP.lin_y' t ht σ hσ φ ψ hφ hψ α β, inner_add_right, inner_smul_right, inner_smul_right])]
    rw [integral_add ((integrand_integrableOn hP hG ht hφ).const_mul α)
      ((integrand_integrableOn hP hG ht hψ).const_mul β), integral_const_mul, integral_const_mul]
  rw [hint]; ring

theorem noiseF_const (t : ℝ) (ht : t ∈ Set.Icc 0 T) (c : ℝ) :
    P.noiseF G t (fun _ => c) = 0 := by
  unfold PathData.noiseF
  rw [hP.const_y t ht t ⟨ht.1, le_rfl⟩ c]
  have : (∫ σ in Set.Icc 0 t, inner ℝ (G σ) (P.y' t (fun _ => c) σ)) = 0 := by
    rw [setIntegral_congr_fun measurableSet_Icc (g := fun _ => (0 : ℝ)) (fun σ hσ => by
      simp only []
      rw [hP.const_y' t ht σ hσ c, inner_zero_right])]
    simp
  rw [this]; simp

theorem initF_lin (η : NegSobolev d (a + 2)) {t : ℝ} (ht : t ∈ Set.Icc 0 T)
    {φ ψ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (hψ : Torus.IsSmooth ψ) (α β : ℝ) :
    P.initF η t (fun x => α * φ x + β * ψ x) = α * P.initF η t φ + β * P.initF η t ψ := by
  unfold PathData.initF
  rw [hP.lin_w t ht φ ψ hφ hψ α β, inner_add_right, inner_smul_right, inner_smul_right]

theorem initF_const (η : NegSobolev d (a + 2)) {t : ℝ} (ht : t ∈ Set.Icc 0 T) (c : ℝ) :
    P.initF η t (fun _ => c) = 0 := by
  unfold PathData.initF
  rw [hP.const_w t ht c, inner_zero_right]

/-- Riesz hypotheses for the total functional. -/
theorem lam_rieszHyp {M : ℝ} (hG : ContinuousOn G (Set.Icc 0 T))
    (hM : ∀ σ ∈ Set.Icc 0 T, ‖G σ‖ ≤ M) (A : ℝ) (η : NegSobolev d (a + 2)) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) :
    RieszHyp (a + 4) ((M * K + T * (M * K)) + |A| * (‖η‖ * K)) (P.lam A η G t) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hP.hT⟩)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hP.hK; have := hP.hT; positivity
  · intro φ ψ hφ hψ α β
    unfold PathData.lam
    rw [noiseF_lin hP hG ht hφ hψ, initF_lin hP η ht hφ hψ]; ring
  · intro φ hφ
    unfold PathData.lam
    have h1 := noiseF_bd hP hG hM ht hφ
    have h2 := initF_bd hP η ht hφ
    calc |P.noiseF G t φ + A * P.initF η t φ| ≤ |P.noiseF G t φ| + |A * P.initF η t φ| := abs_add_le _ _
      _ ≤ (M * K + T * (M * K)) * sobolevNorm (a + 4) φ + |A| * (‖η‖ * K * sobolevNorm (a + 4) φ) := by
          rw [abs_mul]; exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 (abs_nonneg _))
      _ = _ := by ring
  · intro c
    unfold PathData.lam
    rw [noiseF_const hP t ht c, initF_const hP η ht c]; ring

theorem Yelt_eval {M : ℝ} (hG : ContinuousOn G (Set.Icc 0 T))
    (hM : ∀ σ ∈ Set.Icc 0 T, ‖G σ‖ ≤ M) (A : ℝ) (η : NegSobolev d (a + 2)) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    NegSobolev.eval (P.Yelt A η G t) φ = P.lam A η G t φ :=
  rieszElt_eval (lam_rieszHyp hP hG hM A η ht) hφ

theorem Yelt_norm_le {M : ℝ} (hG : ContinuousOn G (Set.Icc 0 T))
    (hM : ∀ σ ∈ Set.Icc 0 T, ‖G σ‖ ≤ M) (A : ℝ) (η : NegSobolev d (a + 2)) {t : ℝ}
    (ht : t ∈ Set.Icc 0 T) :
    ‖P.Yelt A η G t‖ ≤ (M * K + T * (M * K)) + |A| * (‖η‖ * K) :=
  rieszElt_norm_le (lam_rieszHyp hP hG hM A η ht)

/-- Lipschitz-type estimate for the total functional in the terminal time. -/
theorem lam_sub_bd {M : ℝ} (hG : ContinuousOn G (Set.Icc 0 T))
    (hM : ∀ σ ∈ Set.Icc 0 T, ‖G σ‖ ≤ M) (A : ℝ) (η : NegSobolev d (a + 2)) {t t' : ℝ}
    (ht : t ∈ Set.Icc 0 T) (ht' : t' ∈ Set.Icc 0 T) (htt' : t' ≤ t) {φ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) :
    |P.lam A η G t φ - P.lam A η G t' φ| ≤
      (K * ‖G t - G t'‖ + ((3 + T) * M * K + |A| * (‖η‖ * K)) * |t - t'|) * sobolevNorm (a + 4) φ := by
  have hn0 : 0 ≤ sobolevNorm (a + 4) φ := Real.sqrt_nonneg _
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hP.hT⟩)
  have hK0 := hP.hK
  have hT0 := hP.hT
  set n := sobolevNorm (a + 4) φ with hn
  have hdt : |t - t'| = t - t' := abs_of_nonneg (sub_nonneg.2 htt')
  rw [hdt]
  have hmin : min t t' = t' := min_eq_right htt'
  -- term 1
  have hy1 : ‖P.y t φ t - P.y t φ t'‖ ≤ K * n * (t - t') := by
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun s => P.y t φ s)
      (f' := fun σ => P.y' t φ σ) (s := Set.Icc 0 t) (C := K * n)
      (fun σ hσ => hP.deriv t ht φ hφ σ hσ) (fun σ hσ => hP.bd_y' t ht σ hσ φ hφ)
      (convex_Icc 0 t) (x := t') (y := t) ⟨ht'.1, htt'⟩ ⟨ht.1, le_rfl⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 htt')] at this
    exact this
  have hy2 : ‖P.y t φ t' - P.y t' φ t'‖ ≤ K * (t - t') * n := by
    have := hP.lip_y t ht t' ht' t' ⟨ht'.1, by rw [hmin]⟩ φ hφ
    rwa [hdt] at this
  have hterm1 : |inner ℝ (G t) (P.y t φ t) - inner ℝ (G t') (P.y t' φ t')| ≤
      K * ‖G t - G t'‖ * n + M * (2 * (K * n * (t - t'))) := by
    have e : inner ℝ (G t) (P.y t φ t) - inner ℝ (G t') (P.y t' φ t') =
        inner ℝ (G t - G t') (P.y t φ t) + inner ℝ (G t') (P.y t φ t - P.y t' φ t') := by
      rw [inner_sub_left, inner_sub_right]; ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (abs_real_inner_le_norm _ _).trans ?_
      have := hP.bd_y t ht t ⟨ht.1, le_rfl⟩ φ hφ
      calc ‖G t - G t'‖ * ‖P.y t φ t‖ ≤ ‖G t - G t'‖ * (K * n) :=
            mul_le_mul_of_nonneg_left this (norm_nonneg _)
        _ = _ := by ring
    · refine (abs_real_inner_le_norm _ _).trans ?_
      have h1 : ‖P.y t φ t - P.y t' φ t'‖ ≤ 2 * (K * n * (t - t')) := by
        have := norm_sub_le_norm_sub_add_norm_sub (P.y t φ t) (P.y t φ t') (P.y t' φ t')
        nlinarith [this, hy1, hy2]
      exact mul_le_mul (hM t' ht') h1 (norm_nonneg _) hM0
  -- term 2
  set f : ℝ → (Torus d → ℝ) → ℝ → ℝ := fun τ ψ σ => inner ℝ (G σ) (P.y' τ ψ σ) with hf
  have hfc : ∀ τ ∈ Set.Icc 0 T, ContinuousOn (f τ φ) (Set.Icc 0 τ) := fun τ hτ =>
    integrand_continuousOn hP hG hτ hφ
  have hII : ∀ τ ∈ Set.Icc 0 T, (∫ σ in Set.Icc 0 τ, f τ φ σ) = ∫ σ in (0 : ℝ)..τ, f τ φ σ := by
    intro τ hτ
    rw [intervalIntegral.integral_of_le hτ.1, integral_Icc_eq_integral_Ioc]
  have hii : ∀ τ ∈ Set.Icc 0 T, ∀ u v : ℝ, u ∈ Set.Icc 0 τ → v ∈ Set.Icc 0 τ →
      IntervalIntegrable (f τ φ) volume u v := by
    intro τ hτ u v hu hv
    have h0 : IntervalIntegrable (f τ φ) volume 0 τ :=
      (hfc τ hτ).intervalIntegrable_of_Icc hτ.1
    refine h0.mono_set ?_
    rw [Set.uIcc_of_le hτ.1]
    exact Set.uIcc_subset_Icc hu hv
  have h0t' : (0 : ℝ) ∈ Set.Icc 0 t' := ⟨le_rfl, ht'.1⟩
  have h0t : (0 : ℝ) ∈ Set.Icc 0 t := ⟨le_rfl, ht.1⟩
  have ht'in : t' ∈ Set.Icc 0 t := ⟨ht'.1, htt'⟩
  have htin : t ∈ Set.Icc 0 t := ⟨ht.1, le_rfl⟩
  have hsplit : (∫ σ in (0 : ℝ)..t, f t φ σ) =
      (∫ σ in (0 : ℝ)..t', f t φ σ) + ∫ σ in t'..t, f t φ σ :=
    (intervalIntegral.integral_add_adjacent_intervals (hii t ht 0 t' h0t ht'in)
      (hii t ht t' t ht'in htin)).symm
  have hdiff : (∫ σ in Set.Icc 0 t, f t φ σ) - ∫ σ in Set.Icc 0 t', f t' φ σ =
      (∫ σ in (0 : ℝ)..t', (f t φ σ - f t' φ σ)) + ∫ σ in t'..t, f t φ σ := by
    rw [hII t ht, hII t' ht', hsplit, intervalIntegral.integral_sub (hii t ht 0 t' h0t ht'in)
      (hii t' ht' 0 t' h0t' ⟨ht'.1, le_rfl⟩)]
    ring
  have hb1 : ‖∫ σ in (0 : ℝ)..t', (f t φ σ - f t' φ σ)‖ ≤ (M * (K * (t - t') * n)) * |t' - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ => ?_
    rw [Set.uIoc_of_le ht'.1] at hσ
    have hσ' : σ ∈ Set.Icc 0 (min t t') := ⟨hσ.1.le, by rw [hmin]; exact hσ.2⟩
    have e : f t φ σ - f t' φ σ = inner ℝ (G σ) (P.y' t φ σ - P.y' t' φ σ) := by
      simp only [hf, inner_sub_right]
    rw [e, Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    have := hP.lip_y' t ht t' ht' σ hσ' φ hφ
    rw [hdt] at this
    exact mul_le_mul (hM σ ⟨hσ.1.le, hσ.2.trans ht'.2⟩) this (norm_nonneg _) hM0
  have hb2 : ‖∫ σ in t'..t, f t φ σ‖ ≤ (M * (K * n)) * |t - t'| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ => ?_
    rw [Set.uIoc_of_le htt'] at hσ
    have hσt : σ ∈ Set.Icc 0 t := ⟨ht'.1.trans hσ.1.le, hσ.2⟩
    rw [Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul (hM σ ⟨hσt.1, hσt.2.trans ht.2⟩) (hP.bd_y' t ht σ hσt φ hφ) (norm_nonneg _) hM0
  have hterm2 : |(∫ σ in Set.Icc 0 t, f t φ σ) - ∫ σ in Set.Icc 0 t', f t' φ σ| ≤
      (T + 1) * M * K * n * (t - t') := by
    rw [hdiff, ← Real.norm_eq_abs]
    refine (norm_add_le _ _).trans ?_
    rw [abs_of_nonneg (sub_nonneg.2 htt'), sub_zero, abs_of_nonneg ht'.1] at *
    have ht'T : t' ≤ T := ht'.2
    have h1 : (M * (K * (t - t') * n)) * t' ≤ (M * (K * (t - t') * n)) * T :=
      mul_le_mul_of_nonneg_left ht'T (by
        have : 0 ≤ t - t' := sub_nonneg.2 htt'
        positivity)
    nlinarith [hb1, hb2, h1]
  -- term 3
  have hterm3 : |A * P.initF η t φ - A * P.initF η t' φ| ≤ |A| * (‖η‖ * K) * (t - t') * n := by
    rw [← mul_sub, abs_mul]
    unfold PathData.initF
    rw [← inner_sub_right]
    have h1 := (abs_real_inner_le_norm η (P.w t φ - P.w t' φ))
    have h2 := hP.lip_w t ht t' ht' φ hφ
    rw [hdt] at h2
    have : |inner ℝ η (P.w t φ - P.w t' φ)| ≤ ‖η‖ * (K * (t - t') * n) :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
    calc |A| * |inner ℝ η (P.w t φ - P.w t' φ)| ≤ |A| * (‖η‖ * (K * (t - t') * n)) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = _ := by ring
  have e : P.lam A η G t φ - P.lam A η G t' φ =
      (inner ℝ (G t) (P.y t φ t) - inner ℝ (G t') (P.y t' φ t')) -
        ((∫ σ in Set.Icc 0 t, f t φ σ) - ∫ σ in Set.Icc 0 t', f t' φ σ) +
        (A * P.initF η t φ - A * P.initF η t' φ) := by
    unfold PathData.lam PathData.noiseF
    simp only [hf]; ring
  rw [e]
  calc _ ≤ |(inner ℝ (G t) (P.y t φ t) - inner ℝ (G t') (P.y t' φ t')) -
        ((∫ σ in Set.Icc 0 t, f t φ σ) - ∫ σ in Set.Icc 0 t', f t' φ σ)| +
        |A * P.initF η t φ - A * P.initF η t' φ| := abs_add_le _ _
    _ ≤ (|inner ℝ (G t) (P.y t φ t) - inner ℝ (G t') (P.y t' φ t')| +
        |(∫ σ in Set.Icc 0 t, f t φ σ) - ∫ σ in Set.Icc 0 t', f t' φ σ|) +
        |A * P.initF η t φ - A * P.initF η t' φ| := add_le_add (abs_sub _ _) le_rfl
    _ ≤ (K * ‖G t - G t'‖ * n + M * (2 * (K * n * (t - t')))) + (T + 1) * M * K * n * (t - t') +
        |A| * (‖η‖ * K) * (t - t') * n := by
        gcongr
    _ = _ := by ring

theorem Yelt_sub_norm_le {M : ℝ} (hG : ContinuousOn G (Set.Icc 0 T))
    (hM : ∀ σ ∈ Set.Icc 0 T, ‖G σ‖ ≤ M) (A : ℝ) (η : NegSobolev d (a + 2)) {t t' : ℝ}
    (ht : t ∈ Set.Icc 0 T) (ht' : t' ∈ Set.Icc 0 T) :
    ‖P.Yelt A η G t - P.Yelt A η G t'‖ ≤
      K * ‖G t - G t'‖ + ((3 + T) * M * K + |A| * (‖η‖ * K)) * |t - t'| := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hP.hT⟩)
  have hK0 := hP.hK
  have hT0 := hP.hT
  set B : ℝ := K * ‖G t - G t'‖ + ((3 + T) * M * K + |A| * (‖η‖ * K)) * |t - t'| with hB
  have hB0 : 0 ≤ B := by positivity
  have hH1 := lam_rieszHyp hP hG hM A η ht
  have hH2 := lam_rieszHyp hP hG hM A η ht'
  have hH : RieszHyp (a + 4) B (fun φ => P.lam A η G t φ - P.lam A η G t' φ) := by
    refine ⟨hB0, ?_, ?_, ?_⟩
    · intro φ ψ hφ hψ α β
      rw [hH1.lin φ ψ hφ hψ α β, hH2.lin φ ψ hφ hψ α β]; ring
    · intro φ hφ
      rcases le_total t' t with h | h
      · exact lam_sub_bd hP hG hM A η ht ht' h hφ
      · have := lam_sub_bd hP hG hM A η ht' ht h hφ
        rw [abs_sub_comm, norm_sub_rev (G t') (G t), abs_sub_comm t' t] at this
        exact this
    · intro c
      rw [hH1.const c, hH2.const c]; ring
  have heq : rieszElt (a + 4) (fun φ => P.lam A η G t φ - P.lam A η G t' φ) =
      P.Yelt A η G t - P.Yelt A η G t' := by
    refine Subtype.ext (funext fun k => ?_)
    have e1 := rieszElt_coord hH k
    have e2 := rieszElt_coord hH1 k
    have e3 := rieszElt_coord hH2 k
    show NegSobolev.coord (rieszElt (a + 4) _) k =
      NegSobolev.coord (P.Yelt A η G t - P.Yelt A η G t') k
    rw [NegSobolev.coord_sub']
    unfold PathData.Yelt
    rw [e1, e2, e3]; ring
  rw [← heq]
  exact rieszElt_norm_le hH

end Bounds

end HRS.Uniform.Q54c
