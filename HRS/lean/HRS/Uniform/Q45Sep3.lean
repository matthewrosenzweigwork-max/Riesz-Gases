import HRS.Uniform.Q45Sep2
import HRS.Uniform.Q45Lim1
import HRS.Uniform.Q45Path2

/-!
# Q45 (Lemma 3.20): terminal observations separate the points of `𝒴 ⊗̂_π 𝒴`
-/

noncomputable section

open MeasureTheory Filter Topology UniformSpace
open scoped ENNReal NNReal BigOperators TensorProduct

namespace HRS.Uniform.Q45

section Abstract

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma tmul_zero_left (c : Y) : tmul 0 c = 0 := by
  have := tmul_smul_left 0 (0 : Y) c
  simpa using this

lemma tmul_zero_right (c : Y) : tmul c 0 = 0 := by
  have := tmul_smul_right 0 c (0 : Y)
  simpa using this

lemma tmul_sum_left {ι : Type*} (s : Finset ι) (f : ι → Y) (c : Y) :
    tmul (∑ p ∈ s, f p) c = ∑ p ∈ s, tmul (f p) c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tmul_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, tmul_add_left, ih]

lemma tmul_sum_right {ι : Type*} (s : Finset ι) (f : ι → Y) (c : Y) :
    tmul c (∑ p ∈ s, f p) = ∑ p ∈ s, tmul c (f p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tmul_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, tmul_add_right, ih]

lemma tmul_sum_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (c : ι → ℝ) (u : ι → Y) (d : κ → ℝ)
    (v : κ → Y) :
    tmul (∑ p, c p • u p) (∑ q, d q • v q) = ∑ p, ∑ q, (c p * d q) • tmul (u p) (v q) := by
  rw [tmul_sum_left]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [tmul_smul_left, tmul_sum_right, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [tmul_smul_right, smul_smul]

lemma tensorPairingL_tmul (Ψ : Y →L[ℝ] Y →L[ℝ] ℝ) (y y' : Y) :
    tensorPairingL Ψ (tmul y y') = Ψ y y' := by
  have := tensorPairing_tmul Ψ y y'
  rwa [tensorPairing_eq] at this

/-- Abstract separation: a tensor killed by all pairings with the product forms `φ_p ⊗ φ_q` of a finite-rank
approximation of the identity vanishes. -/
theorem tensor_zero_of_approx (Λ : ℕ → Y →L[ℝ] Y) (hb : ∀ n, ‖Λ n‖ ≤ 1)
    (hl : ∀ y, Tendsto (fun n => Λ n y) atTop (𝓝 y))
    {ι : ℕ → Type} [∀ n, Fintype (ι n)] (φ : ∀ n, ι n → Y →L[ℝ] ℝ) (u : ∀ n, ι n → Y)
    (hexp : ∀ n y, Λ n y = ∑ p, φ n p y • u n p)
    (τ : ProjTensor2 Y)
    (h : ∀ n p q, tensorPairingL ((φ n p).smulRight (φ n q)) τ = 0) : τ = 0 := by
  have hmap : ∀ n, tensorMap (Λ n) τ = 0 := by
    intro n
    have hext : tensorMap (Λ n) = ∑ p, ∑ q, (tensorPairingL ((φ n p).smulRight (φ n q))).smulRight
        (tmul (u n p) (u n q)) := by
      refine tensor_clm_ext _ _ fun y y' => ?_
      rw [tensorMap_tmul, hexp, hexp, tmul_sum_sum]
      simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
        tensorPairingL_tmul]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      simp
    rw [hext]
    simp [ContinuousLinearMap.sum_apply, h]
  have hbd : ∀ n, ‖tensorMap (Λ n)‖ ≤ 1 := by
    intro n
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun τ' => ?_
    refine (norm_tensorMap_le (Λ n) τ').trans ?_
    have : ‖Λ n‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hb n)
    nlinarith [norm_nonneg τ']
  have hconv : ∀ y y', Tendsto (fun n => tensorMap (Λ n) (tmul y y')) atTop (𝓝 (tmul y y')) := by
    intro y y'
    simp only [tensorMap_tmul]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h1 := tendsto_iff_norm_sub_tendsto_zero.1 (hl y)
    have h2 := tendsto_iff_norm_sub_tendsto_zero.1 (hl y')
    have h3 : Tendsto (fun n => ‖Λ n y - y‖ * ‖y'‖ + ‖y‖ * ‖Λ n y' - y'‖) atTop (𝓝 (0 * ‖y'‖ + ‖y‖ * 0)) :=
      (h1.mul_const _).add (h2.const_mul _)
    rw [zero_mul, mul_zero, add_zero] at h3
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h3
    refine (norm_tmul_sub_le _ _ _ _).trans ?_
    have : ‖Λ n y'‖ ≤ ‖y'‖ := ((Λ n).le_opNorm y').trans
      (by nlinarith [hb n, norm_nonneg y', norm_nonneg (Λ n)])
    nlinarith [norm_nonneg (Λ n y - y), norm_nonneg y, norm_nonneg (Λ n y' - y')]
  have hT := tensor_tendsto_of_bdd (fun n => tensorMap (Λ n)) hbd hconv τ
  simp only [hmap] at hT
  exact tendsto_nhds_unique hT tendsto_const_nhds

end Abstract

section Concrete

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma projB_add {d : ℕ} (b : Fin d → E) (w w' : E) : projB b (w + w') = projB b w + projB b w' := by
  simp [projB, inner_add_right, add_smul, Finset.sum_add_distrib]

lemma projB_smul {d : ℕ} (b : Fin d → E) (r : ℝ) (w : E) : projB b (r • w) = r • projB b w := by
  simp [projB, inner_smul_right, smul_smul, Finset.smul_sum]

lemma samplePath_add {T : ℝ} (hT : 0 ≤ T) (g : ℕ) (y y' : PathSp T E) :
    samplePath hT g (y + y') = samplePath hT g y + samplePath hT g y' := by
  funext i; simp [samplePath, pcm_add]

lemma samplePath_smul {T : ℝ} (hT : 0 ≤ T) (g : ℕ) (r : ℝ) (y : PathSp T E) :
    samplePath hT g (r • y) = r • samplePath hT g y := by
  funext i; simp [samplePath, pcm_smul]

/-- The approximation `Λ_n` of the identity of `C([0,T];E)` by grid interpolation of finite-rank projections of the
node values, as a bounded linear map. -/
def lamCLM {T : ℝ} (hT : 0 < T) {d : ℕ} (b : Fin d → E) (hb : Orthonormal ℝ b) (n : ℕ) :
    PathSp T E →L[ℝ] PathSp T E :=
  LinearMap.mkContinuous
    { toFun := fun y => hatPath T (n + 1) (fun i => projB b (samplePath hT.le (n + 1) y i))
      map_add' := fun y y' => by
        rw [← hatPath_add]
        congr 1
        funext i
        simp [samplePath_add, projB_add]
      map_smul' := fun r y => by
        rw [RingHom.id_apply, ← hatPath_smul]
        congr 1
        funext i
        simp [samplePath_smul, projB_smul] } 1
    (fun y => by
      rw [one_mul]
      refine norm_hatPath_le hT (Nat.le_add_left 1 n) _ (norm_nonneg _) fun i => ?_
      exact (norm_projB_le hb _).trans (norm_pcm_apply_le y _))

lemma lamCLM_apply {T : ℝ} (hT : 0 < T) {d : ℕ} (b : Fin d → E) (hb : Orthonormal ℝ b) (n : ℕ)
    (y : PathSp T E) :
    lamCLM hT b hb n y = hatPath T (n + 1) (fun i => projB b (samplePath hT.le (n + 1) y i)) := rfl

lemma norm_lamCLM_le {T : ℝ} (hT : 0 < T) {d : ℕ} (b : Fin d → E) (hb : Orthonormal ℝ b) (n : ℕ) :
    ‖lamCLM hT b hb n‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Finite-rank expansion of `Λ_n`. -/
lemma lamCLM_expand {T : ℝ} (hT : 0 < T) {d : ℕ} (b : Fin d → E) (hb : Orthonormal ℝ b) (n : ℕ)
    (y : PathSp T E) :
    lamCLM hT b hb n y = ∑ p : Fin (n + 1 + 1) × Fin d,
      (inner ℝ (b p.2) (samplePath hT.le (n + 1) y p.1)) •
        hatPath T (n + 1) (Pi.single p.1 (b p.2)) := by
  rw [lamCLM_apply]
  have hv : (fun i => projB b (samplePath hT.le (n + 1) y i)) =
      ∑ p : Fin (n + 1 + 1) × Fin d, (inner ℝ (b p.2) (samplePath hT.le (n + 1) y p.1)) •
        (Pi.single p.1 (b p.2) : Fin (n + 1 + 1) → E) := by
    funext j
    rw [Fintype.sum_prod_type, Finset.sum_apply]
    simp only [Finset.sum_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single j]
    · simp [projB, Pi.single_apply]
    · intro i _ hij
      simp [Pi.single_apply, hij.symm]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hv]
  have := map_sum (hatCLM hT (Nat.le_add_left 1 n) (E := E)) (fun p : Fin (n + 1 + 1) × Fin d =>
    (inner ℝ (b p.2) (samplePath hT.le (n + 1) y p.1)) •
        (Pi.single p.1 (b p.2) : Fin (n + 1 + 1) → E)) Finset.univ
  simp only [hatCLM_apply, map_smul] at this ⊢
  exact this

end Concrete

section Obs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- **Separation.** Terminal observations `(t₁,ℓ₁), (t₂,ℓ₂)` separate the points of `𝒴 ⊗̂_π 𝒴`,
`𝒴 = C([0,T];E)`, `E` a separable Hilbert space, `T > 0`. -/
theorem obs_separate {T : ℝ} (hT : 0 < T) (τ : ProjTensor2 (PathSp T E))
    (h : ∀ (t₁ t₂ : Set.Icc (0 : ℝ) T) (ℓ₁ ℓ₂ : E →L[ℝ] ℝ),
      tensorPairing (obsForm t₁ t₂ ℓ₁ ℓ₂) τ = 0) : τ = 0 := by
  obtain ⟨d, b, hb, hspat⟩ := exists_spatial_approx E
  refine tensor_zero_of_approx (fun n => lamCLM hT (b n) (hb n) n) (fun n => norm_lamCLM_le hT _ _ n)
    ?_ (ι := fun n => Fin (n + 1 + 1) × Fin (d n))
    (fun n p => (innerSL ℝ (b n p.2)).comp
      (PathSp.eval (Set.projIcc 0 T hT.le (p.1 * T / ((n + 1 : ℕ) : ℝ)))))
    (fun n p => hatPath T (n + 1) (Pi.single p.1 (b n p.2))) ?_ τ ?_
  · intro y
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨n0, hn0⟩ := lambda_approx hT hb (hspat T) y (half_pos hε)
    exact ⟨n0, fun n hn => by
      rw [dist_eq_norm]
      exact lt_of_le_of_lt (hn0 n hn) (half_lt_self hε)⟩
  · intro n y
    rw [lamCLM_expand]
    rfl
  · intro n p q
    have := h (Set.projIcc 0 T hT.le (p.1 * T / ((n + 1 : ℕ) : ℝ)))
      (Set.projIcc 0 T hT.le (q.1 * T / ((n + 1 : ℕ) : ℝ))) (innerSL ℝ (b n p.2)) (innerSL ℝ (b n q.2))
    rw [tensorPairing_eq] at this
    exact this

end Obs

end HRS.Uniform.Q45
