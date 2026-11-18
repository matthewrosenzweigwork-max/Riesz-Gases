import HRS.Prob.Metrics
import HRS.Torus.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# S11.1 continuation, T04: the finite common-noise coupling

`P = (N(0,A) ⊗ N(0,B) ⊗ N(0,S))`, `X = w₀ + w₂`, `Y = w₁ + w₂`: the pair `(X,Y)` is jointly centered Gaussian, with the
covariances `A+S`, `B+S` and `X-Y` of covariance `A+B`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HRS.MS.S111K

open HRS (Euc)

section Generic

variable {n : ℕ} (M : Fin 3 → Matrix (Fin n) (Fin n) ℝ)

/-- The product law. -/
def s111k_prodLaw : Measure (Fin 3 → Euc n) :=
  Measure.pi (fun k : Fin 3 => multivariateGaussian (0 : Euc n) (M k))

instance s111k_prodLaw_prob : IsProbabilityMeasure (s111k_prodLaw M) := by
  unfold s111k_prodLaw; infer_instance

variable {M}

theorem s111k_eval_map (k : Fin 3) :
    (s111k_prodLaw M).map (fun w => w k) = multivariateGaussian (0 : Euc n) (M k) :=
  (measurePreserving_eval (fun k : Fin 3 => multivariateGaussian (0 : Euc n) (M k)) k).map_eq

theorem s111k_integral_eval (k : Fin 3) (f : Euc n → ℝ) (hf : AEStronglyMeasurable f (multivariateGaussian (0 : Euc n) (M k))) :
    ∫ w, f (w k) ∂(s111k_prodLaw M) = ∫ x, f x ∂(multivariateGaussian (0 : Euc n) (M k)) := by
  rw [← s111k_eval_map k]
  rw [integral_map (measurable_pi_apply k).aemeasurable (by rw [s111k_eval_map k]; exact hf)]

theorem s111k_memLp_coord (k : Fin 3) (i : Fin n) :
    MemLp (fun x : Euc n => x i) 2 (multivariateGaussian (0 : Euc n) (M k)) := by
  have := IsGaussian.memLp_dual (multivariateGaussian (0 : Euc n) (M k))
    (EuclideanSpace.proj (𝕜 := ℝ) i) 2 (by simp)
  exact this

theorem s111k_memLp_w (k : Fin 3) (i : Fin n) :
    MemLp (fun w : Fin 3 → Euc n => w k i) 2 (s111k_prodLaw M) := by
  have h := s111k_memLp_coord (M := M) k i
  rw [← s111k_eval_map (M := M) k] at h
  have := (memLp_map_measure_iff (g := fun x : Euc n => x i) (f := fun w : Fin 3 → Euc n => w k)
    (p := 2) (μ := s111k_prodLaw M) ?_ (measurable_pi_apply k).aemeasurable).1 h
  · exact this
  · rw [s111k_eval_map k]; exact (by fun_prop : Continuous fun x : Euc n => x i).aestronglyMeasurable

theorem s111k_mean_coord (k : Fin 3) (i : Fin n) :
    ∫ x, x i ∂(multivariateGaussian (0 : Euc n) (M k)) = 0 := by
  have h := integral_id_multivariateGaussian (μ := (0 : Euc n)) (S := M k)
  have h2 : ∫ x : Euc n, x i ∂(multivariateGaussian (0 : Euc n) (M k)) =
      (∫ x : Euc n, x ∂(multivariateGaussian (0 : Euc n) (M k))) i := by
    have := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm
      (IsGaussian.integrable_id (μ := multivariateGaussian (0 : Euc n) (M k)))
    simpa using this
  rw [h2, h]; simp

theorem s111k_mean_w (k : Fin 3) (i : Fin n) : ∫ w, w k i ∂(s111k_prodLaw M) = 0 := by
  have := s111k_integral_eval (M := M) k (fun x => x i)
    (by fun_prop : Continuous fun x : Euc n => x i).aestronglyMeasurable
  rw [this]; exact s111k_mean_coord k i

theorem s111k_second_moment (hM : ∀ k, (M k).PosSemidef) (k : Fin 3) (i j : Fin n) :
    ∫ w, w k i * w k j ∂(s111k_prodLaw M) = M k i j := by
  have h1 := s111k_integral_eval (M := M) k (fun x => x i * x j)
    ((by fun_prop : Continuous fun x : Euc n => x i * x j).aestronglyMeasurable)
  rw [h1]
  have h2 := covariance_eval_multivariateGaussian (μ := (0 : Euc n)) (hM k) i j
  rw [covariance_eq_sub (s111k_memLp_coord k i) (s111k_memLp_coord k j)] at h2
  rw [s111k_mean_coord, s111k_mean_coord] at h2
  simpa using h2

theorem s111k_indep : iIndepFun (fun (k : Fin 3) (w : Fin 3 → Euc n) => w k) (s111k_prodLaw M) :=
  iIndepFun_pi (μ := fun k : Fin 3 => multivariateGaussian (0 : Euc n) (M k))
    (X := fun _ => id) (fun _ => aemeasurable_id)

theorem s111k_cross (k l : Fin 3) (hkl : k ≠ l) (i j : Fin n) :
    ∫ w, w k i * w l j ∂(s111k_prodLaw M) = 0 := by
  have hind := (s111k_indep (M := M)).indepFun hkl
  have h2 := (hind.comp (φ := fun x : Euc n => x i) (ψ := fun x : Euc n => x j)
    (by fun_prop) (by fun_prop))
  have := h2.integral_mul_eq_mul_integral
    (by exact ((s111k_memLp_w k i).aestronglyMeasurable))
    (by exact ((s111k_memLp_w l j).aestronglyMeasurable))
  simp only [Pi.mul_apply, Function.comp_apply] at this
  rw [this]
  have := s111k_mean_w (M := M) k i
  simp [this]

theorem s111k_pair_moment (hM : ∀ k, (M k).PosSemidef) (k l : Fin 3) (i j : Fin n) :
    ∫ w, w k i * w l j ∂(s111k_prodLaw M) = if k = l then M k i j else 0 := by
  by_cases hkl : k = l
  · subst hkl; simpa using s111k_second_moment hM k i j
  · simp [hkl, s111k_cross k l hkl]

theorem s111k_pair_int (k l : Fin 3) (i j : Fin n) :
    Integrable (fun w : Fin 3 → Euc n => w k i * w l j) (s111k_prodLaw M) :=
  (s111k_memLp_w k i).integrable_mul (s111k_memLp_w l j)

/-- The second moment of a linear combination of the three coordinates. -/
theorem s111k_combo_moment (hM : ∀ k, (M k).PosSemidef) (u : Fin 3 → ℝ) (i j : Fin n) :
    ∫ w, (∑ k, u k * w k i) * (∑ l, u l * w l j) ∂(s111k_prodLaw M) = ∑ k, u k ^ 2 * M k i j := by
  have : ∀ w : Fin 3 → Euc n, (∑ k, u k * w k i) * (∑ l, u l * w l j) =
      ∑ k, ∑ l, (u k * u l) * (w k i * w l j) := by
    intro w
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))
  simp_rw [this]
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ =>
    (s111k_pair_int k l i j).const_mul _))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [integral_finsetSum _ (fun l _ => (s111k_pair_int k l i j).const_mul _)]
  simp_rw [integral_const_mul, s111k_pair_moment hM]
  simp [mul_ite, sq]

/-- The linear map `w ↦ (w₀ + w₂, w₁ + w₂)`. -/
def s111k_obs : (Fin 3 → Euc n) →L[ℝ] (Fin 2 × Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w i => if i.1 = 0 then w 0 i.2 + w 2 i.2 else w 1 i.2 + w 2 i.2
      map_add' := by intro a b; ext i; by_cases h : i.1 = 0 <;> simp [h] <;> ring
      map_smul' := by intro c a; ext i; by_cases h : i.1 = 0 <;> simp [h] <;> ring }

theorem s111k_obs_apply (w : Fin 3 → Euc n) (i : Fin 2 × Fin n) :
    s111k_obs w i = if i.1 = 0 then w 0 i.2 + w 2 i.2 else w 1 i.2 + w 2 i.2 := rfl

theorem s111k_hasGaussian (hM : ∀ k, (M k).PosSemidef) :
    HasGaussianLaw (fun w : Fin 3 → Euc n => w) (s111k_prodLaw M) := by
  have hk : ∀ k : Fin 3, HasGaussianLaw (fun w : Fin 3 → Euc n => w k) (s111k_prodLaw M) := by
    intro k
    have : IsGaussian (multivariateGaussian (0 : Euc n) (M k)) := inferInstance
    exact HasLaw.hasGaussianLaw (μ := multivariateGaussian (0 : Euc n) (M k))
      ⟨(measurable_pi_apply k).aemeasurable, s111k_eval_map k⟩
  exact iIndepFun.hasGaussianLaw hk s111k_indep

theorem s111k_obs_gaussian (hM : ∀ k, (M k).PosSemidef) :
    IsGaussian ((s111k_prodLaw M).map (s111k_obs : (Fin 3 → Euc n) → (Fin 2 × Fin n → ℝ))) := by
  have h := (s111k_hasGaussian hM).map_of_measurable (s111k_obs (n := n)) (by fun_prop)
  exact h.isGaussian_map

theorem s111k_obs_centered (hM : ∀ k, (M k).PosSemidef) :
    IsCenteredGaussian ((s111k_prodLaw M).map (s111k_obs : (Fin 3 → Euc n) → (Fin 2 × Fin n → ℝ))) := by
  have := s111k_obs_gaussian hM
  refine ⟨inferInstance, fun L => ?_⟩
  have hint : Integrable (fun z : Fin 2 × Fin n → ℝ => z) ((s111k_prodLaw M).map
      (s111k_obs : (Fin 3 → Euc n) → (Fin 2 × Fin n → ℝ))) := IsGaussian.integrable_id
  have h0 : ∫ z : Fin 2 × Fin n → ℝ, z ∂((s111k_prodLaw M).map
      (s111k_obs : (Fin 3 → Euc n) → (Fin 2 × Fin n → ℝ))) = 0 := by
    ext i
    have h1 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 × Fin n => ℝ) i).integral_comp_comm hint
    simp only [ContinuousLinearMap.proj_apply] at h1
    rw [← h1, integral_map (by fun_prop : Measurable (s111k_obs : (Fin 3 → Euc n) → (Fin 2 × Fin n → ℝ))).aemeasurable
      (continuous_apply i).aestronglyMeasurable]
    simp only [s111k_obs_apply]
    by_cases h : i.1 = 0
    · simp only [h, ite_true]
      rw [integral_add (s111k_memLp_w 0 i.2 |>.integrable one_le_two) (s111k_memLp_w 2 i.2 |>.integrable one_le_two),
        s111k_mean_w, s111k_mean_w]; simp
    · simp only [h, ite_false]
      rw [integral_add (s111k_memLp_w 1 i.2 |>.integrable one_le_two) (s111k_memLp_w 2 i.2 |>.integrable one_le_two),
        s111k_mean_w, s111k_mean_w]; simp
  rw [ContinuousLinearMap.integral_comp_comm L hint, h0]; simp

end Generic

/-- **T04 (finite common-noise coupling).** -/
theorem s111k_finite_common_noise (n : ℕ) (A B S : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hS : S.PosSemidef) :
    let P : Measure (Fin 3 → Euc n) :=
      Measure.pi (fun i : Fin 3 => multivariateGaussian 0 (if i = 0 then A else if i = 1 then B else S))
    let X := fun w : Fin 3 → Euc n => w 0 + w 2
    let Y := fun w : Fin 3 → Euc n => w 1 + w 2
    IsProbabilityMeasure P ∧
      HRS.IsCenteredGaussian (P.map fun w (i : Fin 2 × Fin n) =>
        if i.1 = 0 then X w i.2 else Y w i.2) ∧
      ∀ i j : Fin n,
        (∫ w, X w i * X w j ∂P) = A i j + S i j ∧
        (∫ w, Y w i * Y w j ∂P) = B i j + S i j ∧
        (∫ w, (X w i - Y w i) * (X w j - Y w j) ∂P) = A i j + B i j := by
  intro P X Y
  set M : Fin 3 → Matrix (Fin n) (Fin n) ℝ := fun i => if i = 0 then A else if i = 1 then B else S with hMdef
  have hM : ∀ k, (M k).PosSemidef := by
    intro k; simp only [hMdef]; split_ifs <;> assumption
  have hP : P = s111k_prodLaw M := rfl
  have hM0 : M 0 = A := by simp [hMdef]
  have hM1 : M 1 = B := by simp [hMdef]
  have hM2 : M 2 = S := by simp [hMdef]
  refine ⟨hP ▸ inferInstance, ?_, fun i j => ?_⟩
  · have := s111k_obs_centered hM
    rw [hP]
    convert this using 3
    ext i
    simp [s111k_obs_apply, X, Y]
  · have e1 : ∀ w : Fin 3 → Euc n, X w i * X w j =
        (∑ k, (![1, 0, 1] : Fin 3 → ℝ) k * w k i) * (∑ l, (![1, 0, 1] : Fin 3 → ℝ) l * w l j) := by
      intro w; simp [X, Fin.sum_univ_three]
    have e2 : ∀ w : Fin 3 → Euc n, Y w i * Y w j =
        (∑ k, (![0, 1, 1] : Fin 3 → ℝ) k * w k i) * (∑ l, (![0, 1, 1] : Fin 3 → ℝ) l * w l j) := by
      intro w; simp [Y, Fin.sum_univ_three]
    have e3 : ∀ w : Fin 3 → Euc n, (X w i - Y w i) * (X w j - Y w j) =
        (∑ k, (![1, -1, 0] : Fin 3 → ℝ) k * w k i) * (∑ l, (![1, -1, 0] : Fin 3 → ℝ) l * w l j) := by
      intro w; simp [X, Y, Fin.sum_univ_three]; ring
    refine ⟨?_, ?_, ?_⟩
    · simp_rw [e1]; rw [hP, s111k_combo_moment hM]; simp [Fin.sum_univ_three, hM0, hM2]
    · simp_rw [e2]; rw [hP, s111k_combo_moment hM]; simp [Fin.sum_univ_three, hM1, hM2]
    · simp_rw [e3]; rw [hP, s111k_combo_moment hM]; simp [Fin.sum_univ_three, hM0, hM1]

end HRS.MS.S111K
