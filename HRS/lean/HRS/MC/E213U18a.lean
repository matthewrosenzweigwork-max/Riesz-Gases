import HRS.MC.E213U11j
import HRS.MC.E213U13o

/-!
# Packet e213u18 (part a): `Kwin` evaluated on a product of three linear functionals

`Kwin T a (ℓ₀ ⊗ ℓ₁ ⊗ ℓ₂) = K₀-term - cyc3 Dt + cyc3 Jt` where
`Dt i j k = E[ℓ_i(D_a) ℓ_j(Z_a) ℓ_k(Z_a)]` and `Jt i j k = E[ℓ_k(Z_a) J_a(ℓ_i ⊗ ℓ_j)]`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U18

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

section Alg

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- The product trilinear form `x ↦ ∏ ℓ_i (x_i)`. -/
def trilin (ℓ : Fin 3 → B →L[ℝ] ℝ) : B [×3]→L[ℝ] ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℝ 3 ℝ).compContinuousLinearMap ℓ

theorem trilin_apply (ℓ : Fin 3 → B →L[ℝ] ℝ) (x : Fin 3 → B) :
    trilin ℓ x = ℓ 0 (x 0) * ℓ 1 (x 1) * ℓ 2 (x 2) := by
  simp [trilin, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.ofFn_succ, mul_assoc]

theorem trilin_domDomCongr (ℓ : Fin 3 → B →L[ℝ] ℝ) (σ : Equiv.Perm (Fin 3)) :
    (trilin ℓ).domDomCongr σ = trilin (fun j => ℓ (σ.symm j)) := by
  ext x
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  have h1 : ∀ ℓ' : Fin 3 → B →L[ℝ] ℝ, ∀ y : Fin 3 → B, trilin ℓ' y = ∏ i, ℓ' i (y i) := by
    intro ℓ' y; rw [trilin_apply, Fin.prod_univ_three]
  rw [h1, h1]
  exact Equiv.prod_comp σ (fun j => ℓ (σ.symm j) (x j)) ▸ by
    refine Finset.prod_congr rfl fun i _ => ?_
    simp

/-- The sum over the six permutations. -/
theorem perm3_sum (G : Fin 3 → Fin 3 → Fin 3 → ℝ) :
    ∑ σ : Equiv.Perm (Fin 3), G (σ 0) (σ 1) (σ 2) =
      G 0 1 2 + G 0 2 1 + G 1 0 2 + G 1 2 0 + G 2 0 1 + G 2 1 0 := by
  have : (Finset.univ : Finset (Equiv.Perm (Fin 3))) =
      {1, Equiv.swap 1 2, Equiv.swap 0 1, Equiv.swap 0 2, (Equiv.swap 0 1) * (Equiv.swap 1 2),
        (Equiv.swap 1 2) * (Equiv.swap 0 1)} := by
    decide
  rw [this]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [Equiv.swap_apply_def, Equiv.Perm.mul_apply]
  ring

/-- `trilin` of a permuted triple, as a function of the three entries. -/
theorem trilin_perm_eq (ℓ : Fin 3 → B →L[ℝ] ℝ) (σ : Equiv.Perm (Fin 3)) :
    trilin (fun j => ℓ (σ j)) = trilin ![ℓ (σ 0), ℓ (σ 1), ℓ (σ 2)] := by
  congr 1
  funext j
  fin_cases j <;> rfl

/-- The sum over permutations of `u ((trilin ℓ).domDomCongr σ)`. -/
theorem sum_perm_trilin (u : TensorDual B 3) (ℓ : Fin 3 → B →L[ℝ] ℝ) :
    ∑ σ : Equiv.Perm (Fin 3), u ((trilin ℓ).domDomCongr σ) =
      u (trilin ![ℓ 0, ℓ 1, ℓ 2]) + u (trilin ![ℓ 0, ℓ 2, ℓ 1]) + u (trilin ![ℓ 1, ℓ 0, ℓ 2]) +
      u (trilin ![ℓ 1, ℓ 2, ℓ 0]) + u (trilin ![ℓ 2, ℓ 0, ℓ 1]) + u (trilin ![ℓ 2, ℓ 1, ℓ 0]) := by
  simp_rw [trilin_domDomCongr]
  have key : ∑ σ : Equiv.Perm (Fin 3), u (trilin fun j => ℓ (σ.symm j)) =
      ∑ σ : Equiv.Perm (Fin 3), u (trilin fun j => ℓ (σ j)) :=
    Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin 3))) (fun σ => u (trilin fun j => ℓ (σ j)))
  rw [key]
  simp_rw [trilin_perm_eq]
  exact perm3_sum (fun i j k => u (trilin ![ℓ i, ℓ j, ℓ k]))


/-- The product bilinear form `(x,y) ↦ ℓ₁ x * ℓ₂ y`. -/
def mk2 (l₁ l₂ : B →L[ℝ] ℝ) : B [×2]→L[ℝ] ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap ![l₁, l₂]

theorem mk2_apply (l₁ l₂ : B →L[ℝ] ℝ) (x : Fin 2 → B) : mk2 l₁ l₂ x = l₁ (x 0) * l₂ (x 1) := by
  simp [mk2, Fin.prod_univ_two]

theorem lastSlot_trilin (ℓ : Fin 3 → B →L[ℝ] ℝ) (g : B) :
    HRS.lastSlot (trilin ℓ) g = (ℓ 2 g) • mk2 (ℓ 0) (ℓ 1) := by
  ext x
  simp only [HRS.lastSlot, ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.apply_apply, smul_apply, smul_eq_mul, mk2_apply,
    continuousMultilinearCurryRightEquiv_apply', trilin_apply]
  have h0 : (Fin.snoc x g : Fin 3 → B) 0 = x 0 := rfl
  have h1 : (Fin.snoc x g : Fin 3 → B) 1 = x 1 := rfl
  have h2 : (Fin.snoc x g : Fin 3 → B) 2 = g := rfl
  rw [h0, h1, h2]
  ring

end Alg


section Kw

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

/-- The sum of a triple function over the six orderings. -/
def sum6 (G : Fin 3 → Fin 3 → Fin 3 → ℝ) : ℝ :=
  G 0 1 2 + G 0 2 1 + G 1 0 2 + G 1 2 0 + G 2 0 1 + G 2 1 0

/-- `Kwin` on a product of three linear functionals. -/
theorem kwin_trilin (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (ℓ : Fin 3 → PathSpace d m T →L[ℝ] ℝ)
    (hK0m : AEStronglyMeasurable (ellVec S β₀) S.μ0)
    (hK0i : Integrable (fun x => ‖ellVec S β₀ x‖ * ‖ellVec S β₀ x‖ * ‖ellVec S β₀ x‖) S.μ0) :
    gd.Kwin T a (trilin ℓ) =
      (∫ x, ℓ 0 (Iwin S β₀ hE T a (ellVec S β₀ x)) * ℓ 1 (Iwin S β₀ hE T a (ellVec S β₀ x)) *
          ℓ 2 (Iwin S β₀ hE T a (ellVec S β₀ x)) ∂S.μ0)
      - (1 / 2) * sum6 (fun i j k => ∫ ω, ℓ i (gd.Dwin T a ω) * ℓ j (gd.Zwin T a ω) *
          ℓ k (gd.Zwin T a ω) ∂gd.P₀)
      + (1 / 2) * sum6 (fun i j k => ∫ ω, ℓ k (gd.Zwin T a ω) * gd.Jwin T a ω (mk2 (ℓ i) (ℓ j)) ∂gd.P₀) := by
  obtain ⟨C, hC⟩ := HRS.MC.E213U11.gd_moments_proof gd T hT
  obtain ⟨hJmem, hZm, hDm, hJm, hi3, hi21, -, -⟩ := hC a ha
  have := μ0_isProb S
  have hpush : ∀ ℓ' : Fin 3 → PathSpace d m T →L[ℝ] ℝ,
      pushforward3 (Iwin S β₀ hE T a) (Kinit0 S β₀) (trilin ℓ') =
        ∫ x, ℓ' 0 (Iwin S β₀ hE T a (ellVec S β₀ x)) * ℓ' 1 (Iwin S β₀ hE T a (ellVec S β₀ x)) *
          ℓ' 2 (Iwin S β₀ hE T a (ellVec S β₀ x)) ∂S.μ0 := by
    intro ℓ'
    rw [pushforward3_apply]
    unfold Kinit0
    rw [bochTensor3_apply hK0m hK0m hK0m hK0i]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [trilin_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hbD : ∀ ℓ' : Fin 3 → PathSpace d m T →L[ℝ] ℝ,
      bochTensor3 gd.P₀ (gd.Dwin T a) (gd.Zwin T a) (gd.Zwin T a) (trilin ℓ') =
        ∫ ω, ℓ' 0 (gd.Dwin T a ω) * ℓ' 1 (gd.Zwin T a ω) * ℓ' 2 (gd.Zwin T a ω) ∂gd.P₀ := by
    intro ℓ'
    rw [bochTensor3_apply hDm hZm hZm hi3]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp [trilin_apply]
  have hbJ : ∀ ℓ' : Fin 3 → PathSpace d m T →L[ℝ] ℝ,
      bochTensor21 gd.P₀ (gd.Jwin T a) (gd.Zwin T a) (trilin ℓ') =
        ∫ ω, ℓ' 2 (gd.Zwin T a ω) * gd.Jwin T a ω (mk2 (ℓ' 0) (ℓ' 1)) ∂gd.P₀ := by
    intro ℓ'
    rw [bochTensor21_apply hJm hZm hi21]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    show (gd.Jwin T a ω) (HRS.lastSlot (trilin ℓ') (gd.Zwin T a ω)) = _
    rw [lastSlot_trilin, map_smul, smul_eq_mul]
  unfold GaussData.Kwin
  rw [symm3_apply]
  have hterm : ∀ σ : Equiv.Perm (Fin 3),
      (pushforward3 (Iwin S β₀ hE T a) (Kinit0 S β₀) - (3 : ℝ) • bochTensor3 gd.P₀ (gd.Dwin T a) (gd.Zwin T a) (gd.Zwin T a)
        + (3 : ℝ) • bochTensor21 gd.P₀ (gd.Jwin T a) (gd.Zwin T a)) ((trilin ℓ).domDomCongr σ) =
      pushforward3 (Iwin S β₀ hE T a) (Kinit0 S β₀) ((trilin ℓ).domDomCongr σ)
        - 3 * bochTensor3 gd.P₀ (gd.Dwin T a) (gd.Zwin T a) (gd.Zwin T a) ((trilin ℓ).domDomCongr σ)
        + 3 * bochTensor21 gd.P₀ (gd.Jwin T a) (gd.Zwin T a) ((trilin ℓ).domDomCongr σ) := by
    intro σ
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_perm_trilin, sum_perm_trilin, sum_perm_trilin]
  simp only [hpush, hbD, hbJ, sum6, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  set F : Fin 3 → Torus d → ℝ := fun i x => ℓ i (Iwin S β₀ hE T a (ellVec S β₀ x)) with hF
  have hp : ∀ i j k : Fin 3, (∫ x, ℓ i (Iwin S β₀ hE T a (ellVec S β₀ x)) *
      ℓ j (Iwin S β₀ hE T a (ellVec S β₀ x)) * ℓ k (Iwin S β₀ hE T a (ellVec S β₀ x)) ∂S.μ0) =
      ∫ x, F i x * F j x * F k x ∂S.μ0 := fun _ _ _ => rfl
  have hq : ∀ i j k : Fin 3, (∫ x, F i x * F j x * F k x ∂S.μ0) =
      ∫ x, F 0 x * F 1 x * F 2 x ∂S.μ0 → True := fun _ _ _ _ => trivial
  rw [hp 0 1 2, hp 0 2 1, hp 1 0 2, hp 1 2 0, hp 2 0 1, hp 2 1 0]
  have c1 : (∫ x, F 0 x * F 2 x * F 1 x ∂S.μ0) = ∫ x, F 0 x * F 1 x * F 2 x ∂S.μ0 := by
    congr 1; funext x; ring
  have c2 : (∫ x, F 1 x * F 0 x * F 2 x ∂S.μ0) = ∫ x, F 0 x * F 1 x * F 2 x ∂S.μ0 := by
    congr 1; funext x; ring
  have c3 : (∫ x, F 1 x * F 2 x * F 0 x ∂S.μ0) = ∫ x, F 0 x * F 1 x * F 2 x ∂S.μ0 := by
    congr 1; funext x; ring
  have c4 : (∫ x, F 2 x * F 0 x * F 1 x ∂S.μ0) = ∫ x, F 0 x * F 1 x * F 2 x ∂S.μ0 := by
    congr 1; funext x; ring
  have c5 : (∫ x, F 2 x * F 1 x * F 0 x ∂S.μ0) = ∫ x, F 0 x * F 1 x * F 2 x ∂S.μ0 := by
    congr 1; funext x; ring
  rw [c1, c2, c3, c4, c5]
  ring

end Kw

end HRS.MC.E213U18

end
