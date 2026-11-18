import HRS.MS.Fp81S21RecentRS3
import HRS.MS.Fp81S21BV05

/-! Riemann–Stieltjes functionals on anchored BV paths. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Set
open scoped ENNReal
namespace HRS.Fp81.S21

/-- Existence and variation-norm control for one continuous operator path. -/
theorem fp81s21_recentRS_bv_exists_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (H : ℝ) (hH : 0 < H)
    (B : C(Icc (0 : ℝ) H, E →L[ℝ] ℝ))
    (v : fp81s21_BV0 (E := E) hH.le) :
    ∃ I : ℝ, fp81s21_IsRSOn 0 H
      (fun τ u w => B (Set.projIcc 0 H hH.le τ)
        (fp81s21_bvExt hH.le v w - fp81s21_bvExt hH.le v u)) I ∧
      |I| ≤ ‖B‖ * ‖v‖ := by
  let G : ℝ → E →L[ℝ] ℝ := fun τ => B (Set.projIcc 0 H hH.le τ)
  have hG : ContinuousOn G (Icc 0 H) :=
    (B.continuous.comp continuous_projIcc).continuousOn
  obtain ⟨I, hI, hbound⟩ := fp81s21_rsOn_bv hH (fp81s21_bvExt hH.le v) G
    (fp81s21_bvExt_bv hH.le v) hG
  refine ⟨I, hI, ?_⟩
  have hsup : (⨆ τ : Icc (0 : ℝ) H, ‖G τ‖) ≤ ‖B‖ := by
    letI : Nonempty (Icc (0 : ℝ) H) := ⟨⟨0, ⟨le_rfl, hH.le⟩⟩⟩
    apply ciSup_le
    intro τ
    exact ContinuousMap.norm_coe_le_norm B _
  calc
    |I| ≤ (⨆ τ : Icc (0 : ℝ) H, ‖G τ‖) *
        (eVariationOn (fp81s21_bvExt hH.le v) (Icc 0 H)).toReal := hbound
    _ ≤ ‖B‖ * ‖v‖ := by
      rw [fp81s21_bv_norm_eq]
      exact mul_le_mul_of_nonneg_right hsup ENNReal.toReal_nonneg

private theorem fp81s21_recentRS_add {T I J : ℝ}
    {S R : ℝ → ℝ → ℝ → ℝ}
    (hS : HRS.Sec7.IsRS T S I) (hR : HRS.Sec7.IsRS T R J) :
    HRS.Sec7.IsRS T (fun τ u w => S τ u w + R τ u w) (I + J) := by
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := hS (ε / 2) (by linarith)
  obtain ⟨δ₂, hδ₂, h₂⟩ := hR (ε / 2) (by linarith)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun n u τ hu hu0 huT htag hmesh => ?_⟩
  have e₁ := h₁ n u τ hu hu0 huT htag (fun i => lt_of_lt_of_le (hmesh i) (min_le_left _ _))
  have e₂ := h₂ n u τ hu hu0 huT htag (fun i => lt_of_lt_of_le (hmesh i) (min_le_right _ _))
  rw [Finset.sum_add_distrib]
  calc
    |(∑ i : Fin n, S (τ i) (u i.castSucc) (u i.succ)) +
        (∑ i : Fin n, R (τ i) (u i.castSucc) (u i.succ)) - (I + J)| =
      |((∑ i : Fin n, S (τ i) (u i.castSucc) (u i.succ)) - I) +
       ((∑ i : Fin n, R (τ i) (u i.castSucc) (u i.succ)) - J)| := by ring_nf
    _ ≤ |(∑ i : Fin n, S (τ i) (u i.castSucc) (u i.succ)) - I| +
        |(∑ i : Fin n, R (τ i) (u i.castSucc) (u i.succ)) - J| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add e₁ e₂
    _ = ε := by ring

private theorem fp81s21_recentRS_mul {T I : ℝ}
    {S : ℝ → ℝ → ℝ → ℝ} (hS : HRS.Sec7.IsRS T S I) (c : ℝ) :
    HRS.Sec7.IsRS T (fun τ u w => c * S τ u w) (c * I) := by
  intro ε hε
  have hp : 0 < |c| + 1 := by positivity
  obtain ⟨δ, hδ, hs⟩ := hS (ε / (|c| + 1)) (div_pos hε hp)
  refine ⟨δ, hδ, fun n u τ hu hu0 huT htag hmesh => ?_⟩
  have he := hs n u τ hu hu0 huT htag hmesh
  have hm : (|c| + 1) *
      |(∑ i : Fin n, S (τ i) (u i.castSucc) (u i.succ)) - I| < ε := by
    calc
      _ < (|c| + 1) * (ε / (|c| + 1)) := mul_lt_mul_of_pos_left he hp
      _ = ε := by field_simp
  rw [← Finset.mul_sum, ← mul_sub, abs_mul]
  nlinarith [abs_nonneg c,
    abs_nonneg ((∑ i : Fin n, S (τ i) (u i.castSucc) (u i.succ)) - I)]

private def fp81s21_recentRS_value
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (H : ℝ) (hH : 0 < H) (B : C(Icc (0 : ℝ) H, E →L[ℝ] ℝ))
    (v : fp81s21_BV0 (E := E) hH.le) : ℝ :=
  Classical.choose (fp81s21_recentRS_bv_exists_bound H hH B v)

private theorem fp81s21_recentRS_value_spec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (H : ℝ) (hH : 0 < H) (B : C(Icc (0 : ℝ) H, E →L[ℝ] ℝ))
    (v : fp81s21_BV0 (E := E) hH.le) :
    fp81s21_IsRSOn 0 H
      (fun τ u w => B (Set.projIcc 0 H hH.le τ)
        (fp81s21_bvExt hH.le v w - fp81s21_bvExt hH.le v u))
      (fp81s21_recentRS_value H hH B v) ∧
    |fp81s21_recentRS_value H hH B v| ≤ ‖B‖ * ‖v‖ :=
  Classical.choose_spec (fp81s21_recentRS_bv_exists_bound H hH B v)

private theorem fp81s21_recentRS_value_spec_RS
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (H : ℝ) (hH : 0 < H) (B : C(Icc (0 : ℝ) H, E →L[ℝ] ℝ))
    (v : fp81s21_BV0 (E := E) hH.le) :
    HRS.Sec7.IsRS H
      (fun τ u w => B (projIcc 0 H hH.le τ)
        (fp81s21_bvExt hH.le v w - fp81s21_bvExt hH.le v u))
      (fp81s21_recentRS_value H hH B v) := by
  apply (HRS.MS.R2Interp.s102_isR2RS_iff _ _ _).1
  simpa only [fp81s21_IsRSOn, zero_add, sub_zero] using
    (fp81s21_recentRS_value_spec H hH B v).1

private theorem fp81s21_recentRS_value_add_bv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (H : ℝ) (hH : 0 < H) (B : C(Icc (0 : ℝ) H, E →L[ℝ] ℝ))
    (v w : fp81s21_BV0 (E := E) hH.le) :
    fp81s21_recentRS_value H hH B (v + w) =
      fp81s21_recentRS_value H hH B v + fp81s21_recentRS_value H hH B w := by
  have hs := fp81s21_recentRS_add (fp81s21_recentRS_value_spec_RS H hH B v)
    (fp81s21_recentRS_value_spec_RS H hH B w)
  have hs' : fp81s21_IsRSOn 0 H
      (fun τ u z => B (projIcc 0 H hH.le τ)
        (fp81s21_bvExt hH.le (v + w) z - fp81s21_bvExt hH.le (v + w) u))
      (fp81s21_recentRS_value H hH B v + fp81s21_recentRS_value H hH B w) := by
    simp only [fp81s21_IsRSOn, zero_add, sub_zero]
    apply fp81s21_IsR2RS_congr (S := _) _
      ((HRS.MS.R2Interp.s102_isR2RS_iff _ _ _).2 hs)
    intro τ u z
    simp only [zero_add, fp81s21_bvExt_add, Pi.add_apply]
    rw [show fp81s21_bvExt hH.le v z + fp81s21_bvExt hH.le w z -
        (fp81s21_bvExt hH.le v u + fp81s21_bvExt hH.le w u) =
        (fp81s21_bvExt hH.le v z - fp81s21_bvExt hH.le v u) +
        (fp81s21_bvExt hH.le w z - fp81s21_bvExt hH.le w u) by abel]
    simp
  exact fp81s21_isRSOn_unique hH (fp81s21_recentRS_value_spec H hH B (v + w)).1 hs'

private theorem fp81s21_recentRS_value_smul_bv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (H : ℝ) (hH : 0 < H) (B : C(Icc (0 : ℝ) H, E →L[ℝ] ℝ))
    (c : ℝ) (v : fp81s21_BV0 (E := E) hH.le) :
    fp81s21_recentRS_value H hH B (c • v) = c * fp81s21_recentRS_value H hH B v := by
  have hs := fp81s21_recentRS_mul (fp81s21_recentRS_value_spec_RS H hH B v) c
  have hs' : fp81s21_IsRSOn 0 H
      (fun τ u z => B (projIcc 0 H hH.le τ)
        (fp81s21_bvExt hH.le (c • v) z - fp81s21_bvExt hH.le (c • v) u))
      (c * fp81s21_recentRS_value H hH B v) := by
    simp only [fp81s21_IsRSOn, zero_add, sub_zero]
    apply fp81s21_IsR2RS_congr (S := _) _
      ((HRS.MS.R2Interp.s102_isR2RS_iff _ _ _).2 hs)
    intro τ u z
    simp only [zero_add, fp81s21_bvExt_smul, Pi.smul_apply, ← smul_sub, map_smul,
      smul_eq_mul]
  exact fp81s21_isRSOn_unique hH (fp81s21_recentRS_value_spec H hH B (c • v)).1 hs'

private theorem fp81s21_recentRS_value_add_op
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (H : ℝ) (hH : 0 < H) (B D : C(Icc (0 : ℝ) H, E →L[ℝ] ℝ))
    (v : fp81s21_BV0 (E := E) hH.le) :
    fp81s21_recentRS_value H hH (B + D) v =
      fp81s21_recentRS_value H hH B v + fp81s21_recentRS_value H hH D v := by
  have hs := fp81s21_recentRS_add (fp81s21_recentRS_value_spec_RS H hH B v)
    (fp81s21_recentRS_value_spec_RS H hH D v)
  have hs' : fp81s21_IsRSOn 0 H
      (fun τ u z => (B + D) (projIcc 0 H hH.le τ)
        (fp81s21_bvExt hH.le v z - fp81s21_bvExt hH.le v u))
      (fp81s21_recentRS_value H hH B v + fp81s21_recentRS_value H hH D v) := by
    simp only [fp81s21_IsRSOn, zero_add, sub_zero]
    apply fp81s21_IsR2RS_congr (S := _) _
      ((HRS.MS.R2Interp.s102_isR2RS_iff _ _ _).2 hs)
    intro τ u z
    simp
  exact fp81s21_isRSOn_unique hH (fp81s21_recentRS_value_spec H hH (B + D) v).1 hs'

private def fp81s21_recentRS_operator
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (H : ℝ) (hH : 0 < H) (B : C(Icc (0 : ℝ) H, E →L[ℝ] ℝ)) :
    fp81s21_BV0 (E := E) hH.le →L[ℝ] ℝ := by
  let L : fp81s21_BV0 (E := E) hH.le →ₗ[ℝ] ℝ :=
    { toFun := fp81s21_recentRS_value H hH B
      map_add' := fp81s21_recentRS_value_add_bv H hH B
      map_smul' := by
        intro c v
        simpa only [RingHom.id_apply, smul_eq_mul] using
          fp81s21_recentRS_value_smul_bv H hH B c v }
  exact L.mkContinuous ‖B‖ (by
    intro v
    change ‖fp81s21_recentRS_value H hH B v‖ ≤ ‖B‖ * ‖v‖
    rw [Real.norm_eq_abs]
    exact (fp81s21_recentRS_value_spec H hH B v).2)

private theorem fp81s21_recentRS_operator_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (H : ℝ) (hH : 0 < H) (B : C(Icc (0 : ℝ) H, E →L[ℝ] ℝ)) :
    ‖fp81s21_recentRS_operator H hH B‖ ≤ ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
  intro v
  change ‖fp81s21_recentRS_value H hH B v‖ ≤ ‖B‖ * ‖v‖
  rw [Real.norm_eq_abs]
  exact (fp81s21_recentRS_value_spec H hH B v).2

private theorem fp81s21_recentRS_operator_sub_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (H : ℝ) (hH : 0 < H) (B D : C(Icc (0 : ℝ) H, E →L[ℝ] ℝ))
    (v : fp81s21_BV0 (E := E) hH.le) :
    ‖(fp81s21_recentRS_operator H hH B - fp81s21_recentRS_operator H hH D) v‖ ≤
      ‖B - D‖ * ‖v‖ := by
  have hadd := fp81s21_recentRS_value_add_op H hH (B - D) D v
  rw [sub_add_cancel] at hadd
  have heq : fp81s21_recentRS_value H hH B v - fp81s21_recentRS_value H hH D v =
      fp81s21_recentRS_value H hH (B - D) v := by linarith
  change |fp81s21_recentRS_value H hH B v - fp81s21_recentRS_value H hH D v| ≤ _
  rw [heq]
  exact (fp81s21_recentRS_value_spec H hH (B - D) v).2

/-- Construct the uniformly bounded, Lipschitz family of RS functionals. -/
theorem fp81s21_recentRSKernel_of_continuous_operators
    {C E : Type*}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (H K : ℝ) (hH : 0 < H) (hK : 0 ≤ K)
    (A : C → ContinuousMap (Icc (0 : ℝ) H) (E →L[ℝ] ℝ))
    (hbound : ∀ y, ‖A y‖ ≤ K)
    (hlip : ∀ y y', ‖A y - A y'‖ ≤ K * ‖y - y'‖) :
    ∃ F : fp81s21_RecentRSKernel C
        (fp81s21_BV0 (E := E) hH.le) (K + 1),
      ∀ y v, fp81s21_IsRSOn 0 H
        (fun τ u w =>
          A y (Set.projIcc 0 H hH.le τ)
            (fp81s21_bvExt hH.le v w -
             fp81s21_bvExt hH.le v u))
        (F.kernel y v) := by
  let F : fp81s21_RecentRSKernel C (fp81s21_BV0 (E := E) hH.le) (K + 1) :=
    { kernel := fun y => fp81s21_recentRS_operator H hH (A y)
      bound := by
        intro y
        exact (fp81s21_recentRS_operator_bound H hH (A y)).trans (by linarith [hbound y])
      lipschitz := by
        intro y y'
        have hk : ‖fp81s21_recentRS_operator H hH (A y) -
            fp81s21_recentRS_operator H hH (A y')‖ ≤ K * ‖y - y'‖ := by
          apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK (norm_nonneg _))
          intro v
          exact (fp81s21_recentRS_operator_sub_bound H hH (A y) (A y') v).trans
            (mul_le_mul_of_nonneg_right (hlip y y') (norm_nonneg v))
        exact hk.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)) }
  refine ⟨F, ?_⟩
  intro y v
  exact (fp81s21_recentRS_value_spec H hH (A y) v).1

#print axioms fp81s21_recentRS_bv_exists_bound
#print axioms fp81s21_recentRSKernel_of_continuous_operators
end HRS.Fp81.S21
end
