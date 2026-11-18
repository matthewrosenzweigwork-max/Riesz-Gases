import HRS.MC.E213U11i
import HRS.MC.E213U1a

/-!
# Packet e213u11, file j: the relocated statements `gd_moments`, `Kwin_mem`, `Kproj_bounded`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U11

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

/-- Young: `x y² ≤ (x³ + 2y³)/3`. -/
theorem u11_young3 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (x y : Ω → ℝ)
    (hx0 : ∀ ω, 0 ≤ x ω) (hy0 : ∀ ω, 0 ≤ y ω) (hxm : AEStronglyMeasurable x P) (hym : AEStronglyMeasurable y P)
    (hxi : Integrable (fun ω => x ω ^ 3) P) (hyi : Integrable (fun ω => y ω ^ 3) P) (Cx Cy : ℝ)
    (hxb : ∫ ω, x ω ^ 3 ∂P ≤ Cx) (hyb : ∫ ω, y ω ^ 3 ∂P ≤ Cy) :
    Integrable (fun ω => x ω * y ω * y ω) P ∧ ∫ ω, x ω * y ω * y ω ∂P ≤ (Cx + 2 * Cy) / 3 := by
  have hpt : ∀ ω, x ω * y ω * y ω ≤ (x ω ^ 3 + 2 * y ω ^ 3) / 3 := fun ω => by
    nlinarith [mul_nonneg (add_nonneg (hx0 ω) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hy0 ω)))
      (sq_nonneg (x ω - y ω))]
  have hIr : Integrable (fun ω => (x ω ^ 3 + 2 * y ω ^ 3) / 3) P :=
    (hxi.add (hyi.const_mul 2)).div_const 3
  refine ⟨hIr.mono' ((hxm.mul hym).mul hym) (Eventually.of_forall fun ω => ?_), ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hx0 ω) (hy0 ω)) (hy0 ω))]
    exact hpt ω
  · refine (integral_mono_of_nonneg (Eventually.of_forall fun ω =>
      mul_nonneg (mul_nonneg (hx0 ω) (hy0 ω)) (hy0 ω)) hIr (Eventually.of_forall hpt)).trans ?_
    rw [integral_div, integral_add hxi (hyi.const_mul 2), integral_const_mul]
    linarith

/-- Young: `x y ≤ (x² + y²)/2`. -/
theorem u11_young2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (x y : Ω → ℝ)
    (hx0 : ∀ ω, 0 ≤ x ω) (hy0 : ∀ ω, 0 ≤ y ω) (hxm : AEStronglyMeasurable x P) (hym : AEStronglyMeasurable y P)
    (hxi : Integrable (fun ω => x ω ^ 2) P) (hyi : Integrable (fun ω => y ω ^ 2) P) (Cx Cy : ℝ)
    (hxb : ∫ ω, x ω ^ 2 ∂P ≤ Cx) (hyb : ∫ ω, y ω ^ 2 ∂P ≤ Cy) :
    Integrable (fun ω => x ω * y ω) P ∧ ∫ ω, x ω * y ω ∂P ≤ (Cx + Cy) / 2 := by
  have hpt : ∀ ω, x ω * y ω ≤ (x ω ^ 2 + y ω ^ 2) / 2 := fun ω => by
    nlinarith [sq_nonneg (x ω - y ω)]
  have hIr : Integrable (fun ω => (x ω ^ 2 + y ω ^ 2) / 2) P := (hxi.add hyi).div_const 2
  refine ⟨hIr.mono' (hxm.mul hym) (Eventually.of_forall fun ω => ?_), ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hx0 ω) (hy0 ω))]
    exact hpt ω
  · refine (integral_mono_of_nonneg (Eventually.of_forall fun ω =>
      mul_nonneg (hx0 ω) (hy0 ω)) hIr (Eventually.of_forall hpt)).trans ?_
    rw [integral_div, integral_add hxi hyi]
    linarith

theorem u11_norm_symm3_apply_le {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] (u : TensorDual B 3) :
    ‖symm3 B u‖ ≤ ‖u‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg u) fun M => ?_
  rw [symm3_apply]
  have h : ∀ σ : Equiv.Perm (Fin 3), ‖u (M.domDomCongr σ)‖ ≤ ‖u‖ * ‖M‖ := fun σ => by
    have h1 := norm_permForms_apply σ M
    rw [permForms_apply] at h1
    have h2 := u.le_opNorm (M.domDomCongr σ)
    rwa [h1] at h2
  have hc : (Fintype.card (Equiv.Perm (Fin 3)) : ℝ) = 6 := by
    rw [Fintype.card_perm]; simp [Nat.factorial]
  calc ‖(1 / 6 : ℝ) * ∑ σ : Equiv.Perm (Fin 3), u (M.domDomCongr σ)‖
      = (1 / 6 : ℝ) * ‖∑ σ : Equiv.Perm (Fin 3), u (M.domDomCongr σ)‖ := by
        rw [norm_mul]; simp
    _ ≤ (1 / 6 : ℝ) * ∑ σ : Equiv.Perm (Fin 3), ‖u (M.domDomCongr σ)‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num)
    _ ≤ (1 / 6 : ℝ) * ∑ σ : Equiv.Perm (Fin 3), ‖u‖ * ‖M‖ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => h σ) (by norm_num)
    _ = ‖u‖ * ‖M‖ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]; ring

theorem u11_norm_pushforward3_apply_le {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (I : E →L[ℝ] B) (u : TensorDual E 3) :
    ‖pushforward3 I u‖ ≤ ‖I‖ ^ 3 * ‖u‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun M => ?_
  show ‖u (compForms I M)‖ ≤ ‖I‖ ^ 3 * ‖u‖ * ‖M‖
  calc ‖u (compForms I M)‖ ≤ ‖u‖ * ‖compForms I M‖ := u.le_opNorm _
    _ ≤ ‖u‖ * (‖I‖ ^ 3 * ‖M‖) := by
        gcongr; exact ((compForms I).le_opNorm M).trans (by gcongr; exact norm_compForms_le I)
    _ = ‖I‖ ^ 3 * ‖u‖ * ‖M‖ := by ring

section Final

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

theorem gd_moments_proof (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, ∀ a : ℝ, 0 ≤ a →
      (∀ᵐ ω ∂gd.P₀, gd.Jwin T a ω ∈ projTensor (PathSpace d m T) 2) ∧
      AEStronglyMeasurable (gd.Zwin T a) gd.P₀ ∧ AEStronglyMeasurable (gd.Dwin T a) gd.P₀ ∧
      AEStronglyMeasurable (gd.Jwin T a) gd.P₀ ∧
      Integrable (fun ω => ‖gd.Dwin T a ω‖ * ‖gd.Zwin T a ω‖ * ‖gd.Zwin T a ω‖) gd.P₀ ∧
      Integrable (fun ω => ‖gd.Jwin T a ω‖ * ‖gd.Zwin T a ω‖) gd.P₀ ∧
      (∫ ω, ‖gd.Dwin T a ω‖ * ‖gd.Zwin T a ω‖ * ‖gd.Zwin T a ω‖ ∂gd.P₀) ≤ C ∧
      (∫ ω, ‖gd.Jwin T a ω‖ * ‖gd.Zwin T a ω‖ ∂gd.P₀) ≤ C := by
  obtain ⟨CD, hCD0, hCD⟩ := u11_D_moment3 hE gd T hT
  obtain ⟨CJ, hCJ0, hCJ⟩ := u11_J_moment2 hE gd T hT
  obtain ⟨CZ3, hCZ30, hCZ3⟩ := u11_Z_moment gd T hT 3 (by norm_num)
  obtain ⟨CZ2, hCZ20, hCZ2⟩ := u11_Z_moment gd T hT 2 (by norm_num)
  refine ⟨(CD + 2 * CZ3) / 3 + (CJ + CZ2) / 2, fun a ha => ?_⟩
  obtain ⟨hZm, hZ3i, hZ3b⟩ := hCZ3 a ha
  obtain ⟨-, hZ2i, hZ2b⟩ := hCZ2 a ha
  obtain ⟨hD3i, hD3b⟩ := hCD a ha
  obtain ⟨hJ2i, hJ2b⟩ := hCJ a ha
  obtain ⟨hJm, hJmem⟩ := u11_Jwin_aesm_mem gd T hT a ha
  have hDm := u11_Dwin_aesm gd T hT a ha
  have hJn : AEStronglyMeasurable (fun ω => ‖gd.Jwin T a ω‖) gd.P₀ :=
    (continuous_norm (E := TensorDual (PathSpace d m T) 2)).comp_aestronglyMeasurable hJm
  have hZ3i' : Integrable (fun ω => ‖gd.Zwin T a ω‖ ^ 3) gd.P₀ := by simpa [Real.rpow_ofNat] using hZ3i
  have hZ3b' : ∫ ω, ‖gd.Zwin T a ω‖ ^ 3 ∂gd.P₀ ≤ CZ3 := by simpa [Real.rpow_ofNat] using hZ3b
  have hZ2i' : Integrable (fun ω => ‖gd.Zwin T a ω‖ ^ 2) gd.P₀ := by simpa [Real.rpow_ofNat] using hZ2i
  have hZ2b' : ∫ ω, ‖gd.Zwin T a ω‖ ^ 2 ∂gd.P₀ ≤ CZ2 := by simpa [Real.rpow_ofNat] using hZ2b
  obtain ⟨y1, y2⟩ := u11_young3 (P := gd.P₀) (fun ω => ‖gd.Dwin T a ω‖) (fun ω => ‖gd.Zwin T a ω‖)
    (fun ω => norm_nonneg _) (fun ω => norm_nonneg _) hDm.norm hZm.norm hD3i hZ3i' CD CZ3 hD3b hZ3b'
  obtain ⟨z1, z2⟩ := u11_young2 (P := gd.P₀) (fun ω => ‖gd.Jwin T a ω‖) (fun ω => ‖gd.Zwin T a ω‖)
    (fun ω => norm_nonneg (gd.Jwin T a ω)) (fun ω => norm_nonneg _) hJn hZm.norm hJ2i hZ2i' CJ CZ2 hJ2b hZ2b'
  have p1 : 0 ≤ (CD + 2 * CZ3) / 3 := by positivity
  have p2 : 0 ≤ (CJ + CZ2) / 2 := by positivity
  refine ⟨hJmem, hZm, hDm, hJm, y1, z1, ?_, ?_⟩
  · linarith
  · linarith

theorem Kwin_mem_proof (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) :
    gd.Kwin T a ∈ projTensor (PathSpace d m T) 3 := by
  obtain ⟨C, hC⟩ := gd_moments_proof gd T hT
  obtain ⟨hJmem, hZm, hDm, hJm, hi3, hi21, -, -⟩ := hC a ha
  unfold GaussData.Kwin
  have h1 : pushforward3 (Iwin S β₀ hE T a) (Kinit0 S β₀) ∈ projTensor (PathSpace d m T) 3 :=
    pushforward3_mem _ (HRS.MC.E213U1.Kinit0_mem_proof S β₀)
  have h2 : (-3 : ℝ) • bochTensor3 gd.P₀ (gd.Dwin T a) (gd.Zwin T a) (gd.Zwin T a) ∈
      projTensor (PathSpace d m T) 3 :=
    (projTensor (PathSpace d m T) 3).smul_mem _ (bochTensor3_mem hDm hZm hZm hi3)
  have h3 : (3 : ℝ) • bochTensor21 gd.P₀ (gd.Jwin T a) (gd.Zwin T a) ∈ projTensor (PathSpace d m T) 3 :=
    (projTensor (PathSpace d m T) 3).smul_mem _ (bochTensor21_mem hJm hZm hi21 hJmem)
  have h123 := (projTensor (PathSpace d m T) 3).add_mem ((projTensor (PathSpace d m T) 3).add_mem h1 h2) h3
  have heq : pushforward3 (Iwin S β₀ hE T a) (Kinit0 S β₀) -
      (3 : ℝ) • bochTensor3 gd.P₀ (gd.Dwin T a) (gd.Zwin T a) (gd.Zwin T a) +
      (3 : ℝ) • bochTensor21 gd.P₀ (gd.Jwin T a) (gd.Zwin T a) =
      pushforward3 (Iwin S β₀ hE T a) (Kinit0 S β₀) +
      (-3 : ℝ) • bochTensor3 gd.P₀ (gd.Dwin T a) (gd.Zwin T a) (gd.Zwin T a) +
      (3 : ℝ) • bochTensor21 gd.P₀ (gd.Jwin T a) (gd.Zwin T a) := by
    ext M
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    ring
  rw [heq]
  exact symm3_mem h123

theorem Kproj_bounded_proof (T : ℝ) (hT : 0 < T) : ∃ C : ℝ, ∀ a : ℝ, 0 ≤ a → ‖gd.Kproj T a‖ ≤ C := by
  classical
  obtain ⟨C, hC⟩ := gd_moments_proof gd T hT
  obtain ⟨CI, c, hCI, hc, hI⟩ := Classical.choose_spec (exists_Iwin S β₀ hE T)
  refine ⟨CI ^ 3 * ‖Kinit0 S β₀‖ + 3 * C + 3 * C, fun a ha => ?_⟩
  have hval : ((gd.Kproj T a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3) =
      gd.Kwin T a := by
    unfold GaussData.Kproj
    rw [max_eq_left ha, dif_pos (Kwin_mem_proof gd T hT a ha)]
  have hnorm : ‖gd.Kproj T a‖ = ‖gd.Kwin T a‖ := by rw [← hval]; rfl
  rw [hnorm]
  obtain ⟨-, hZm, hDm, hJm, hi3, hi21, hb3, hb21⟩ := hC a ha
  set X1 : TensorDual (PathSpace d m T) 3 := pushforward3 (Iwin S β₀ hE T a) (Kinit0 S β₀) with hX1
  set X2 : TensorDual (PathSpace d m T) 3 :=
    bochTensor3 gd.P₀ (gd.Dwin T a) (gd.Zwin T a) (gd.Zwin T a) with hX2
  set X3 : TensorDual (PathSpace d m T) 3 := bochTensor21 gd.P₀ (gd.Jwin T a) (gd.Zwin T a) with hX3
  have hn2 : ‖X2‖ ≤ C := (norm_bochTensor3_le hDm hZm hZm hi3).trans hb3
  have hn3 : ‖X3‖ ≤ C := (norm_bochTensor21_le hJm hZm hi21).trans hb21
  have hIa : ‖Iwin S β₀ hE T a‖ ≤ CI := by
    have h1 : ‖Iwin S β₀ hE T a‖ ≤ CI * Real.exp (-c * a) := (hI a ha).2
    refine h1.trans ?_
    have : Real.exp (-c * a) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    nlinarith
  have hn1 : ‖X1‖ ≤ CI ^ 3 * ‖Kinit0 S β₀‖ := by
    refine (u11_norm_pushforward3_apply_le (Iwin S β₀ hE T a) (Kinit0 S β₀)).trans ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hIa 3) (norm_nonneg (Kinit0 S β₀))
  unfold GaussData.Kwin
  refine (u11_norm_symm3_apply_le _).trans ?_
  have hsum : ‖X1 - (3 : ℝ) • X2 + (3 : ℝ) • X3‖ ≤ CI ^ 3 * ‖Kinit0 S β₀‖ + 3 * C + 3 * C := by
    refine (norm_add_le (X1 - (3 : ℝ) • X2) ((3 : ℝ) • X3)).trans
      (add_le_add ((norm_sub_le X1 ((3 : ℝ) • X2)).trans (add_le_add hn1 ?_)) ?_)
    · refine (ContinuousLinearMap.opNorm_smul_le (3 : ℝ) X2).trans ?_
      rw [Real.norm_of_nonneg (by norm_num)]
      exact mul_le_mul_of_nonneg_left hn2 (by norm_num)
    · refine (ContinuousLinearMap.opNorm_smul_le (3 : ℝ) X3).trans ?_
      rw [Real.norm_of_nonneg (by norm_num)]
      exact mul_le_mul_of_nonneg_left hn3 (by norm_num)
  exact hsum

end Final

end HRS.MC.E213U11

end
