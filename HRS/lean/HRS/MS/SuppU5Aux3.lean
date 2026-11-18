import Mathlib
import HRS.MS.SuppU5Aux2

/-!
# Packet U5 (aux 3): the finite-dimensional coupling core
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace Matrix

noncomputable section

namespace HRS.U5

lemma u5_proj_le {k : ℕ} (V : Submodule ℝ (Ek k)) (y w : Ek k) (hw : w ∈ V) :
    ‖y - V.starProjection y‖ ≤ ‖y - w‖ := by
  rw [Submodule.starProjection_minimal]
  exact ciInf_le (⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩ : BddBelow (Set.range fun x : V => ‖y - x‖))
    ⟨w, hw⟩

/-- The quadratic form of the second-moment matrix. -/
lemma u5_dot_moment {k : ℕ} (ρ : Measure (Ek k)) [IsProbabilityMeasure ρ]
    (h2 : Integrable (fun y : Ek k => ‖y‖ ^ 2) ρ) (x y : Ek k) :
    x ⬝ᵥ (Yurinskii.momentMatrix ρ *ᵥ y) = ∫ z, (inner ℝ x z) * (inner ℝ y z) ∂ρ := by
  have hI := Yurinskii.integrable_coord_mul h2
  have e : ∀ z : Ek k, (inner ℝ x z) * (inner ℝ y z) = ∑ a, ∑ b, (x a * y b) * (z a * z b) := fun z => by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hI a b).const_mul _]
  simp only [dotProduct, Matrix.mulVec, Yurinskii.momentMatrix, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => (hI a b).const_mul _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul]; ring


lemma u5_integral_apply_clm {k k' : ℕ} (ρ : Measure (Ek k)) (h2 : Integrable (fun y : Ek k => ‖y‖) ρ)
    (L : Ek k →L[ℝ] Ek k') (c : Fin k') :
    ∫ y, (L y) c ∂ρ = (L (∫ y, y ∂ρ)) c := by
  have hid : Integrable (fun y : Ek k => y) ρ := (integrable_norm_iff aestronglyMeasurable_id).1 h2
  have h := ContinuousLinearMap.integral_comp_comm ((EuclideanSpace.proj c : Ek k' →L[ℝ] ℝ).comp L) hid
  simpa using h

lemma u5_vec_mean_zero {k : ℕ} (ρ : Measure (Ek k)) [IsProbabilityMeasure ρ] {b : ℝ}
    (hb : ∀ᵐ y ∂ρ, ‖y‖ ≤ b) (h0 : ∀ c, ∫ y, y c ∂ρ = 0) : ∫ y, y ∂ρ = 0 := by
  have hi : Integrable (fun y : Ek k => ‖y‖) ρ := Integrable.of_bound (f := fun y : Ek k => ‖y‖) measurable_norm.aestronglyMeasurable b
    (hb.mono fun y hy => by simpa using hy)
  ext c
  have := u5_integral_apply_clm ρ hi (ContinuousLinearMap.id ℝ (Ek k)) c
  simpa [h0 c] using this.symm

lemma u5_core_lind {k r N : ℕ} (hN : 1 ≤ N) (ρ : Measure (Ek k)) [IsProbabilityMeasure ρ] {b : ℝ}
    (hρb : ∀ᵐ y ∂ρ, ‖y‖ ≤ b) (h0 : ∀ c, ∫ y, y c ∂ρ = 0) (τ : Ek k →L[ℝ] Ek r)
    (hτ : ∀ z, ‖τ z‖ ≤ ‖z‖) {ε : ℝ} (hε : 0 < ε) :
    wassersteinE 1 ((Measure.pi fun _ : Fin N => ρ).map
        (fun ω => τ ((Real.sqrt N)⁻¹ • ∑ i, ω i)))
      ((multivariateGaussian (0 : Ek k) (Yurinskii.momentMatrix ρ)).map τ) ≤
    ENNReal.ofReal (2 * ε * Real.sqrt r + 2 / ε ^ 2 *
      ((2 + Yurinskii.c4 / 2) * (b ^ 3 / Real.sqrt N))) := by
  set s : ℝ := (Real.sqrt N)⁻¹ with hs
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hs0 : 0 ≤ s := inv_nonneg.2 hsqrt.le
  have hb0 : 0 ≤ b := by
    obtain ⟨y0, hy0⟩ := hρb.exists
    exact (norm_nonneg _).trans hy0
  set g : Ek k → Ek r := fun y => s • τ y with hg
  have hgm : Measurable g := (τ.continuous.measurable).const_smul s
  have hgb : ∀ᵐ y ∂ρ, ‖g y‖ ≤ s * b := hρb.mono fun y hy => by
    rw [hg, norm_smul, Real.norm_of_nonneg hs0]
    exact mul_le_mul_of_nonneg_left ((hτ y).trans hy) hs0
  set ρ' : Measure (Ek r) := ρ.map g with hρ'
  haveI : IsProbabilityMeasure ρ' := by rw [hρ']; infer_instance
  have h2 : Integrable (fun y : Ek k => ‖y‖ ^ 2) ρ :=
    Integrable.of_bound ((measurable_norm.pow_const 2).aestronglyMeasurable) (b ^ 2)
      (hρb.mono fun y hy => by
        rw [Real.norm_eq_abs, abs_pow, abs_norm]; exact pow_le_pow_left₀ (norm_nonneg _) hy 2)
  have h2' : Integrable (fun y : Ek r => ‖y‖ ^ 2) ρ' := by
    rw [hρ']
    refine (integrable_map_measure (measurable_norm.pow_const 2).aestronglyMeasurable
      hgm.aemeasurable).2 ?_
    refine Integrable.of_bound ((measurable_norm.pow_const 2).comp hgm).aestronglyMeasurable
      ((s * b) ^ 2) (hgb.mono fun y hy => ?_)
    simp only [Function.comp_apply, Real.norm_eq_abs, abs_pow, abs_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) hy 2
  have h3' : Integrable (fun y : Ek r => ‖y‖ ^ 3) ρ' := by
    rw [hρ']
    refine (integrable_map_measure (measurable_norm.pow_const 3).aestronglyMeasurable
      hgm.aemeasurable).2 ?_
    refine Integrable.of_bound ((measurable_norm.pow_const 3).comp hgm).aestronglyMeasurable
      ((s * b) ^ 3) (hgb.mono fun y hy => ?_)
    simp only [Function.comp_apply, Real.norm_eq_abs, abs_pow, abs_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) hy 3
  -- mean zero
  have hmean : ∫ y, y ∂ρ = 0 := u5_vec_mean_zero ρ hρb h0
  have hint1 : Integrable (fun y : Ek k => ‖y‖) ρ := Integrable.of_bound (f := fun y : Ek k => ‖y‖) measurable_norm.aestronglyMeasurable b
    (hρb.mono fun y hy => by simpa using hy)
  have h0' : ∀ c, ∫ x, x c ∂ρ' = 0 := fun c => by
    rw [hρ', integral_map hgm.aemeasurable (by fun_prop : Measurable fun x : Ek r => x c).aestronglyMeasurable]
    have := u5_integral_apply_clm ρ hint1 (s • τ) c
    calc ∫ y, g y c ∂ρ = ∫ y, ((s • τ) y) c ∂ρ := rfl
      _ = ((s • τ) (∫ y, y ∂ρ)) c := this
      _ = 0 := by rw [hmean]; simp
  -- the law of the sum
  have hlawS : (Measure.pi fun _ : Fin N => ρ).map (fun ω => τ (s • ∑ i, ω i)) =
      (Measure.pi fun _ : Fin N => ρ').map (fun p => ∑ i, p i) := by
    have hsm : Measurable (fun p : Fin N → Ek r => ∑ i, p i) :=
      Finset.measurable_sum _ fun i _ => measurable_pi_apply i
    have hmeas : Measurable (fun (x : Fin N → Ek k) (i : Fin N) => g (x i)) :=
      Measurable.of_eval fun i => hgm.comp (measurable_pi_apply i)
    rw [← Measure.pi_map_pi (μ := fun _ : Fin N => ρ) (f := fun _ => g) (fun _ => hgm.aemeasurable),
      Measure.map_map hsm hmeas]
    have : (fun ω : Fin N → Ek k => τ (s • ∑ i, ω i)) =
        (fun p : Fin N → Ek r => ∑ i, p i) ∘ (fun (x : Fin N → Ek k) (i : Fin N) => g (x i)) := by
      ext ω : 1
      simp [hg, map_sum, Finset.smul_sum]
    rw [this]
  -- the law of the Gaussian
  have hQp : (Yurinskii.momentMatrix ρ).PosSemidef := Yurinskii.momentMatrix_posSemidef ρ h2
  have hQ'p : (∑ _i : Fin N, Yurinskii.momentMatrix ρ').PosSemidef :=
    Matrix.posSemidef_sum _ fun _ _ => Yurinskii.momentMatrix_posSemidef ρ' h2'
  have hlawG : (multivariateGaussian (0 : Ek k) (Yurinskii.momentMatrix ρ)).map τ =
      multivariateGaussian (0 : Ek r) (∑ _i : Fin N, Yurinskii.momentMatrix ρ') := by
    refine u5_gauss_map hQ'p τ (fun u v => ?_) hQp
    rw [u5_dot_moment ρ h2]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have : u ⬝ᵥ ((N • Yurinskii.momentMatrix ρ') *ᵥ v) = N * (u ⬝ᵥ (Yurinskii.momentMatrix ρ' *ᵥ v)) := by
      rw [Matrix.smul_mulVec, dotProduct_smul]; simp
    rw [this, u5_dot_moment ρ' h2' u v, hρ', integral_map hgm.aemeasurable (by fun_prop : Measurable fun x : Ek r => (inner ℝ u x) * (inner ℝ v x)).aestronglyMeasurable]
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    simp only [hg, inner_smul_right, ContinuousLinearMap.adjoint_inner_left]
    have hNs : (N : ℝ) * (s * s) = 1 := by
      rw [hs, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg N)]
      field_simp
    calc ⟪u, τ y⟫ * ⟪v, τ y⟫ = ((N : ℝ) * (s * s)) * (⟪u, τ y⟫ * ⟪v, τ y⟫) := by rw [hNs, one_mul]
      _ = _ := by ring
  rw [hlawS, hlawG]
  have := u5_w1_iid_gauss (N := N) ρ' h0' h3' hε
  refine this.trans (ENNReal.ofReal_le_ofReal ?_)
  have hint : ∫ x, ‖x‖ ^ 3 ∂ρ' ≤ (s * b) ^ 3 := by
    rw [hρ', integral_map hgm.aemeasurable (measurable_norm.pow_const 3).aestronglyMeasurable]
    have hi : Integrable (fun y : Ek k => ‖g y‖ ^ 3) ρ := by
      refine Integrable.of_bound ((measurable_norm.pow_const 3).comp hgm).aestronglyMeasurable
        ((s * b) ^ 3) (hgb.mono fun y hy => ?_)
      simp only [Real.norm_eq_abs, abs_pow, abs_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) hy 3
    calc ∫ y, ‖g y‖ ^ 3 ∂ρ ≤ ∫ _y, (s * b) ^ 3 ∂ρ :=
          integral_mono_ae hi (integrable_const _) (hgb.mono fun y hy =>
            pow_le_pow_left₀ (norm_nonneg _) hy 3)
      _ = (s * b) ^ 3 := by simp
  have hNb : (N : ℝ) * (s * b) ^ 3 = b ^ 3 / Real.sqrt N := by
    have hsq : (N : ℝ) = Real.sqrt N * Real.sqrt N := (Real.mul_self_sqrt (Nat.cast_nonneg N)).symm
    rw [hs]
    field_simp
    rw [Real.sq_sqrt (Nat.cast_nonneg N)]
  have hε2 : 0 ≤ 2 / ε ^ 2 := by positivity
  have hc4 : 0 ≤ 2 + Yurinskii.c4 / 2 := by have := Yurinskii.c4_nonneg; positivity
  gcongr
  rw [← hNb]
  exact mul_le_mul_of_nonneg_left hint (Nat.cast_nonneg N)


/-- Orthonormal coordinates on a finite-dimensional subspace. -/
lemma u5_proj_data {k : ℕ} (V : Submodule ℝ (Ek k)) :
    ∃ (τ : Ek k →L[ℝ] Ek (Module.finrank ℝ V)) (ι : Ek (Module.finrank ℝ V) →L[ℝ] Ek k),
      (∀ z, ι (τ z) = V.starProjection z) ∧ ‖ι‖ ≤ 1 ∧ ∀ z, ‖τ z‖ ≤ ‖z‖ := by
  let e := stdOrthonormalBasis ℝ V
  refine ⟨e.repr.toLinearIsometry.toContinuousLinearMap.comp V.orthogonalProjectionOnto,
    V.subtypeL.comp e.repr.symm.toLinearIsometry.toContinuousLinearMap, fun z => ?_, ?_, fun z => ?_⟩
  · simp
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
    simp only [one_mul, ContinuousLinearMap.coe_comp', Function.comp_apply, Submodule.subtypeL_apply,
      LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
    exact le_of_eq (by rw [← Submodule.coe_norm]; exact e.repr.symm.norm_map w)
  · simpa using V.norm_orthogonalProjectionOnto_apply_le z

theorem u5_core2 {k N : ℕ} (hN : 1 ≤ N) (ρ : Measure (Ek k)) [IsProbabilityMeasure ρ] {b : ℝ}
    (hρb : ∀ᵐ y ∂ρ, ‖y‖ ≤ b) (h0 : ∀ c, ∫ y, y c ∂ρ = 0)
    (V : Submodule ℝ (Ek k)) {n : ℕ} (hV : Module.finrank ℝ V ≤ n) {δ : ℝ} (hδ : 0 ≤ δ)
    (htail : ∫ y, ‖y - V.starProjection y‖ ^ 2 ∂ρ ≤ δ ^ 2) {ε : ℝ} (hε : 0 < ε) :
    wassersteinE 1 ((Measure.pi fun _ : Fin N => ρ).map
        (fun ω => (Real.sqrt N)⁻¹ • ∑ i, ω i))
      (multivariateGaussian (0 : Ek k) (Yurinskii.momentMatrix ρ)) ≤
    ENNReal.ofReal (2 * δ + (2 * ε * Real.sqrt n + 2 / ε ^ 2 *
      ((2 + Yurinskii.c4 / 2) * (b ^ 3 / Real.sqrt N)))) := by
  haveI : V.HasOrthogonalProjection := inferInstance
  set P : Ek k →L[ℝ] Ek k := V.starProjection with hP
  obtain ⟨τ, ι, hτι, hι, hτ⟩ := u5_proj_data V
  set s : ℝ := (Real.sqrt N)⁻¹ with hs
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsqrt : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hs0 : 0 ≤ s := inv_nonneg.2 hsqrt.le
  have hb0 : 0 ≤ b := by
    obtain ⟨y0, hy0⟩ := hρb.exists
    exact (norm_nonneg _).trans hy0
  have hNs : (N : ℝ) * (s * s) = 1 := by
    rw [hs, ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg N)]
    field_simp
  set π : Measure (Fin N → Ek k) := Measure.pi fun _ : Fin N => ρ with hπ
  set γ := multivariateGaussian (0 : Ek k) (Yurinskii.momentMatrix ρ) with hγ
  have hSm : Measurable (fun ω : Fin N → Ek k => s • ∑ i, ω i) :=
    (Finset.measurable_sum _ fun i _ => measurable_pi_apply i).const_smul s
  have hPm : Measurable P := P.continuous.measurable
  have h2 : Integrable (fun y : Ek k => ‖y‖ ^ 2) ρ :=
    Integrable.of_bound ((measurable_norm.pow_const 2).aestronglyMeasurable) (b ^ 2)
      (hρb.mono fun y hy => by
        rw [Real.norm_eq_abs, abs_pow, abs_norm]; exact pow_le_pow_left₀ (norm_nonneg _) hy 2)
  have hmean : ∫ y, y ∂ρ = 0 := u5_vec_mean_zero ρ hρb h0
  have hint1 : Integrable (fun y : Ek k => ‖y‖) ρ :=
    Integrable.of_bound (f := fun y : Ek k => ‖y‖) measurable_norm.aestronglyMeasurable b
      (hρb.mono fun y hy => by simpa using hy)
  -- the complement map
  set Q : Ek k →L[ℝ] Ek k := ContinuousLinearMap.id ℝ (Ek k) - P with hQ
  have hQapp : ∀ y, Q y = y - P y := fun y => rfl
  have hQb : ∀ y, ‖Q y‖ ≤ ‖y‖ := fun y => by
    rw [hQapp]; simpa using u5_proj_le V y 0 V.zero_mem
  have hQ0 : ∀ c, ∫ y, (Q y) c ∂ρ = 0 := fun c => by
    rw [u5_integral_apply_clm ρ hint1 Q c, hmean]; simp
  -- first estimate: S versus P S
  have hδ1 : ∫ ω, ‖(s • ∑ i, ω i) - P (s • ∑ i, ω i)‖ ∂π ≤ δ := by
    have e1 : ∀ ω : Fin N → Ek k, (s • ∑ i, ω i) - P (s • ∑ i, ω i) = s • ∑ i, Q (ω i) := fun ω => by
      simp [hQapp, map_sum, Finset.smul_sum, smul_sub]
    simp_rw [e1]
    have hmeasQ : Measurable fun ω : Fin N → Ek k => ‖s • ∑ i, Q (ω i)‖ :=
      ((Finset.measurable_sum _ fun i _ => Q.continuous.measurable.comp (measurable_pi_apply i)).const_smul s).norm
    have hbd : ∀ᵐ ω ∂π, ‖s • ∑ i, Q (ω i)‖ ≤ s * (N * b) :=
      (u5_ae_pi (N := N) hρb).mono fun ω hω => by
      rw [norm_smul, Real.norm_of_nonneg hs0]
      refine mul_le_mul_of_nonneg_left ?_ hs0
      calc ‖∑ i, Q (ω i)‖ ≤ ∑ i, ‖Q (ω i)‖ := norm_sum_le _ _
        _ ≤ ∑ _i : Fin N, b := Finset.sum_le_sum fun i _ => (hQb _).trans (hω i)
        _ = N * b := by simp
    have hL2 : MemLp (fun ω : Fin N → Ek k => ‖s • ∑ i, Q (ω i)‖) 2 π :=
      MemLp.of_bound hmeasQ.aestronglyMeasurable (s * (N * b)) (hbd.mono fun ω h => by
        rw [Real.norm_eq_abs, abs_norm]; exact h)
    have hsq : ∫ ω, ‖s • ∑ i, Q (ω i)‖ ^ 2 ∂π = ∫ y, ‖Q y‖ ^ 2 ∂ρ := by
      simp_rw [norm_smul, Real.norm_of_nonneg hs0, mul_pow]
      rw [integral_const_mul]
      have := u5_pi_sum_sq (N := N) ρ Q Q.continuous.measurable (B := b) (hρb.mono fun y hy => (hQb y).trans hy) hQ0
      rw [hπ, this, ← mul_assoc, show s ^ 2 * (N : ℝ) = 1 by nlinarith [hNs], one_mul]
    have hint0 : 0 ≤ ∫ ω, ‖s • ∑ i, Q (ω i)‖ ∂π := integral_nonneg fun _ => norm_nonneg _
    calc ∫ ω, ‖s • ∑ i, Q (ω i)‖ ∂π ≤ Real.sqrt (∫ ω, ‖s • ∑ i, Q (ω i)‖ ^ 2 ∂π) :=
          u5_integral_le_sqrt π hL2 hint0
      _ ≤ δ := by
          rw [hsq]
          refine Real.sqrt_le_iff.2 ⟨hδ, ?_⟩
          simpa [hQapp] using htail
  -- second estimate: Z versus P Z for the Gaussian
  have hδ2 : ∫ z, ‖P z - z‖ ∂γ ≤ δ := by
    have h2γ : Integrable (fun y : Ek k => ‖y‖ ^ 2) γ :=
      Yurinskii.integrable_norm_pow_gauss 2 (by norm_num)
    have hmeasQ : Measurable fun z : Ek k => ‖P z - z‖ :=
      ((P.continuous.measurable).sub measurable_id).norm
    have hL2 : MemLp (fun z : Ek k => ‖P z - z‖) 2 γ := by
      rw [memLp_two_iff_integrable_sq_norm hmeasQ.aestronglyMeasurable]
      refine h2γ.mono' (hmeasQ.norm.pow_const 2).aestronglyMeasurable (ae_of_all _ fun z => ?_)
      simp only [norm_norm, norm_pow, Real.norm_eq_abs, abs_norm]
      have : ‖P z - z‖ ≤ ‖z‖ := by rw [norm_sub_rev]; rw [← hQapp]; exact hQb z
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    have hsq : ∫ z, ‖P z - z‖ ^ 2 ∂γ ≤ δ ^ 2 := by
      have := u5_gauss_sq_eq ρ h2 Q
      simp only [hQapp] at this
      calc ∫ z, ‖P z - z‖ ^ 2 ∂γ = ∫ z, ‖z - P z‖ ^ 2 ∂γ := by
            refine integral_congr_ae (ae_of_all _ fun z => ?_)
            simp only [norm_sub_rev]
        _ = ∫ y, ‖y - P y‖ ^ 2 ∂ρ := this
        _ ≤ δ ^ 2 := htail
    have hint0 : 0 ≤ ∫ z, ‖P z - z‖ ∂γ := integral_nonneg fun _ => norm_nonneg _
    calc ∫ z, ‖P z - z‖ ∂γ ≤ Real.sqrt (∫ z, ‖P z - z‖ ^ 2 ∂γ) := u5_integral_le_sqrt γ hL2 hint0
      _ ≤ δ := Real.sqrt_le_iff.2 ⟨hδ, hsq⟩
  -- the three Wasserstein pieces
  have hW1 : wassersteinE 1 (π.map fun ω => s • ∑ i, ω i) (π.map fun ω => P (s • ∑ i, ω i)) ≤
      ENNReal.ofReal δ := by
    refine (wasserstein_le_integral π hSm (hPm.comp hSm) ?_).trans (ENNReal.ofReal_le_ofReal ?_)
    · refine Integrable.of_bound (hSm.sub (hPm.comp hSm)).norm.aestronglyMeasurable
        (s * (N * b)) ((u5_ae_pi (N := N) hρb).mono fun ω hω => ?_)
      have e1 : (s • ∑ i, ω i) - P (s • ∑ i, ω i) = s • ∑ i, Q (ω i) := by
        simp [hQapp, map_sum, Finset.smul_sum, smul_sub]
      rw [Real.norm_eq_abs, abs_norm]
      change ‖(s • ∑ i, ω i) - P (s • ∑ i, ω i)‖ ≤ _
      rw [e1, norm_smul, Real.norm_of_nonneg hs0]
      refine mul_le_mul_of_nonneg_left ?_ hs0
      calc ‖∑ i, Q (ω i)‖ ≤ ∑ i, ‖Q (ω i)‖ := norm_sum_le _ _
        _ ≤ ∑ _i : Fin N, b := Finset.sum_le_sum fun i _ => (hQb _).trans (hω i)
        _ = N * b := by simp
    · exact hδ1
  have hW3 : wassersteinE 1 (γ.map P) γ ≤ ENNReal.ofReal δ := by
    have := wasserstein_le_integral γ (Z := P) (W := fun z : Ek k => z) hPm measurable_id (by
      have h2γ : Integrable (fun y : Ek k => ‖y‖ ^ 2) γ :=
        Yurinskii.integrable_norm_pow_gauss 2 (by norm_num)
      refine Integrable.mono' (h2γ.add (integrable_const 1)) ((hPm.sub measurable_id).norm.aestronglyMeasurable)
        (ae_of_all _ fun z => ?_)
      have : ‖P z - z‖ ≤ ‖z‖ := by rw [norm_sub_rev]; rw [← hQapp]; exact hQb z
      show ‖‖P z - z‖‖ ≤ ‖z‖ ^ 2 + 1
      rw [norm_norm]
      nlinarith [norm_nonneg z, sq_nonneg (‖z‖ - 1)])
    have hid : γ.map (fun z : Ek k => z) = γ := Measure.map_id
    change wassersteinE 1 (γ.map P) (γ.map fun z : Ek k => z) ≤ _ at this
    rw [hid] at this
    exact this.trans (ENNReal.ofReal_le_ofReal hδ2)
  have hW2 : wassersteinE 1 (π.map fun ω => P (s • ∑ i, ω i)) (γ.map P) ≤
      ENNReal.ofReal (2 * ε * Real.sqrt (Module.finrank ℝ V) + 2 / ε ^ 2 *
        ((2 + Yurinskii.c4 / 2) * (b ^ 3 / Real.sqrt N))) := by
    have hlind := u5_core_lind (N := N) hN ρ hρb h0 τ hτ hε
    have e1 : (π.map fun ω => P (s • ∑ i, ω i)) = (π.map fun ω => τ (s • ∑ i, ω i)).map ι := by
      have := Measure.map_map (μ := π) ι.continuous.measurable (τ.continuous.measurable.comp hSm)
      refine Eq.trans ?_ this.symm
      congr 1
      ext ω : 1
      simp [hτι, hP]
    have e2 : γ.map P = (γ.map τ).map ι := by
      have := Measure.map_map (μ := γ) ι.continuous.measurable τ.continuous.measurable
      refine Eq.trans ?_ this.symm
      congr 1
      ext z : 1
      simp [hτι, hP]
    rw [e1, e2]
    exact (u5_wasserstein_map_le ι hι _ _).trans hlind
  have hT1 := wassersteinE_triangle 1 le_rfl (π.map fun ω => s • ∑ i, ω i)
    (π.map fun ω => P (s • ∑ i, ω i)) γ
  have hT2 := wassersteinE_triangle 1 le_rfl (π.map fun ω => P (s • ∑ i, ω i)) (γ.map P) γ
  have hX : 0 ≤ 2 * ε * Real.sqrt (Module.finrank ℝ V) + 2 / ε ^ 2 *
        ((2 + Yurinskii.c4 / 2) * (b ^ 3 / Real.sqrt N)) := by
    have := Yurinskii.c4_nonneg
    positivity
  have hXle : 2 * ε * Real.sqrt (Module.finrank ℝ V) + 2 / ε ^ 2 *
        ((2 + Yurinskii.c4 / 2) * (b ^ 3 / Real.sqrt N)) ≤ 2 * ε * Real.sqrt n + 2 / ε ^ 2 *
        ((2 + Yurinskii.c4 / 2) * (b ^ 3 / Real.sqrt N)) := by
    have : Real.sqrt (Module.finrank ℝ V) ≤ Real.sqrt n :=
      Real.sqrt_le_sqrt (by exact_mod_cast hV)
    nlinarith
  calc wassersteinE 1 (π.map fun ω => s • ∑ i, ω i) γ
      ≤ wassersteinE 1 (π.map fun ω => s • ∑ i, ω i) (π.map fun ω => P (s • ∑ i, ω i)) +
        wassersteinE 1 (π.map fun ω => P (s • ∑ i, ω i)) γ := hT1
    _ ≤ ENNReal.ofReal δ + (ENNReal.ofReal (2 * ε * Real.sqrt (Module.finrank ℝ V) + 2 / ε ^ 2 *
        ((2 + Yurinskii.c4 / 2) * (b ^ 3 / Real.sqrt N))) + ENNReal.ofReal δ) := by
        refine add_le_add hW1 (hT2.trans (add_le_add hW2 hW3))
    _ = ENNReal.ofReal (2 * δ + (2 * ε * Real.sqrt (Module.finrank ℝ V) + 2 / ε ^ 2 *
        ((2 + Yurinskii.c4 / 2) * (b ^ 3 / Real.sqrt N)))) := by
        rw [← ENNReal.ofReal_add hX hδ, ← ENNReal.ofReal_add hδ (add_nonneg hX hδ)]
        congr 1; ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)

end HRS.U5
