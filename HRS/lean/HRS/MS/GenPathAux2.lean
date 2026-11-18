import HRS.MS.GenPathAux1
import HRS.MS.GoFeatAux4
import HRS.Whole.AppendixALemmas

/-!
# S5.6 packet P1, part 1: `ulocNormE` and `cNormE` of a function with bounded derivatives

`s56_uloc_of_sup`: `‖g‖_{H^r_uloc} ≤ C K'` when `‖D^l g‖_∞ ≤ K'` for `l ≤ r` (the constant depends on `d, r, χ` only).
`s56_cNormE_le`: the quantity `𝒩(h) = cNormE χ h` of `test_cutoff_pathwise` is bounded by `C K'` when `h` is `C^{mStar d - 1}`
with `‖D^l h‖_∞ ≤ K'` for `l ≤ mStar d - 1`.  Helper names carry the prefix `s56_`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.GenPath

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.RdInit

variable {d : ℕ}

theorem s56_uloc_of_sup {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) (r : ℕ) :
    ∃ Cu : ℝ, 0 ≤ Cu ∧ ∀ (g : Euc d → ℝ) (K' : ℝ), 0 ≤ K' → ContDiff ℝ r g →
      (∀ l ≤ r, ∀ x, ‖iteratedFDeriv ℝ l g x‖ ≤ K') →
      ulocNormE r χ g ≤ ENNReal.ofReal (Cu * K') := by
  obtain ⟨M, hM0, hM⟩ := mri_cutoff_bound hχ r
  set V0 : ℝ := (volume (Metric.ball (0 : Euc d) 2)).toReal with hV0
  have hV00 : 0 ≤ V0 := ENNReal.toReal_nonneg
  refine ⟨Real.sqrt (mriKc d r M * (((r : ℝ) + 1) * V0)), Real.sqrt_nonneg _, fun g K' hK0 hg hK => ?_⟩
  set Gc : ℝ := ((r : ℝ) + 1) * K' ^ 2 with hGc
  have hG : ∀ x, mriG r g x ≤ Gc := by
    intro x
    unfold mriG
    calc ∑ i ∈ Finset.range (r + 1), ‖iteratedFDeriv ℝ i g x‖ ^ 2
        ≤ ∑ _i ∈ Finset.range (r + 1), K' ^ 2 :=
          Finset.sum_le_sum fun i hi =>
            pow_le_pow_left₀ (norm_nonneg _) (hK i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) x) 2
      _ = Gc := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  have hbound : ∀ z : Euc d, ∫ x in Metric.ball z 2, mriG r g x ≤ Gc * V0 := by
    intro z
    have hGint : IntegrableOn (mriG r g) (Metric.ball z 2) volume :=
      ((mriG_continuous hg).continuousOn.integrableOn_compact (isCompact_closedBall z 2)).mono_set
        Metric.ball_subset_closedBall
    have hcint : IntegrableOn (fun _ : Euc d => Gc) (Metric.ball z 2) volume :=
      integrableOn_const measure_ball_lt_top.ne
    calc ∫ x in Metric.ball z 2, mriG r g x ≤ ∫ x in Metric.ball z 2, Gc :=
          setIntegral_mono_on hGint hcint measurableSet_ball fun x _ => hG x
      _ = Gc * V0 := by
          rw [setIntegral_const, smul_eq_mul, Measure.real, Measure.addHaar_ball_center, mul_comm]
  have hEq : mriKc d r M * (Gc * V0) =
      (Real.sqrt (mriKc d r M * (((r : ℝ) + 1) * V0)) * K') ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by have := mriKc_nonneg d r M; positivity), hGc]; ring
  have hlt : ∀ z : Euc d, sobolevNormE (r : ℝ) (fun x => χ (x - z) * g x) ≤
      ENNReal.ofReal (Real.sqrt (mriKc d r M * (((r : ℝ) + 1) * V0)) * K') := by
    intro z
    obtain ⟨hmem, -, hle⟩ := mri_cell_bound hχ hM0 r hM hg z
    unfold sobolevNormE
    simp only [hmem, ite_true]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (r : ℝ) (fun x => χ (x - z) * g x)) ≤
        Real.sqrt ((Real.sqrt (mriKc d r M * (((r : ℝ) + 1) * V0)) * K') ^ 2) :=
      Real.sqrt_le_sqrt (by
        rw [← hEq]
        exact hle.trans (mul_le_mul_of_nonneg_left (hbound _) (mriKc_nonneg d r M)))
    rwa [Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) hK0)] at h2
  unfold ulocNormE
  exact iSup_le hlt

theorem s56_mStar_pred (d : ℕ) : 2 ≤ mStar d - 1 := by
  unfold mStar; omega

theorem s56_cNormE_le {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) :
    ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ (h : Euc d → ℝ) (K' : ℝ), 0 ≤ K' → ContDiff ℝ ((mStar d - 1 : ℕ) : WithTop ℕ∞) h →
      (∀ l ≤ mStar d - 1, ∀ x, ‖iteratedFDeriv ℝ l h x‖ ≤ K') →
      cNormE χ h ≤ ENNReal.ofReal (Cn * K') := by
  obtain ⟨Cu, hCu0, hCu⟩ := s56_uloc_of_sup hχ (mStar d - 1)
  refine ⟨2 + Cu, by positivity, fun h K' hK0 hh hK => ?_⟩
  have hm2 := s56_mStar_pred d
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by exact_mod_cast (show 1 ≤ mStar d - 1 by omega))
  have hdiff : Differentiable ℝ h := hh1.differentiable one_ne_zero
  have hLip : LipschitzWith (Real.toNNReal K') h := by
    refine lipschitzWith_of_nnnorm_fderiv_le hdiff fun x => ?_
    have h1 := hK 1 (by omega) x
    have h2 : ‖fderiv ℝ h x‖ = ‖iteratedFDeriv ℝ 1 h x‖ := by
      have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := h) (x := x) (n := 0)
      rw [norm_iteratedFDeriv_zero] at this
      exact this
    rw [← NNReal.coe_le_coe, coe_nnnorm, h2, Real.coe_toNNReal _ hK0]
    exact h1
  have hsup : ∀ x, |h x| ≤ K' := fun x => by
    have := hK 0 (by omega) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hl1 : (⨆ x, ENNReal.ofReal |h x|) ≤ ENNReal.ofReal K' :=
    iSup_le fun x => ENNReal.ofReal_le_ofReal (hsup x)
  have hl2 : (⨆ p : {p : Euc d × Euc d // p.1 ≠ p.2},
      ENNReal.ofReal (|h p.1.1 - h p.1.2| / ‖p.1.1 - p.1.2‖)) ≤ ENNReal.ofReal K' := by
    refine iSup_le fun p => ENNReal.ofReal_le_ofReal ?_
    have hne : 0 < ‖p.1.1 - p.1.2‖ := norm_pos_iff.2 (sub_ne_zero.2 p.2)
    rw [div_le_iff₀ hne]
    have := hLip.dist_le_mul p.1.1 p.1.2
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hK0] at this
    exact this
  unfold cNormE lipNormE
  calc _ ≤ (ENNReal.ofReal K' + ENNReal.ofReal K') + ENNReal.ofReal (Cu * K') :=
        add_le_add (add_le_add hl1 hl2) (hCu h K' hK0 hh hK)
    _ = ENNReal.ofReal ((2 + Cu) * K') := by
        rw [← ENNReal.ofReal_add hK0 hK0, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

section Form

open scoped RealInnerProductSpace

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

noncomputable def s56_Bop (A : K →L[ℝ] K) : K →L[ℝ] K →L[ℝ] ℝ :=
  ((innerSL ℝ : K →L[ℝ] K →L[ℝ] ℝ).flip.comp A).flip

lemma s56_Bop_apply (A : K →L[ℝ] K) (u v : K) : s56_Bop A u v = inner ℝ u (A v) := by
  simp only [s56_Bop, ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply]
  rw [innerSL_apply_apply, real_inner_comm]

lemma s56_Bop_norm_le (A : K →L[ℝ] K) : ‖s56_Bop A‖ ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [s56_Bop_apply]
  calc ‖inner ℝ u (A v)‖ ≤ ‖u‖ * ‖A v‖ := norm_inner_le_norm _ _
    _ ≤ ‖u‖ * (‖A‖ * ‖v‖) := by gcongr; exact A.le_opNorm v
    _ = ‖A‖ * ‖u‖ * ‖v‖ := by ring

noncomputable def s56_Aop {n : ℕ} (e f : Fin n → K) (ε : Fin n → ℝ) : K →L[ℝ] K :=
  ∑ i, ε i • ((innerSL ℝ (e i)).smulRight (f i))

lemma s56_Aop_apply {n : ℕ} (e f : Fin n → K) (ε : Fin n → ℝ) (v : K) :
    s56_Aop e f ε v = ∑ i, (ε i * inner ℝ (e i) v) • f i := by
  simp [s56_Aop, mul_smul]

lemma s56_Aop_norm_le {n : ℕ} {e f : Fin n → K} {ε : Fin n → ℝ} (he : Orthonormal ℝ e)
    (hf : Orthonormal ℝ f) (hε : ∀ i, |ε i| ≤ 1) : ‖s56_Aop e f ε‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [s56_Aop_apply]
  have h1 := hf.inner_sum (fun i => ε i * inner ℝ (e i) v) (fun i => ε i * inner ℝ (e i) v) Finset.univ
  have h2 : ‖∑ i, (ε i * inner ℝ (e i) v) • f i‖ ^ 2 = ∑ i, (ε i * inner ℝ (e i) v) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, h1]
    simp [sq]
  have h3 : ∑ i, (ε i * inner ℝ (e i) v) ^ 2 ≤ ‖v‖ ^ 2 := by
    calc ∑ i, (ε i * inner ℝ (e i) v) ^ 2 ≤ ∑ i, ‖inner ℝ (e i) v‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [mul_pow, Real.norm_eq_abs, sq_abs]
          have : ε i ^ 2 ≤ 1 := by
            have := hε i
            nlinarith [abs_nonneg (ε i), sq_abs (ε i)]
          nlinarith [sq_nonneg (inner ℝ (e i) v)]
      _ ≤ ‖v‖ ^ 2 := he.sum_inner_products_le v
  have : ‖∑ i, (ε i * inner ℝ (e i) v) • f i‖ ≤ ‖v‖ := by
    refine le_of_sq_le_sq ?_ (norm_nonneg _)
    rw [h2]; exact h3
  simpa using this

theorem s56_h_data {k : ℕ} {Γ : Euc d → K} (hΓ : ContDiff ℝ k Γ) {B : ℝ}
    (hB : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j Γ x‖ ≤ B) {n : ℕ} {e f : Fin n → K} {ε : Fin n → ℝ}
    (he : Orthonormal ℝ e) (hf : Orthonormal ℝ f) (hε : ∀ i, |ε i| ≤ 1) :
    ContDiff ℝ k (fun x => ∑ i, ε i * (inner ℝ (Γ x) (e i) * inner ℝ (Γ x) (f i))) ∧
      ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j
        (fun x => ∑ i, ε i * (inner ℝ (Γ x) (e i) * inner ℝ (Γ x) (f i))) x‖ ≤ 2 ^ j * B ^ 2 := by
  set A := s56_Aop e f ε with hA
  have hA1 : ‖A‖ ≤ 1 := s56_Aop_norm_le he hf hε
  have hBn : ‖s56_Bop A‖ ≤ 1 := (s56_Bop_norm_le A).trans hA1
  have hrepr : (fun x => ∑ i, ε i * (inner ℝ (Γ x) (e i) * inner ℝ (Γ x) (f i))) =
      fun x => s56_Bop A (Γ x) (Γ x) := by
    funext x
    rw [s56_Bop_apply, hA, s56_Aop_apply, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_right, real_inner_comm (Γ x) (e i)]
    ring
  rw [hrepr]
  refine ⟨((s56_Bop A).contDiff.comp hΓ).clm_apply hΓ, fun j hj x => ?_⟩
  have h1 := (s56_Bop A).norm_iteratedFDeriv_le_of_bilinear_of_le_one hΓ hΓ x
    (n := j) (by exact_mod_cast hj) hBn
  refine h1.trans ?_
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) x)
  calc ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i Γ x‖ *
        ‖iteratedFDeriv ℝ (j - i) Γ x‖
      ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B ^ 2 := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have h2 := hB i (hi'.trans hj) x
        have h3 := hB (j - i) ((Nat.sub_le _ _).trans hj) x
        calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i Γ x‖ * ‖iteratedFDeriv ℝ (j - i) Γ x‖
            ≤ (j.choose i : ℝ) * B * B := by gcongr
          _ = (j.choose i : ℝ) * B ^ 2 := by ring
    _ = 2 ^ j * B ^ 2 := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose j

end Form

theorem s56_oNL_le {s C₀ Λ C : ℝ} (hd : 1 ≤ d) (hΛ : 1 ≤ Λ)
    (hC : C₀ * Λ ^ (s / d) + Real.log Λ / (2 * d) ≤ C) (N : ℕ) (hN : 2 ≤ N) :
    oNΛ d s C₀ Λ N ≤ oN d s C N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hΛpos : 0 < Λ := by linarith
  have hlogΛ : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  have hpow : 0 < (N : ℝ) ^ (s / d - 1) := Real.rpow_pos_of_pos hNpos _
  unfold oNΛ oN
  by_cases hs : s = 0
  · subst hs
    simp only [if_true, zero_div, Real.rpow_zero, mul_one, zero_sub]
    rw [Real.rpow_neg_one, Real.log_mul hNpos.ne' hΛpos.ne']
    have h2 : 0 ≤ Real.log Λ / (2 * d) := by positivity
    have hC' : C₀ + Real.log Λ / (2 * d) ≤ C := by simpa using hC
    have hNi : 0 < (N : ℝ)⁻¹ := inv_pos.2 hNpos
    have e1 : Real.log Λ / (2 * d * N) = (Real.log Λ / (2 * d)) * (N : ℝ)⁻¹ := by
      field_simp
    have e2 : (Real.log N + Real.log Λ) / (2 * d * N) =
        Real.log N / (2 * d * N) + (Real.log Λ / (2 * d)) * (N : ℝ)⁻¹ := by
      rw [add_div, e1]
    rw [e2]
    nlinarith [mul_le_mul_of_nonneg_right hC' hNi.le]
  · simp only [hs, if_false, zero_add, add_zero]
    have hlog2 : 0 ≤ Real.log Λ / (2 * d) := by positivity
    exact mul_le_mul_of_nonneg_right (by linarith) hpow.le

section Generic

open scoped RealInnerProductSpace

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

theorem s56_orthPairs_nonempty : Nonempty (OrthonormalPairs K) :=
  ⟨⟨⟨0, fun i => i.elim0, fun i => i.elim0⟩, ⟨fun i => i.elim0, fun i => i.elim0⟩,
    ⟨fun i => i.elim0, fun i => i.elim0⟩⟩⟩

/-- Generic covariance comparison: if `μ₁, μ₂` satisfy the test inequality
`|∫h dμ₁ - ∫h dμ₂| ≤ Cc 𝒩(h) Err` and the features `Γ_a` are `C^{m_*-1}` with derivatives bounded by `B`,
then `‖B₁ - B₂‖_{𝔖₁} ≤ 2 q n Cc Cn 2^{m_*-1} B² Err` for the forms `B_i(u,v) = 2q ∑_a ∫⟨Γ_a,u⟩⟨Γ_a,v⟩dμ_i`. -/
theorem s56_trace_generic {n : ℕ} {χ : Euc d → ℝ} {Cn : ℝ} (hCn : 0 ≤ Cn)
    (hCnb : ∀ (h : Euc d → ℝ) (K' : ℝ), 0 ≤ K' → ContDiff ℝ ((mStar d - 1 : ℕ) : WithTop ℕ∞) h →
      (∀ l ≤ mStar d - 1, ∀ x, ‖iteratedFDeriv ℝ l h x‖ ≤ K') →
      cNormE χ h ≤ ENNReal.ofReal (Cn * K'))
    (Γ : Fin n → Euc d → K) (B : ℝ)
    (hΓ : ∀ a, ContDiff ℝ ((mStar d - 1 : ℕ) : WithTop ℕ∞) (Γ a))
    (hB : ∀ a, ∀ j ≤ mStar d - 1, ∀ x, ‖iteratedFDeriv ℝ j (Γ a) x‖ ≤ B)
    (μ₁ μ₂ : Measure (Euc d)) [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂] {Cc Err : ℝ} (hCc : 0 ≤ Cc)
    (hErr : 0 ≤ Err)
    (hTest : ∀ h : Euc d → ℝ, cNormE χ h < ⊤ →
      |HRS.Whole.pair μ₁ h - HRS.Whole.pair μ₂ h| ≤ Cc * (cNormE χ h).toReal * Err)
    {q : ℝ} (hq : 0 ≤ q) (B₁ B₂ : K →L[ℝ] K →L[ℝ] ℝ)
    (h1 : ∀ u v, B₁ u v = 2 * q * ∑ a, ∫ x, inner ℝ (Γ a x) u * inner ℝ (Γ a x) v ∂μ₁)
    (h2 : ∀ u v, B₂ u v = 2 * q * ∑ a, ∫ x, inner ℝ (Γ a x) u * inner ℝ (Γ a x) v ∂μ₂) :
    traceNormForm (B₁ - B₂) ≤
      2 * q * n * (Cc * (Cn * (2 ^ (mStar d - 1) * B ^ 2)) * Err) := by
  have hbd : ∀ a, ∀ x, ‖Γ a x‖ ≤ B := fun a x => by
    have := hB a 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero] at this
  have hB0 : ∀ a : Fin n, 0 ≤ B := fun a => (norm_nonneg _).trans (hbd a 0)
  unfold traceNormForm
  haveI := s56_orthPairs_nonempty (K := K)
  refine ciSup_le fun p => ?_
  obtain ⟨⟨m', e, f⟩, he, hf⟩ := p
  simp only
  set ε : Fin m' → ℝ := fun i => if 0 ≤ (B₁ - B₂) (e i) (f i) then 1 else -1 with hε
  have hεabs : ∀ i, |ε i| ≤ 1 := fun i => by
    simp only [hε]; split_ifs <;> simp
  have habs : ∀ i, |(B₁ - B₂) (e i) (f i)| = ε i * (B₁ - B₂) (e i) (f i) := fun i => by
    simp only [hε]
    split_ifs with h
    · rw [abs_of_nonneg h, one_mul]
    · rw [abs_of_neg (not_le.1 h)]; ring
  simp_rw [habs]
  have hint : ∀ (μ : Measure (Euc d)) [IsFiniteMeasure μ], ∀ a, ∀ (u v : K), ‖u‖ = 1 → ‖v‖ = 1 →
      Integrable (fun x => inner ℝ (Γ a x) u * inner ℝ (Γ a x) v) μ := by
    intro μ _ a u v hu hv
    have hc : Continuous (Γ a) := (hΓ a).continuous
    refine Integrable.of_bound (C := B * B) ?_ (Eventually.of_forall fun x => ?_)
    · exact ((hc.inner continuous_const).mul (hc.inner continuous_const)).aestronglyMeasurable
    · rw [norm_mul]
      have e1 : ‖inner ℝ (Γ a x) u‖ ≤ B := by
        calc ‖inner ℝ (Γ a x) u‖ ≤ ‖Γ a x‖ * ‖u‖ := norm_inner_le_norm _ _
          _ ≤ B := by rw [hu, mul_one]; exact hbd a x
      have e2 : ‖inner ℝ (Γ a x) v‖ ≤ B := by
        calc ‖inner ℝ (Γ a x) v‖ ≤ ‖Γ a x‖ * ‖v‖ := norm_inner_le_norm _ _
          _ ≤ B := by rw [hv, mul_one]; exact hbd a x
      exact mul_le_mul e1 e2 (norm_nonneg _) (hB0 a)
  -- the test functions `h_a`
  set h : Fin n → Euc d → ℝ := fun a x => ∑ i, ε i * (inner ℝ (Γ a x) (e i) * inner ℝ (Γ a x) (f i))
    with hh
  have key : ∀ (μ : Measure (Euc d)) [IsFiniteMeasure μ] (a : Fin n),
      ∑ i, ε i * ∫ x, inner ℝ (Γ a x) (e i) * inner ℝ (Γ a x) (f i) ∂μ = HRS.Whole.pair μ (h a) := by
    intro μ _ a
    unfold HRS.Whole.pair
    rw [hh]
    simp only
    rw [integral_finset_sum _ (fun i _ => (hint μ a (e i) (f i) (he.1 i) (hf.1 i)).const_mul (ε i))]
    exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul]
  have hexp : ∀ i, ε i * (B₁ - B₂) (e i) (f i) = 2 * q *
      ∑ a, (ε i * ∫ x, inner ℝ (Γ a x) (e i) * inner ℝ (Γ a x) (f i) ∂μ₁ -
        ε i * ∫ x, inner ℝ (Γ a x) (e i) * inner ℝ (Γ a x) (f i) ∂μ₂) := fun i => by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply, h1, h2]
    simp only [← mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
    ring_nf
  have hsum : ∑ i, ε i * (B₁ - B₂) (e i) (f i) =
      2 * q * ∑ a, (HRS.Whole.pair μ₁ (h a) - HRS.Whole.pair μ₂ (h a)) := by
    simp_rw [hexp]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_sub_distrib, key μ₁ a, key μ₂ a]
  rw [hsum]
  have hK' : (0 : ℝ) ≤ 2 ^ (mStar d - 1) * B ^ 2 := by
    by_cases hn : n = 0
    · subst hn; positivity
    · have := hB0 ⟨0, Nat.pos_of_ne_zero hn⟩; positivity
  have hone : ∀ a : Fin n, |HRS.Whole.pair μ₁ (h a) - HRS.Whole.pair μ₂ (h a)| ≤
      Cc * (Cn * (2 ^ (mStar d - 1) * B ^ 2)) * Err := fun a => by
    obtain ⟨hcd, hder⟩ := s56_h_data (hΓ a) (hB a) he hf hεabs
    have hder' : ∀ l ≤ mStar d - 1, ∀ x, ‖iteratedFDeriv ℝ l (h a) x‖ ≤ 2 ^ (mStar d - 1) * B ^ 2 := by
      intro l hl x
      refine (hder l hl x).trans ?_
      gcongr
      · norm_num
    have hc := hCnb (h a) _ hK' hcd hder'
    have hlt : cNormE χ (h a) < ⊤ := lt_of_le_of_lt hc ENNReal.ofReal_lt_top
    refine (hTest (h a) hlt).trans ?_
    have : (cNormE χ (h a)).toReal ≤ Cn * (2 ^ (mStar d - 1) * B ^ 2) := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hc
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    gcongr
  calc 2 * q * ∑ a, (HRS.Whole.pair μ₁ (h a) - HRS.Whole.pair μ₂ (h a))
      ≤ 2 * q * ∑ _a : Fin n, Cc * (Cn * (2 ^ (mStar d - 1) * B ^ 2)) * Err := by
        gcongr with a _
        exact (le_abs_self _).trans (hone a)
    _ = 2 * q * n * (Cc * (Cn * (2 ^ (mStar d - 1) * B ^ 2)) * Err) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end Generic

end HRS.MS.GenPath
