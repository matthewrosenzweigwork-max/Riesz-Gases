import HRS.Uniform.Q14Aux2

/-!
# Q14, part 3: forms given by an integral `∫ ⟨u,x⟩⟨u,y⟩ dξ`, and the Bures bound through `L²(ξ)`
-/

noncomputable section

open HRS
open MeasureTheory Filter Topology HRS.HilbertCLTAux
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q14

section Integral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {Ξ : Type*} [MeasurableSpace Ξ] {ξ : Measure Ξ} [IsFiniteMeasure ξ]

lemma q14_integrable_inner_mul {u v : Ξ → H} (hu : Measurable u) (hv : Measurable v) {M : ℝ}
    (hMu : ∀ s, ‖u s‖ ≤ M) (hMv : ∀ s, ‖v s‖ ≤ M) (x y : H) :
    Integrable (fun s => inner ℝ (u s) x * inner ℝ (v s) y) ξ := by
  refine Integrable.of_bound (C := M * ‖x‖ * (M * ‖y‖))
    ((hu.inner measurable_const).mul (hv.inner measurable_const)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |inner ℝ (u s) x| ≤ M * ‖x‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hMu s) (norm_nonneg _))
  have h2 : |inner ℝ (v s) y| ≤ M * ‖y‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hMv s) (norm_nonneg _))
  exact mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)

lemma q14_integrable_norm_sq {u : Ξ → H} (hu : Measurable u) {M : ℝ} (hM : ∀ s, ‖u s‖ ≤ M) :
    Integrable (fun s => ‖u s‖ ^ 2) ξ := by
  refine Integrable.of_bound (C := M ^ 2) (hu.norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hM s) 2

/-- The form `C x y = ∫ ⟨u,x⟩⟨u,y⟩ dξ` is trace class with trace `∫ ‖u‖² dξ`. -/
lemma q14_form_of_integral {u : Ξ → H} (hu : Measurable u) {M : ℝ} (hM : ∀ s, ‖u s‖ ≤ M)
    {C : H →L[ℝ] H →L[ℝ] ℝ} (hC : ∀ x y, C x y = ∫ s, inner ℝ (u s) x * inner ℝ (u s) y ∂ξ)
    {ι : Type} (e : HilbertBasis ι ℝ H) :
    IsTraceClassCov C ∧ traceNormForm C = ∫ s, ‖u s‖ ^ 2 ∂ξ := by
  classical
  haveI : Countable ι := countable_of_orthonormal e.orthonormal
  have hint := fun x y => q14_integrable_inner_mul (ξ := ξ) hu hu hM hM x y
  have hdiag : ∀ j, C (e j) (e j) = ∫ s, inner ℝ (u s) (e j) ^ 2 ∂ξ := fun j => by
    rw [hC]; exact integral_congr_ae (Filter.Eventually.of_forall fun s => (sq _).symm)
  have hpt : ∀ s, HasSum (fun j => inner ℝ (u s) (e j) ^ 2) (‖u s‖ ^ 2) :=
    fun s => q14_hasSum_sq e (u s)
  have hsumle : ∀ F : Finset ι, ∑ j ∈ F, C (e j) (e j) ≤ ∫ s, ‖u s‖ ^ 2 ∂ξ := by
    intro F
    simp only [hdiag]
    rw [← integral_finset_sum _ fun j _ => by
      simpa [sq] using hint (e j) (e j)]
    refine integral_mono (integrable_finset_sum _ fun j _ => by simpa [sq] using hint (e j) (e j))
      (q14_integrable_norm_sq hu hM) fun s => ?_
    have := e.orthonormal.sum_inner_products_le (u s) (s := F)
    simp only [Real.norm_eq_abs, sq_abs] at this
    calc ∑ j ∈ F, inner ℝ (u s) (e j) ^ 2 = ∑ j ∈ F, inner ℝ (e j) (u s) ^ 2 :=
          Finset.sum_congr rfl fun j _ => by rw [real_inner_comm]
      _ ≤ ‖u s‖ ^ 2 := this
  have hnn : ∀ j, 0 ≤ C (e j) (e j) := fun j => by
    rw [hdiag]; exact integral_nonneg fun s => sq_nonneg _
  have hsm : Summable fun j => C (e j) (e j) := summable_of_sum_le hnn hsumle
  have htc : IsTraceClassCov C := by
    refine ⟨fun x y => ?_, fun x => ?_, ⟨ι, e, hsm⟩⟩
    · rw [hC, hC]; exact integral_congr_ae (Filter.Eventually.of_forall fun s => mul_comm _ _)
    · rw [hC]; exact integral_nonneg fun s => mul_self_nonneg _
  refine ⟨htc, ?_⟩
  have h1 : ∑' j, C (e j) (e j) = ∫ s, ‖u s‖ ^ 2 ∂ξ := by
    have hnorm : Summable fun j => ∫ s, ‖inner ℝ (u s) (e j) ^ 2‖ ∂ξ := by
      refine hsm.congr fun j => ?_
      rw [hdiag]
      exact integral_congr_ae (Filter.Eventually.of_forall fun s =>
        (Real.norm_of_nonneg (sq_nonneg _)).symm)
    have := integral_tsum_of_summable_integral_norm
      (fun j => by simpa [sq] using hint (e j) (e j)) hnorm
    simp only [(hpt _).tsum_eq] at this
    rw [← this]
    exact tsum_congr fun j => hdiag j
  rw [← h1]
  exact le_antisymm (traceNormForm_le_basis_trace htc e) (htc.tsum_basis_le e)

lemma q14_memLp_inner {u : Ξ → H} (hu : Measurable u) {M : ℝ} (hM : ∀ s, ‖u s‖ ≤ M) (x : H) :
    MemLp (fun s => inner ℝ (u s) x) 2 ξ := by
  refine MemLp.of_bound (hu.inner measurable_const).aestronglyMeasurable (M * ‖x‖)
    (Filter.Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hM s) (norm_nonneg _))

lemma q14_exists_op {u : Ξ → H} (hu : Measurable u) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ s, ‖u s‖ ≤ M) :
    ∃ A : H →L[ℝ] Lp ℝ 2 ξ, ∀ x, A x =ᵐ[ξ] fun s => inner ℝ (u s) x := by
  classical
  let lin : H →ₗ[ℝ] Lp ℝ 2 ξ :=
    { toFun := fun x => (q14_memLp_inner hu hM x).toLp _
      map_add' := fun x y => by
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp (q14_memLp_inner hu hM (x + y)),
          MemLp.coeFn_toLp (q14_memLp_inner hu hM x), MemLp.coeFn_toLp (q14_memLp_inner hu hM y),
          Lp.coeFn_add ((q14_memLp_inner hu hM x).toLp _) ((q14_memLp_inner hu hM y).toLp _)]
          with s h1 h2 h3 h4
        rw [h4]; simp only [Pi.add_apply]; rw [h1, h2, h3, inner_add_right]
      map_smul' := fun c x => by
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp (q14_memLp_inner hu hM (c • x)),
          MemLp.coeFn_toLp (q14_memLp_inner hu hM x),
          Lp.coeFn_smul c ((q14_memLp_inner hu hM x).toLp _)] with s h1 h2 h4
        rw [RingHom.id_apply, h4]; simp only [Pi.smul_apply]; rw [h1, h2, inner_smul_right]
        rfl }
  have hlin : ∀ x, lin x =ᵐ[ξ] fun s => inner ℝ (u s) x := fun x =>
    MemLp.coeFn_toLp (q14_memLp_inner hu hM x)
  have hnorm : ∀ x, ‖lin x‖ ^ 2 = ∫ s, inner ℝ (u s) x * inner ℝ (u s) x ∂ξ := by
    intro x
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hlin x] with s hs
    rw [hs]; simp [sq]
  refine ⟨lin.mkContinuous (M * Real.sqrt (ξ.real Set.univ)) fun x => ?_, fun x => hlin x⟩
  have h1 : ‖lin x‖ ^ 2 ≤ (M * Real.sqrt (ξ.real Set.univ) * ‖x‖) ^ 2 := by
    rw [hnorm]
    calc ∫ s, inner ℝ (u s) x * inner ℝ (u s) x ∂ξ ≤ ∫ s, (M * ‖x‖) ^ 2 ∂ξ := by
          refine integral_mono (q14_integrable_inner_mul hu hu hM hM x x) (integrable_const _)
            fun s => ?_
          have := (abs_real_inner_le_norm (u s) x).trans
            (mul_le_mul_of_nonneg_right (hM s) (norm_nonneg x))
          nlinarith [abs_mul_abs_self (inner ℝ (u s) x), abs_nonneg (inner ℝ (u s) x)]
      _ = (M * Real.sqrt (ξ.real Set.univ) * ‖x‖) ^ 2 := by
          have hsq : Real.sqrt (ξ.real Set.univ) ^ 2 = ξ.real Set.univ :=
            Real.sq_sqrt measureReal_nonneg
          have e : (M * Real.sqrt (ξ.real Set.univ) * ‖x‖) ^ 2 =
              ξ.real Set.univ * (M ^ 2 * ‖x‖ ^ 2) := by
            rw [mul_pow, mul_pow, hsq]; ring
          rw [integral_const, smul_eq_mul, e, mul_pow]
  have hM1 : 0 ≤ M * Real.sqrt (ξ.real Set.univ) * ‖x‖ := by positivity
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hM1 two_ne_zero).1 h1

/-- The Bures bound for forms given by integrals: `𝔟(C,D)² ≤ ∫ ‖u - v‖² dξ`. -/
theorem q14_bures2_le_integral {u v : Ξ → H} (hu : Measurable u) (hv : Measurable v) {M : ℝ}
    (hM0 : 0 ≤ M) (hMu : ∀ s, ‖u s‖ ≤ M) (hMv : ∀ s, ‖v s‖ ≤ M) {C D : H →L[ℝ] H →L[ℝ] ℝ}
    (hC : ∀ x y, C x y = ∫ s, inner ℝ (u s) x * inner ℝ (u s) y ∂ξ)
    (hD : ∀ x y, D x y = ∫ s, inner ℝ (v s) x * inner ℝ (v s) y ∂ξ) :
    Uniform.bures2 C D ≤ ∫ s, ‖u s - v s‖ ^ 2 ∂ξ := by
  classical
  obtain ⟨ι, hι, e, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
  haveI := hι
  obtain ⟨htcC, htrC⟩ := q14_form_of_integral hu hMu hC e
  obtain ⟨htcD, htrD⟩ := q14_form_of_integral hv hMv hD e
  obtain ⟨A, hA⟩ := q14_exists_op (ξ := ξ) hu hM0 hMu
  obtain ⟨B, hB⟩ := q14_exists_op (ξ := ξ) hv hM0 hMv
  have hAA : ∀ x y, inner ℝ (A x) (A y) = C x y := by
    intro x y
    rw [L2.inner_def, hC]
    refine integral_congr_ae ?_
    filter_upwards [hA x, hA y] with s h1 h2
    rw [h1, h2]; simp [mul_comm]
  have hBB : ∀ x y, inner ℝ (B x) (B y) = D x y := by
    intro x y
    rw [L2.inner_def, hD]
    refine integral_congr_ae ?_
    filter_upwards [hB x, hB y] with s h1 h2
    rw [h1, h2]; simp [mul_comm]
  have hmain := q14_bures2_le e htcC htcD A B hAA hBB
  -- the cross term
  have hcross : ∀ j, inner ℝ (A (e j)) (B (e j)) = ∫ s, inner ℝ (u s) (e j) * inner ℝ (v s) (e j) ∂ξ := by
    intro j
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hA (e j), hB (e j)] with s h1 h2
    rw [h1, h2]; simp [mul_comm]
  have hCs : Summable fun j => C (e j) (e j) := by
    obtain ⟨T, hT, -⟩ := htcC.hasSum_basis e; exact hT.summable
  have hDs : Summable fun j => D (e j) (e j) := by
    obtain ⟨T, hT, -⟩ := htcD.hasSum_basis e; exact hT.summable
  have hint : ∀ j, Integrable (fun s => inner ℝ (u s) (e j) * inner ℝ (v s) (e j)) ξ :=
    fun j => q14_integrable_inner_mul hu hv hMu hMv _ _
  have hnorm : Summable fun j => ∫ s, ‖inner ℝ (u s) (e j) * inner ℝ (v s) (e j)‖ ∂ξ := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun s => norm_nonneg _)
      (fun j => ?_) ((hCs.add hDs).mul_left (1 / 2))
    have h1 : ∫ s, ‖inner ℝ (u s) (e j) * inner ℝ (v s) (e j)‖ ∂ξ ≤
        ∫ s, (1 / 2) * (inner ℝ (u s) (e j) * inner ℝ (u s) (e j) +
          inner ℝ (v s) (e j) * inner ℝ (v s) (e j)) ∂ξ := by
      refine integral_mono (hint j).norm ?_ fun s => ?_
      · exact ((q14_integrable_inner_mul hu hu hMu hMu (e j) (e j)).add
          (q14_integrable_inner_mul hv hv hMv hMv (e j) (e j))).const_mul _
      · rw [Real.norm_eq_abs, abs_mul]
        nlinarith [sq_nonneg (|inner ℝ (u s) (e j)| - |inner ℝ (v s) (e j)|),
          abs_mul_abs_self (inner ℝ (u s) (e j)), abs_mul_abs_self (inner ℝ (v s) (e j))]
    refine h1.trans (le_of_eq ?_)
    rw [integral_const_mul, integral_add (q14_integrable_inner_mul hu hu hMu hMu (e j) (e j))
      (q14_integrable_inner_mul hv hv hMv hMv (e j) (e j)), hC, hD]
  have hpt : ∀ s, HasSum (fun j => inner ℝ (u s) (e j) * inner ℝ (v s) (e j)) (inner ℝ (u s) (v s)) :=
    fun s => by
      have := e.hasSum_inner_mul_inner (u s) (v s)
      convert this using 2 with j
      rw [real_inner_comm (v s) (e j)]
  have hswap := integral_tsum_of_summable_integral_norm hint hnorm
  simp only [(hpt _).tsum_eq] at hswap
  have hcr : ∑' j, inner ℝ (A (e j)) (B (e j)) = ∫ s, inner ℝ (u s) (v s) ∂ξ := by
    rw [tsum_congr hcross, hswap]
  rw [hcr, htrC, htrD] at hmain
  have hexp : ∫ s, ‖u s - v s‖ ^ 2 ∂ξ =
      ∫ s, ‖u s‖ ^ 2 ∂ξ + ∫ s, ‖v s‖ ^ 2 ∂ξ - 2 * ∫ s, inner ℝ (u s) (v s) ∂ξ := by
    have hi : Integrable (fun s => inner ℝ (u s) (v s)) ξ := by
      refine Integrable.of_bound (C := M * M) (hu.inner hv).aestronglyMeasurable
        (Filter.Eventually.of_forall fun s => ?_)
      rw [Real.norm_eq_abs]
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (hMu s) (hMv s) (norm_nonneg _) hM0)
    rw [← integral_add (q14_integrable_norm_sq hu hMu) (q14_integrable_norm_sq hv hMv),
      ← integral_const_mul, ← integral_sub (f := fun s => ‖u s‖ ^ 2 + ‖v s‖ ^ 2)
        ((q14_integrable_norm_sq hu hMu).add (q14_integrable_norm_sq hv hMv)) (hi.const_mul 2)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only []
    rw [norm_sub_sq_real]; ring
  rw [hexp]; exact hmain

end Integral

end HRS.Uniform.Q14
