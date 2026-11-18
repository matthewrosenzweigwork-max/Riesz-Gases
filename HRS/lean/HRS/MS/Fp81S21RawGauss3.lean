import HRS.MS.Fp81S21RawGauss

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS.Whole

private theorem fp81s21_oscDual_mem_iff {d : ℕ} {f : MultiIndex d → ℝ} :
    Memℓp f 2 ↔ Summable (fun α => f α ^ 2) := by
  rw [memℓp_gen_iff (by norm_num)]
  simp [Real.norm_eq_abs, sq_abs]

private theorem fp81s21_oscDual_norm_sq {d : ℕ} {m : ℝ}
    (q : OscDual d m) : ‖q‖ ^ 2 = ∑' α : MultiIndex d, OscDual.coord q α ^ 2 := by
  rw [OscDual.norm_eq_coord]
  have hs : 0 ≤ ∑' α : MultiIndex d, OscDual.coord q α ^ 2 :=
    tsum_nonneg fun _ => sq_nonneg _
  rw [Real.sq_sqrt hs]

private theorem fp81s21_oscDual_enorm_sq {d : ℕ} {m : ℝ}
    (q : OscDual d m) : ‖q‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖q‖ ^ 2) := by
  rw [← ofReal_norm_eq_enorm]
  exact (ENNReal.rpow_natCast _ 2).trans
    (ENNReal.ofReal_pow (norm_nonneg _) 2).symm

def fp81s21_oscDualCoordOf {d : ℕ} (m : ℝ) (f : MultiIndex d → ℝ) :
    OscDual d m :=
  if h : Memℓp f 2 then (⟨f, h⟩ : lp (fun _ : MultiIndex d => ℝ) 2) else 0

theorem fp81s21_oscDualCoordOf_apply {d : ℕ} {m : ℝ}
    {f : MultiIndex d → ℝ} (hf : Summable (fun α => f α ^ 2))
    (α : MultiIndex d) : OscDual.coord (fp81s21_oscDualCoordOf m f) α = f α := by
  have hm : Memℓp f 2 := fp81s21_oscDual_mem_iff.mpr hf
  simp [fp81s21_oscDualCoordOf, hm, OscDual.coord]

private theorem fp81s21_scalar_square_tonelli
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {d : ℕ} (f : MultiIndex d → Ω → ℝ)
    (hf : ∀ α, MemLp (f α) 2 P)
    (hS : Summable (fun α => ∫ ω, f α ω ^ 2 ∂P)) :
    (∫⁻ ω, ∑' α, ENNReal.ofReal (f α ω ^ 2) ∂P) =
      ENNReal.ofReal (∑' α, ∫ ω, f α ω ^ 2 ∂P) ∧
    ∀ᵐ ω ∂P, Summable (fun α => f α ω ^ 2) := by
  have hm : ∀ α, AEMeasurable (fun ω => ENNReal.ofReal (f α ω ^ 2)) P :=
    fun α => ((hf α).aestronglyMeasurable.pow 2).aemeasurable.ennreal_ofReal
  have hlin : (∫⁻ ω, ∑' α, ENNReal.ofReal (f α ω ^ 2) ∂P) =
      ENNReal.ofReal (∑' α, ∫ ω, f α ω ^ 2 ∂P) := by
    rw [lintegral_tsum hm]
    have hi : ∀ α, (∫⁻ ω, ENNReal.ofReal (f α ω ^ 2) ∂P) =
        ENNReal.ofReal (∫ ω, f α ω ^ 2 ∂P) := fun α =>
      (ofReal_integral_eq_lintegral_ofReal (hf α).integrable_sq
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm
    simp_rw [hi]
    exact (ENNReal.ofReal_tsum_of_nonneg
      (fun α => integral_nonneg fun _ => sq_nonneg _) hS).symm
  refine ⟨hlin, ?_⟩
  have hfinite :
      (∫⁻ ω, ∑' α, ENNReal.ofReal (f α ω ^ 2) ∂P) < ⊤ := by
    rw [hlin]
    exact ENNReal.ofReal_lt_top
  have hmeas : AEMeasurable
      (fun ω => ∑' α, ENNReal.ofReal (f α ω ^ 2)) P := AEMeasurable.ennreal_tsum hm
  filter_upwards [ae_lt_top' hmeas hfinite.ne] with ω hω
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal hω.ne

private theorem fp81s21_oscDualCoordOf_aestronglyMeasurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {d : ℕ} {m : ℝ} (f : MultiIndex d → Ω → ℝ)
    (hf : ∀ α, AEStronglyMeasurable (f α) P)
    (hs : ∀ᵐ ω ∂P, Summable (fun α => f α ω ^ 2)) :
    AEStronglyMeasurable (fun ω => fp81s21_oscDualCoordOf m (fun α => f α ω)) P := by
  let inc : MultiIndex d → ℝ →L[ℝ] OscDual d m := fun α =>
    lp.singleContinuousLinearMap (𝕜 := ℝ)
      (E := fun _ : MultiIndex d => ℝ) 2 α
  refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset (MultiIndex d)))
    (f := fun S ω => ∑ α ∈ S, inc α (f α ω)) ?_ ?_
  · intro S
    exact Finset.aestronglyMeasurable_fun_sum S fun α _ =>
      (inc α).continuous.comp_aestronglyMeasurable (hf α)
  · filter_upwards [hs] with ω hω
    have hm : Memℓp (fun α => f α ω) 2 := fp81s21_oscDual_mem_iff.mpr hω
    have he : fp81s21_oscDualCoordOf m (fun α => f α ω) =
        (⟨fun α => f α ω, hm⟩ : lp (fun _ : MultiIndex d => ℝ) 2) := by
      unfold fp81s21_oscDualCoordOf
      exact dif_pos hm
    rw [he]
    exact lp.hasSum_single (by norm_num) (⟨fun α => f α ω, hm⟩ : OscDual d m)

theorem fp81s21_oscDual_of_coordinates
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {d : ℕ} {m : ℝ} (f : MultiIndex d → Ω → ℝ)
    (hf : ∀ α, MemLp (f α) 2 P)
    (hS : Summable (fun α => ∫ ω, f α ω ^ 2 ∂P)) :
    ∃ q : Ω → OscDual d m, Measurable q ∧ MemLp q 2 P ∧
      (∀ᵐ ω ∂P, ∀ α, OscDual.coord (q ω) α = f α ω) ∧
      (∫ ω, ‖q ω‖ ^ 2 ∂P) = ∑' α, ∫ ω, f α ω ^ 2 ∂P := by
  obtain ⟨hlin, hsum⟩ := fp81s21_scalar_square_tonelli P f hf hS
  let q0 : Ω → OscDual d m := fun ω =>
    fp81s21_oscDualCoordOf m (fun α => f α ω)
  have hq0 : AEStronglyMeasurable q0 P :=
    fp81s21_oscDualCoordOf_aestronglyMeasurable f
      (fun α => (hf α).aestronglyMeasurable) hsum
  have hnorm : ∀ᵐ ω ∂P, ‖q0 ω‖ₑ ^ (2 : ℝ) =
      ∑' α, ENNReal.ofReal (f α ω ^ 2) := by
    filter_upwards [hsum] with ω hω
    rw [fp81s21_oscDual_enorm_sq, fp81s21_oscDual_norm_sq]
    have he : (fun α => OscDual.coord (q0 ω) α ^ 2) =
        (fun α => f α ω ^ 2) := by
      funext α
      rw [fp81s21_oscDualCoordOf_apply hω]
    rw [he]
    exact ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hω
  have hfinite : (∫⁻ ω, ‖q0 ω‖ₑ ^ (2 : ℝ) ∂P) < ⊤ := by
    rw [lintegral_congr_ae hnorm, hlin]
    exact ENNReal.ofReal_lt_top
  have hqLp : MemLp q0 2 P := by
    change eLpNorm q0 2 P < ⊤
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hq0).2
    simpa only [ENNReal.toReal_ofNat] using hfinite
  have hnormInt : (∫ ω, ‖q0 ω‖ ^ 2 ∂P) =
      ∑' α, ∫ ω, f α ω ^ 2 ∂P := by
    have he : ENNReal.ofReal (∫ ω, ‖q0 ω‖ ^ 2 ∂P) =
        ENNReal.ofReal (∑' α, ∫ ω, f α ω ^ 2 ∂P) := by
      calc
        _ = ∫⁻ ω, ENNReal.ofReal (‖q0 ω‖ ^ 2) ∂P :=
          ofReal_integral_eq_lintegral_ofReal
            ((memLp_two_iff_integrable_sq_norm hq0).1 hqLp)
            (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        _ = ∫⁻ ω, ‖q0 ω‖ₑ ^ (2 : ℝ) ∂P := by
          simp_rw [fp81s21_oscDual_enorm_sq]
        _ = _ := (lintegral_congr_ae hnorm).trans hlin
    have ht := congrArg ENNReal.toReal he
    simpa only [ENNReal.toReal_ofReal
      (integral_nonneg fun _ => sq_nonneg _),
      ENNReal.toReal_ofReal (tsum_nonneg fun _ =>
        integral_nonneg fun _ => sq_nonneg _)] using ht
  let q : Ω → OscDual d m := hq0.mk q0
  have hqq : q =ᵐ[P] q0 := hq0.ae_eq_mk.symm
  refine ⟨q, hq0.stronglyMeasurable_mk.measurable,
    (memLp_congr_ae hq0.ae_eq_mk).1 hqLp, ?_, ?_⟩
  · filter_upwards [hqq, hsum] with ω hω hωsum α
    rw [hω]
    exact fp81s21_oscDualCoordOf_apply hωsum α
  · exact (integral_congr_ae
      (hqq.fun_comp (fun z : OscDual d m => ‖z‖ ^ 2))).trans hnormInt

#print axioms fp81s21_oscDual_of_coordinates

end HRS.Fp81.S21

end
