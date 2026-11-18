import HRS.MC.S7FCH4D

/-!
# S7FCH4E: the Gaussian-side identification and integrability of `Y` (H4, part E)
-/
open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace HRS.MC.Sec7.S7FCH4
open Classical
variable {d : ℕ}

/-- Integrability of `Y_{s,m} ∘ F` from a second moment of `F`. -/
theorem S7FCH4_Y_integrable {r T : ℝ} (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d)
    {s : ℝ} (hs : 0 ≤ s) {m : PathSpace d r T} (hm : ‖m‖ ≤ 1) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {F : Ω → PathSpace d r T} (hF : AEMeasurable F P)
    (hmom : Integrable (fun ω => ‖F ω‖ ^ 2) P) :
    Integrable (fun ω => S7FCH4_Y S K s m (F ω)) P := by
  have hmeas : AEStronglyMeasurable (fun ω => S7FCH4_Y S K s m (F ω)) P :=
    ((S7FCH4_Y_continuous S K s m).measurable.comp_aemeasurable hF).aestronglyMeasurable
  set Λ := S7FCH4_Lg r S K + S7FCH4_Lh r S K with hΛ
  have hΛ0 : 0 ≤ Λ := add_nonneg (S7FCH4_Lg_nonneg r S K) (S7FCH4_Lh_nonneg r S K)
  have hmaj : Integrable (fun ω => Λ * ((2 + 2 * (1 + s)) * (1 + ‖F ω‖ ^ 2))) P :=
    ((integrable_const (1 : ℝ)).add hmom).const_mul _ |>.const_mul _
  refine hmaj.mono' hmeas (ae_of_all _ fun ω => ?_)
  have h := S7FCH4_Y_norm_le S K hs hm (F ω)
  refine h.trans ?_
  have hm0 := norm_nonneg m
  have hx := norm_nonneg (F ω)
  refine mul_le_mul_of_nonneg_left ?_ hΛ0
  have : ‖m‖ + s ≤ 1 + s := by linarith
  calc (1 + ‖F ω‖) * (‖F ω‖ + (‖m‖ + s)) ≤ (1 + ‖F ω‖) * (‖F ω‖ + (1 + s)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    _ ≤ (2 + 2 * (1 + s)) * (1 + ‖F ω‖ ^ 2) := by nlinarith [sq_nonneg (‖F ω‖ - 1), sq_nonneg ‖F ω‖]

/-- The Gaussian-side identification: a.s. `toL2 (fcGaussAt ..) = ι(Y₀(procWin) - ∫ Y₀(procWin))`, `Y₀ = Y_{0,0}`. -/
theorem S7FCH4_gauss_id {r : ℝ} {T : ℝ} (hT : 0 < T) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (η : ℝ → Ω' → NegSobolev d r) (S : Finset (NonzeroLattice d))
    (K : NonzeroLattice d → FRKernel d) (hmeas : ∀ t, Measurable (η t))
    (hc : ∀ᵐ ω ∂P', ContinuousOn (fun t => η t ω) (Set.Icc 0 T))
    (hmom : Integrable (fun ω => ‖procWin r T 0 η ω‖ ^ 2) P')
    (hint : Integrable (fun ω => S7FCH4_Y S K 0 (0 : PathSpace d r T) (procWin r T 0 η ω)) P') :
    ∀ᵐ ω ∂P', toL2 r T (fun t => fcGaussAt r S K P' η (0 + t) ω) =
      S7FCH4_iota hT.le (S7FCH4_Y S K 0 (0 : PathSpace d r T) (procWin r T 0 η ω) -
        ∫ ω', S7FCH4_Y S K 0 (0 : PathSpace d r T) (procWin r T 0 η ω') ∂P') := by
  have hae := HRS.MC.Sec7.S7FCD5B.S7FCD5B_procWin_val P' r T η hc
  filter_upwards [hae] with ω hω
  refine S7FCH4_toL2_eq_iota hT.le _ _ fun t ht => ?_
  set tt : Set.Icc (0 : ℝ) T := ⟨t, ht⟩ with htt
  have hI : PathSpace.at' (∫ ω', S7FCH4_Y S K 0 (0 : PathSpace d r T) (procWin r T 0 η ω') ∂P') tt =
      ∫ ω', S7FCH4_gq r S K (η t ω') ∂P' := by
    rw [S7FCH4_at_integral hint tt]
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω' h
    rw [S7FCH4_at_Y, h tt, S7FCH4_at_zero]
    simp [S7FCH4_phi]
    rfl
  have hQ : ∀ k, Integrable (fun ω' => (K k).quad (η t ω')) P' := by
    intro k
    refine Integrable.mono' (hmom.const_mul (S7FCH4_qC r (K k))) ?_ ?_
    · exact ((HRS.MC.Sec7.S7FCW12.s7fcw12_quad_continuous (m := r) (K k)).measurable.comp
        (hmeas t)).aestronglyMeasurable
    · filter_upwards [hae] with ω' h
      have h1 := S7FCH4_quad_abs_le (K k) (η t ω')
      have h2 : ‖η t ω'‖ ≤ ‖procWin r T 0 η ω'‖ := by
        rw [← h tt]; exact S7FCH4_norm_at_le _ tt
      rw [Real.norm_eq_abs]
      refine h1.trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (S7FCH4_qC_nonneg r (K k))
      nlinarith [norm_nonneg (η t ω')]
  have hG : ∫ ω', S7FCH4_gq r S K (η t ω') ∂P' =
      ∑ k ∈ S, (∫ ω', (K k).quad (η t ω') ∂P') • S7FCH4_e r k := by
    unfold S7FCH4_gq
    rw [integral_finsetSum _ (fun k _ => (hQ k).smul_const _)]
    exact Finset.sum_congr rfl fun k _ => integral_smul_const _ _
  show fcGaussAt r S K P' η (0 + t) ω = PathSpace.at' (S7FCH4_Y S K 0 (0 : PathSpace d r T) (procWin r T 0 η ω) -
    ∫ ω', S7FCH4_Y S K 0 (0 : PathSpace d r T) (procWin r T 0 η ω') ∂P') tt
  rw [S7FCH4_at_sub, hI, hG, S7FCH4_at_Y, hω tt, S7FCH4_at_zero]
  unfold fcGaussAt
  simp only [zero_add, add_zero]
  rw [S7FCH4_ofSeq_sum]
  simp only [S7FCH4_phi, zero_smul, sub_zero]
  unfold S7FCH4_gq
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => (sub_smul _ _ _)

end HRS.MC.Sec7.S7FCH4
