import HRS.MS.Fp81S21FutureIndep41

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R2Interp

/-- A past-measurable prediction and an almost everywhere past-measurable
increment are jointly independent of the future. -/
theorem fp81s21_past_pair_independent
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] (P : Measure Ω)
    (past : Ω → A) (future : Ω → B) (hind : IndepFun past future P)
    {E : Type*} [MeasurableSpace E] (Y : Ω → E)
    (hY : Measurable[MeasurableSpace.comap past inferInstance] Y)
    (D : Ω → ℝ)
    (hD : AEStronglyMeasurable[MeasurableSpace.comap past inferInstance] D P) :
    IndepFun (fun ω => (D ω, Y ω)) future P := by
  let D' := hD.mk D
  have hpair : Measurable[MeasurableSpace.comap past inferInstance]
      (fun ω => (D' ω, Y ω)) := hD.stronglyMeasurable_mk.measurable.prodMk hY
  have hind' : IndepFun (fun ω => (D' ω, Y ω)) future P := by
    apply (IndepFun_iff _ _ _).2
    intro s t hs ht
    exact (IndepFun_iff _ _ _).1 hind s t (hpair.comap_le s hs) ht
  apply hind'.congr _ (EventuallyEq.rfl)
  filter_upwards [hD.ae_eq_mk] with ω hω
  simp [D', ← hω]

/-- Derivative conditioning for an arbitrary integrable past increment and
past-measurable prediction, with an independent future path of law `γ r`. -/
theorem fp81s21_heat_derivative_conditioning
    {d : ℕ} {m H : ℝ} {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (past : Ω → A) (Y X : Ω → OscPath d m H)
    (hY : Measurable Y) (hYpast : Measurable[MeasurableSpace.comap past inferInstance] Y)
    (hX : Measurable X) (hind : IndepFun past X P)
    (γ : ℝ → Measure (OscPath d m H)) (r : ℝ) [IsProbabilityMeasure (γ r)]
    (hlaw : P.map X = γ r)
    (Φ : OscPath d m H → ℝ) (hΦ : MemCb 5 Φ)
    (j : ℕ) (hj : j ≤ 5) (h : Fin j → OscPath d m H)
    (D : Ω → ℝ) (hD : Integrable D P)
    (hDpast : AEStronglyMeasurable[MeasurableSpace.comap past inferInstance] D P) :
    let C := (⨆ z, ‖iteratedFDeriv ℝ j Φ z‖) * ∏ i, ‖h i‖
    Integrable (fun ω => D ω * iteratedFDeriv ℝ j Φ (Y ω + X ω) h) P ∧
    Integrable (fun ω => D ω * iteratedFDeriv ℝ j (r2HeatFn γ Φ r) (Y ω) h) P ∧
    (∫ ω, D ω * iteratedFDeriv ℝ j Φ (Y ω + X ω) h ∂P) =
      ∫ ω, D ω * iteratedFDeriv ℝ j (r2HeatFn γ Φ r) (Y ω) h ∂P ∧
    ‖∫ ω, D ω * iteratedFDeriv ℝ j Φ (Y ω + X ω) h ∂P‖ ≤
      C * ∫ ω, ‖D ω‖ ∂P := by
  dsimp only
  let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => OscPath d m H) ℝ h
  let f : OscPath d m H × OscPath d m H → ℝ :=
    fun yz => iteratedFDeriv ℝ j Φ (yz.1 + yz.2) h
  have hf : Continuous f := by
    exact L.continuous.comp ((hΦ.1.continuous_iteratedFDeriv (m := j)
      (by exact_mod_cast hj)).comp (by fun_prop))
  have hb : ∀ yz, ‖f yz‖ ≤ (⨆ z, ‖iteratedFDeriv ℝ j Φ z‖) * ∏ i, ‖h i‖ := by
    intro yz
    exact ((iteratedFDeriv ℝ j Φ (yz.1 + yz.2)).le_opNorm h).trans
      (mul_le_mul_of_nonneg_right (s102_le_sup hΦ hj _) (Finset.prod_nonneg fun _ _ => norm_nonneg _))
  have hi := fp81s21_independent_past_future_integral P D hD Y X hY hX
    (fp81s21_past_pair_independent P past X hind Y hYpast D hDpast) (γ r) hlaw f hf _ hb
  obtain ⟨hform, hInt, hbound⟩ := fp81s21_heat_derivative_increment P γ r Φ hΦ j hj h Y hY D hD
  have heq : (∫ ω, D ω * iteratedFDeriv ℝ j Φ (Y ω + X ω) h ∂P) =
      ∫ ω, D ω * iteratedFDeriv ℝ j (r2HeatFn γ Φ r) (Y ω) h ∂P := by
    rw [hi.2]
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => by dsimp only [f]; rw [hform ω]
  exact ⟨hi.1, hInt, heq, heq ▸ hbound⟩

#print axioms fp81s21_past_pair_independent
#print axioms fp81s21_heat_derivative_conditioning
end HRS.Fp81.S21
end
