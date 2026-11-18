import HRS.Main.GFB1Aux2

/-! A simultaneous measurable modification from dense-time measurability. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set

namespace HRS.Fp81.S21

/-- Measurability at a countable dense set and almost sure path continuity
provide one measurable modification agreeing at every time on a single event. -/
theorem fp81s21_dense_measurable_continuous_version
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) (H : ℝ) (Z : Ω → ℝ → E)
    (s : Set (Icc (0 : ℝ) H)) (hs : s.Countable) (hd : Dense s)
    (hm : ∀ t ∈ s, AEMeasurable (fun ω => Z ω t) P)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (Z ω) (Icc 0 H)) :
    ∃ Z' : Ω → ℝ → E, (∀ t, Measurable (fun ω => Z' ω t)) ∧
      (∀ ω, ContinuousOn (Z' ω) (Icc 0 H)) ∧
      ∀ᵐ ω ∂P, ∀ t ∈ Icc (0 : ℝ) H, Z' ω t = Z ω t := by
  classical
  have hall : ∀ t ∈ Icc (0 : ℝ) H, AEMeasurable (fun ω => Z ω t) P := by
    intro t ht
    let x : Icc (0 : ℝ) H := ⟨t, ht⟩
    have hx : x ∈ closure s := by rw [hd.closure_eq]; exact Set.mem_univ _
    obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hx
    apply aemeasurable_of_tendsto_metrizable_ae' (fun n => hm (u n) (hu n))
    filter_upwards [hc] with ω hω
    exact (hω.restrict.continuousAt.tendsto).comp hlim
  obtain ⟨Y, hYm, hYc, hYeq⟩ := HRS.GF.gf_measurable_modification_proof P H
    (fun t ω => Z ω t) hc hall
  have heq : ∀ᵐ ω ∂P, ∀ t ∈ s, Y t ω = Z ω t :=
    (ae_ball_iff hs).2 fun t _ => hYeq t t.2
  refine ⟨fun ω t => Y t ω, hYm, hYc, ?_⟩
  filter_upwards [heq, hc] with ω hω hcont
  have h : (fun t : Icc (0 : ℝ) H => Y t ω) = (fun t : Icc (0 : ℝ) H => Z ω t) :=
    Continuous.ext_on hd (hYc ω).restrict hcont.restrict (fun t ht => hω t ht)
  intro t ht
  exact congrFun h ⟨t, ht⟩

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_dense_measurable_continuous_version
