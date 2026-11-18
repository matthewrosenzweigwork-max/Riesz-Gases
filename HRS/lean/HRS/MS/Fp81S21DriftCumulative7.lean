import HRS.MS.R2InterpAux104

/-! Almost-everywhere measurable oscillator duals from their coordinates. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS.Whole HRS.MS.R2Interp

/-- A family of oscillator duals is a.e. measurable if each of its countably
many coordinates is a.e. measurable. -/
theorem fp81s21_oscDual_aemeasurable_of_coordinates
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ} {m : ℝ}
    (F : Ω → OscDual d m)
    (hm : ∀ α : MultiIndex d, AEMeasurable (fun ω => OscDual.coord (F ω) α) P) :
    AEMeasurable F P := by
  classical
  let a : MultiIndex d → Ω → ℝ := fun α => (hm α).mk _
  have ha : ∀ α, Measurable (a α) := fun α => (hm α).measurable_mk
  have he : ∀ᵐ ω ∂P, ∀ α, OscDual.coord (F ω) α = a α ω :=
    ae_all_iff.mpr fun α => (hm α).ae_eq_mk
  obtain ⟨B, hsub, hBm, hB0⟩ := exists_measurable_superset_of_null (ae_iff.mp he)
  let G : Ω → OscDual d m := fun ω => if ω ∈ B then 0 else F ω
  have hg : ∀ ω α, OscDual.coord (G ω) α = if ω ∈ B then 0 else a α ω := by
    intro ω α
    by_cases hω : ω ∈ B
    · simp only [G, hω, if_pos]
      change (0 : lp (fun _ : MultiIndex d => ℝ) 2) α = 0
      exact congrFun (lp.coeFn_zero _ _) α
    · have hgood : ∀ α, OscDual.coord (F ω) α = a α ω := by
        by_contra h
        exact hω (hsub h)
      simp [G, hω, hgood α]
  have hmem : ∀ ω, Memℓp (fun α => OscDual.coord (G ω) α) 2 := fun ω =>
    lp.memℓp (show lp (fun _ : MultiIndex d => ℝ) 2 from G ω)
  have hG : Measurable G := by
    have hG' : G = fun ω => (show OscDual d m from
        (⟨fun α => OscDual.coord (G ω) α, hmem ω⟩ : lp (fun _ : MultiIndex d => ℝ) 2)) := by
      funext ω
      rfl
    rw [hG']
    apply s102_measurable_lp _ hmem
    intro α
    simp_rw [hg]
    exact Measurable.ite hBm measurable_const (ha α)
  refine ⟨G, hG, ?_⟩
  have hnot : ∀ᵐ ω ∂P, ω ∉ B := by
    rw [ae_iff]; simpa using hB0
  filter_upwards [hnot] with ω hω
  simp [G, hω]

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_oscDual_aemeasurable_of_coordinates
