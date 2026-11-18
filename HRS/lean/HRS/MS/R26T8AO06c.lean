import HRS.MS.R26T8AO06b

/-!
# S8.2 T8A O06 (part c): exit times from the exhaustion, started inside the open set
`tau Y V A` is the exit time of the path `Y` from `V` on the event `A ∈ ⋂ ℱ i` (where `Y 0 ∈ V`), and `-1` off `A`;
it is a stopping time, the path is in `closure V` up to it, and it exceeds `T` when the path stays in `V` on `[0,T]`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T8A
open HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {E : Type*}

open Classical in
def r26t8a_o06_tau [TopologicalSpace E] (Y : ℝ → Ω → E) (V : Set E) (A : Set Ω) : Ω → WithTop ℝ :=
  fun w => if w ∈ A then exitTime Y V 0 w else ((-1 : ℝ) : WithTop ℝ)

theorem r26t8a_o06_tau_stopping [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E] (ℱ : Filtration ℝ mΩ)
    (Y : ℝ → Ω → E) (hY : Adapted ℱ Y) (hcont : ∀ w, Continuous fun t => Y t w) {V : Set E} (hV : IsOpen V)
    {A : Set Ω} (hA : ∀ i, MeasurableSet[ℱ i] A) : IsStoppingTime ℱ (r26t8a_o06_tau Y V A) := by
  classical
  intro i
  have hE := isStoppingTime_exitTime ℱ Y hY hcont hV 0 i
  have : {w | r26t8a_o06_tau Y V A w ≤ (i : WithTop ℝ)} =
      (A ∩ {w | exitTime Y V 0 w ≤ (i : WithTop ℝ)}) ∪ (Aᶜ ∩ {_w | (((-1 : ℝ)) : WithTop ℝ) ≤ (i : WithTop ℝ)}) := by
    ext w
    by_cases h : w ∈ A <;> simp [r26t8a_o06_tau, h]
  rw [this]
  by_cases hi : (-1 : ℝ) ≤ i
  · have : {_w : Ω | (((-1 : ℝ)) : WithTop ℝ) ≤ (i : WithTop ℝ)} = Set.univ := by
      ext w; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]; exact WithTop.coe_le_coe.2 hi
    rw [this, Set.inter_univ]
    exact @MeasurableSet.union _ (ℱ i) _ _ (@MeasurableSet.inter _ (ℱ i) _ _ (hA i) hE)
      (@MeasurableSet.compl _ _ (ℱ i) (hA i))
  · have : {_w : Ω | (((-1 : ℝ)) : WithTop ℝ) ≤ (i : WithTop ℝ)} = ∅ := by
      ext w; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hi (WithTop.coe_le_coe.1 h)
    rw [this, Set.inter_empty, Set.union_empty]
    exact @MeasurableSet.inter _ (ℱ i) _ _ (hA i) hE

theorem r26t8a_o06_tau_mem [PseudoMetricSpace E] (Y : ℝ → Ω → E) {V : Set E} (hV : IsOpen V) {A : Set Ω}
    {w : Ω} (hw : w ∈ A) (h0 : Y 0 w ∈ V) (hcont : Continuous fun t => Y t w) {t : ℝ} (ht : 0 ≤ t)
    (hle : (t : WithTop ℝ) ≤ r26t8a_o06_tau Y V A w) : Y t w ∈ closure V := by
  classical
  have hle' : (t : WithTop ℝ) ≤ exitTime Y V 0 w := by simpa [r26t8a_o06_tau, hw] using hle
  rcases lt_or_eq_of_le hle' with hlt | heq
  · exact subset_closure (mem_of_lt_exitTime Y V 0 w t ht hlt)
  · rcases eq_or_lt_of_le ht with h0t | hpos
    · rw [← h0t]; exact subset_closure h0
    · have hx : t ∈ closure (Set.Ico (0 : ℝ) t) := by
        rw [closure_Ico hpos.ne]; exact ⟨ht, le_rfl⟩
      have hsub : Set.Ico (0 : ℝ) t ⊆ (fun t => Y t w) ⁻¹' V := fun s hs =>
        mem_of_lt_exitTime Y V 0 w s hs.1 (heq ▸ (by exact_mod_cast hs.2))
      exact hcont.closure_preimage_subset V (closure_mono hsub hx)

theorem r26t8a_o06_tau_neg [TopologicalSpace E] (Y : ℝ → Ω → E) (V : Set E) {A : Set Ω} {w : Ω} (hw : w ∉ A)
    {t : ℝ} (ht : 0 ≤ t) : ¬ ((t : WithTop ℝ) ≤ r26t8a_o06_tau Y V A w) := by
  classical
  simp only [r26t8a_o06_tau, hw, if_false]
  intro h
  have : t ≤ (-1 : ℝ) := by exact_mod_cast h
  linarith

theorem r26t8a_o06_tau_gt [TopologicalSpace E] (Y : ℝ → Ω → E) {V : Set E} (hV : IsOpen V) {A : Set Ω} {w : Ω}
    (hw : w ∈ A) (hcont : Continuous fun t => Y t w) {T : ℝ} (hT : ∀ t ∈ Set.Icc (0 : ℝ) T, Y t w ∈ V) :
    (T : WithTop ℝ) ≤ r26t8a_o06_tau Y V A w := by
  classical
  simp only [r26t8a_o06_tau, hw, if_true]
  by_contra hc
  push_neg at hc
  have : exitTime Y V 0 w ≤ (T : WithTop ℝ) := hc.le
  obtain ⟨r, hr0, hrT, hr⟩ := (hittingAfter_le_iff_of_isClosed Y w hcont hV.isClosed_compl 0 T).1 this
  exact hr (hT r ⟨hr0, hrT⟩)

end HRS.MS.R26T8A

end
