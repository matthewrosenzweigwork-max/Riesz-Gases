import HRS.MC.CepN6Aux6

/-!
# Packet CEPN6 (aux 7): clamped filtration, clamped process, measurability of "exists" events
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal Classical

noncomputable section

namespace HRS.MC.CepN6

open HRS HRS.MC.CepN4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {N : ℕ}

/-- The filtration `u ↦ ℱ (max u 0)`: adaptedness at *all* real times. -/
def n6_clampFilt (ℱ : Filtration ℝ mΩ) : Filtration ℝ mΩ where
  seq u := ℱ (max u 0)
  mono' _ _ h := ℱ.mono (max_le_max h le_rfl)
  le' u := ℱ.le _

/-- A stopping time for the clamped filtration which is `≥ 0` is a stopping time for `ℱ`. -/
theorem n6_stopping_transfer {ℱ : Filtration ℝ mΩ} {ρ : Ω → WithTop ℝ}
    (h : IsStoppingTime (n6_clampFilt ℱ) ρ) (h0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ ρ ω) :
    IsStoppingTime ℱ ρ := by
  intro t
  by_cases ht : 0 ≤ t
  · have := h t
    have e : (n6_clampFilt ℱ) t = ℱ t := by
      show ℱ (max t 0) = ℱ t
      rw [max_eq_left ht]
    rw [e] at this
    exact this
  · have : {ω | ρ ω ≤ ((t : ℝ) : WithTop ℝ)} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      refine lt_of_lt_of_le ?_ (h0 ω)
      exact_mod_cast not_le.1 ht
    rw [this]
    exact @MeasurableSet.empty _ (ℱ t)

/-- The path clamped to `[0,T]` on the set `E`, constant `yb` off `E`. -/
def n6_Ypp (E : Set Ω) (Y : ℝ → Ω → Fin N → Euc 1) (T : ℝ) (yb : Fin N → Euc 1) (u : ℝ) (ω : Ω) :
    Fin N → Euc 1 :=
  if ω ∈ E then Y (min (max u 0) T) ω else yb

theorem n6_Ypp_eq {E : Set Ω} {Y : ℝ → Ω → Fin N → Euc 1} {T : ℝ} {yb : Fin N → Euc 1} {ω : Ω}
    (hω : ω ∈ E) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) T) : n6_Ypp E Y T yb u ω = Y u ω := by
  simp only [n6_Ypp, hω, ↓reduceIte]
  rw [max_eq_left hu.1, min_eq_left hu.2]

theorem n6_Ypp_off {E : Set Ω} {Y : ℝ → Ω → Fin N → Euc 1} {T : ℝ} {yb : Fin N → Euc 1} {ω : Ω}
    (hω : ω ∉ E) (u : ℝ) : n6_Ypp E Y T yb u ω = yb := by
  simp [n6_Ypp, hω]

theorem n6_Ypp_cont {E : Set Ω} {Y : ℝ → Ω → Fin N → Euc 1} {T : ℝ} {yb : Fin N → Euc 1}
    (hT : 0 ≤ T) (hE : ∀ ω ∈ E, ContinuousOn (fun s => Y s ω) (Set.Icc 0 T)) (ω : Ω) :
    Continuous fun u => n6_Ypp E Y T yb u ω := by
  by_cases hω : ω ∈ E
  · have hcl : Continuous fun u : ℝ => min (max u 0) T :=
      (continuous_id.max continuous_const).min continuous_const
    have hmem : ∀ u : ℝ, min (max u 0) T ∈ Set.Icc (0 : ℝ) T := fun u =>
      ⟨le_min (le_max_right _ _) hT, min_le_right _ _⟩
    have : Continuous fun u : ℝ => Y (min (max u 0) T) ω :=
      (hE ω hω).comp_continuous hcl hmem
    simpa [n6_Ypp, hω] using this
  · simp only [n6_Ypp, hω, ↓reduceIte]
    exact continuous_const

theorem n6_Ypp_adapted {ℱ : Filtration ℝ mΩ} {E : Set Ω} {Y : ℝ → Ω → Fin N → Euc 1} {T : ℝ}
    {yb : Fin N → Euc 1} (hT : 0 ≤ T) (hE : MeasurableSet[ℱ 0] E) (hY : Adapted ℱ Y) :
    Adapted (n6_clampFilt ℱ) (n6_Ypp E Y T yb) := by
  intro u
  show Measurable[ℱ (max u 0)] (fun ω => if ω ∈ E then Y (min (max u 0) T) ω else yb)
  have hle : min (max u 0) T ≤ max u 0 := min_le_left _ _
  refine Measurable.ite (ℱ.mono (le_max_right u 0) _ hE) ?_ measurable_const
  exact Measurable.mono (hY _) (ℱ.mono hle) le_rfl

/-- Events `{∃ u ∈ [a,b], f u < c}` for pathwise continuous, measurable `f` are measurable. -/
theorem n6_meas_exists_lt {f : ℝ → Ω → ℝ} (hc : ∀ ω, Continuous fun u => f u ω) {a b : ℝ}
    (hm : ∀ u ∈ Set.Icc a b, Measurable (f u)) (c : ℝ) :
    MeasurableSet {ω | ∃ u ∈ Set.Icc a b, f u ω < c} := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense (Set.Icc a b)
  have : {ω | ∃ u ∈ Set.Icc a b, f u ω < c} = ⋃ s ∈ S, {ω | f (s : ℝ) ω < c} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨u, hu, hlt⟩
      have hopen : IsOpen {x : Set.Icc a b | f (x : ℝ) ω < c} :=
        isOpen_lt ((hc ω).comp continuous_subtype_val) continuous_const
      obtain ⟨s, hsS, hs⟩ := hSd.exists_mem_open hopen ⟨⟨u, hu⟩, hlt⟩
      exact ⟨s, hsS, hs⟩
    · rintro ⟨s, -, hs⟩
      exact ⟨s, s.2, hs⟩
  rw [this]
  exact MeasurableSet.biUnion hSc fun s _ => measurableSet_lt (hm s s.2) measurable_const

end HRS.MC.CepN6
