import HRS.Whole.Critical
import HRS.MS.ShiftFldAux8

/-!
# S8.1 XP (reduction): `critical_whole_W2` from its `u = 0` case, by the S7.9 time-shift trick

Worker S81b, namespace `HRS.Whole.BreakdownS81`, helper prefix `s81b_`.

No path-law stationarity is needed (cf. S79P, `ShiftFldAux8`): the time-shifted data `(X_u, W_{u+·} - W_u, X_{u+·})` of a canonical
realization are again a canonical realization (`s81b_isCanonical_shift`: Brownian, independent initial datum with the Gibbs law,
strong solution on every horizon, a filtered form with the filtration `r ↦ ℱ_{u + max r 0}`, and the same invariance field), and
its window `ζ_N^{0+·}` is the window `ζ_N^{u+·}` of `X` (`s79p_zetaPathW_shift`).  Hence
`s81b_W2_of_zero : S81bW2Zero → critical_whole_W2`, where `S81bW2Zero` is the frozen statement restricted to the window start `u = 0`.
-/

set_option autoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.Whole.BreakdownS81

open HRS.Whole.S79

/-- The filtration `r ↦ ℱ_{u + max r 0}` (constant on negative times, as the shifted process is). -/
def s81b_shiftFil {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ mΩ) (u : ℝ≥0) :
    Filtration ℝ mΩ where
  seq r := ℱ ((u : ℝ) + max r 0)
  mono' _ _ hst := ℱ.mono (by have := max_le_max_right (0 : ℝ) hst; linarith)
  le' _ := ℱ.le _

theorem s81b_shiftFil_coe {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ mΩ) (u t : ℝ≥0) :
    s81b_shiftFil ℱ u (t : ℝ) = HRS.MD.EQLawPath.shiftFil ℱ u t := by
  have : max (t : ℝ) 0 = t := max_eq_left t.2
  simp [s81b_shiftFil, HRS.MD.EQLawPath.shiftFil, this]

theorem s81b_isBrownianFiltration_shift {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Fintype ι]
    {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ} (hW : IsBrownianFiltration P ℱ W)
    (u : ℝ≥0) : IsBrownianFiltration P (s81b_shiftFil ℱ u) (HRS.MD.EQLawPath.shiftProc W u) := by
  have h := HRS.MD.EQLawPath.isBrownianFiltration_shift hW u
  refine ⟨?_, ?_, h.zero, h.cont, ?_, h.gaussian_incr⟩
  · intro t s hs h0
    exact hW.complete _ s hs h0
  · intro t
    rw [s81b_shiftFil_coe]
    exact h.adapted t
  · intro s t hst
    rw [s81b_shiftFil_coe]
    exact h.indep_incr s t hst

theorem s81b_filtered_shift {Ω : Type} {mΩ : MeasurableSpace Ω} {N d : ℕ} {P : Measure Ω}
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → EucConfig d N} (h : IsWholeFilteredSolution P ℱ W' W X) (u : ℝ≥0) :
    IsWholeFilteredSolution P (s81b_shiftFil ℱ u) (HRS.MD.EQLawPath.shiftProc W' u)
      (s79p_shiftW u W) (s79p_shiftX u X) := by
  refine ⟨s81b_isBrownianFiltration_shift h.brownian u, ?_, ?_, ?_⟩
  · filter_upwards [h.coords] with ζ hζ
    intro t i j
    simp [HRS.MD.EQLawPath.shiftProc, s79p_shiftW, hζ]
  · intro t
    rw [s81b_shiftFil_coe]
    exact h.adapted (u + t)
  · intro i
    have hp := h.progressive ((u : ℝ) + max i 0)
    change Measurable[(Subtype.instMeasurableSpace (p := fun x : ℝ => x ∈ Set.Iic i)).prod
      (ℱ ((u : ℝ) + max i 0))] _
    let ψ : Set.Iic i × Ω → Set.Iic ((u : ℝ) + max i 0) × Ω := fun p =>
      (⟨(u : ℝ) + max (p.1 : ℝ) 0, by
        have h1 : (p.1 : ℝ) ≤ i := p.1.2
        have := max_le_max_right (0 : ℝ) h1
        simp only [Set.mem_Iic]
        linarith⟩, p.2)
    have hψ : Measurable[(Subtype.instMeasurableSpace (p := fun x : ℝ => x ∈ Set.Iic i)).prod
        (ℱ ((u : ℝ) + max i 0)), (Subtype.instMeasurableSpace (p := fun x : ℝ =>
          x ∈ Set.Iic ((u : ℝ) + max i 0))).prod (ℱ ((u : ℝ) + max i 0))] ψ := by
      refine Measurable.prodMk ?_ measurable_snd
      refine Measurable.subtype_mk ?_
      exact (measurable_const.add ((measurable_subtype_coe.comp measurable_fst).max measurable_const))
    convert hp.comp hψ using 1
    funext p
    simp only [Function.comp, ψ, ofNNRealTime_apply, s79p_shiftX]
    rw [Real.toNNReal_add u.coe_nonneg (le_max_right _ _), Real.toNNReal_coe]
    simp [Real.toNNReal]

theorem s81b_isCanonical_shift {d N : ℕ} {s a β : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → EucConfig d N} (hR : IsCanonicalRealization d s a β N P X₀ W X) (u : ℝ≥0) :
    IsCanonicalRealization d s a β N P (X u) (s79p_shiftW u W) (s79p_shiftX u X) where
  brownian := s79p_isVectorBrownian_shift hR.brownian u
  indep := s79p_indep_shift hR u
  init := s79p_law_init hR u
  solution := fun T' => s79p_strongSolution_shift hR u T'
  filtered := by
    obtain ⟨ℱ, W', hbf⟩ := hR.filtered
    exact ⟨s81b_shiftFil ℱ u, HRS.MD.EQLawPath.shiftProc W' u, s81b_filtered_shift hbf u⟩
  invariant := hR.invariant

/-- The frozen statement `critical_whole_W2`, restricted to the window start `u = 0` (stationary realizations
started from the canonical law). -/
def S81bW2Zero : Prop :=
  ∀ {d : ℕ}, 2 ≤ d → ∀ (a β : ℝ), 0 < a → 0 < β → ∀ (m : ℝ), (wholeSpaceIndex d : ℝ) ≤ m →
    ∀ T : ℝ, 0 < T →
    ∃ C : ℝ, ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
        IsCanonicalRealization d ((d : ℝ) / 2) a β N P X₀ W X →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → OscDual d m),
        IsStationaryGaussianField d ((d : ℝ) / 2) a β m ρβ P' Z →
        AEMeasurable (processWindow m T 0 Z) P' ∧
          AEMeasurable (zetaPathW m T 0 P X) P ∧
          wassersteinE 2 (law P (zetaPathW m T 0 P X)) (law P' (processWindow m T 0 Z)) ≤
            ENNReal.ofReal (C * (N : ℝ) ^ (-(1 / 2 : ℝ)))

/-- XP reduction: the centered path bound uniform in `u ≥ 0` follows from its `u = 0` case. -/
theorem s81b_W2_of_zero (h0 : S81bW2Zero) : type_of% @HRS.Whole.critical_whole_W2 := by
  intro d hd a β ha hβ m hm T hT
  obtain ⟨C, hC⟩ := h0 hd a β ha hβ m hm T hT
  refine ⟨C, fun ρβ hρβ N hN Ω _ P _ X₀ W X hR Ω' _ P' _ Z hZ => ?_⟩
  refine ⟨(hC ρβ hρβ N hN P X₀ W X hR P' Z hZ).1, fun u hu => ?_⟩
  have hR' := s81b_isCanonical_shift hR u.toNNReal
  obtain ⟨-, hm1, hw⟩ := hC ρβ hρβ N hN P _ _ _ hR' P' Z hZ
  have hz : zetaPathW m T 0 P (s79p_shiftX u.toNNReal X) = zetaPathW m T u P X :=
    funext fun ζ => (s79p_zetaPathW_shift P T X hu ζ).symm
  rw [hz] at hm1 hw
  exact ⟨hm1, hw⟩

end HRS.Whole.BreakdownS81
