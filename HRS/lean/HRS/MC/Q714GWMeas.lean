import HRS.MD.EQGaussWindow
import HRS.Sections.Sec7Setting

/-!
# Packet GW (row 7.14): measurability of the window path

For an `E_m`-valued process with measurable evaluations and a.s. continuous paths on `[0,∞)` the window `procWin m T a Z` is a.e.
measurable into `𝒳_{m,T}` (cylinder sets generate the Borel σ-algebra, `eqgw_borel_eq_generateFrom`), and it is a.s. the honest path.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal

namespace HRS.MC.Q714.GW

open HRS HRS.Sec7 HRS.MD.EQGaussWindow

variable {d : ℕ}

/-- `procWin` is the window path of `HRS.Main.windowPath`. -/
theorem gw_procWin_eq {Ω : Type} (m T a : ℝ) (Z : ℝ → Ω → NegSobolev d m) :
    procWin m T a Z = Main.windowPath m T a Z := rfl

/-- On a trajectory continuous on `[0,∞)` the window path is the honest path. -/
theorem gw_procWin_at {Ω : Type} {m : ℝ} (T a : ℝ) (ha : 0 ≤ a) (Z : ℝ → Ω → NegSobolev d m) (ω : Ω)
    (hc : ContinuousOn (fun t => Z t ω) (Set.Ici 0)) (t : Set.Icc (0 : ℝ) T) :
    (procWin m T a Z ω).at' t = Z (a + t) ω :=
  eqgw_windowPath_at T a ha Z ω hc t

/-- Continuity on every `[0,T]` gives continuity on `[0,∞)`. -/
theorem gw_continuousOn_Ici {E : Type*} [TopologicalSpace E] {f : ℝ → E}
    (h : ∀ T : ℝ, ContinuousOn f (Set.Icc 0 T)) : ContinuousOn f (Set.Ici 0) := by
  intro x hx
  have hx' : 0 ≤ x := hx
  have hmem : Set.Icc (0 : ℝ) (x + 1) ∈ 𝓝[Set.Ici 0] x := by
    refine Filter.mem_of_superset (inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith : x < x + 1))) ?_
    intro y hy
    exact ⟨hy.1, hy.2⟩
  exact (h (x + 1) x ⟨hx', by linarith⟩).mono_of_mem_nhdsWithin hmem

/-- A.e. measurability of the window path. -/
theorem gw_aemeasurable {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {m : ℝ} (T a : ℝ) (ha : 0 ≤ a) (Z : ℝ → Ω → NegSobolev d m) (hmeas : ∀ t, Measurable (Z t))
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Ici 0)) :
    AEMeasurable (procWin m T a Z) P := by
  classical
  have hnull : P {ω | ¬ ContinuousOn (fun t => Z t ω) (Set.Ici 0)} = 0 := ae_iff.1 hcont
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null hnull
  set f : Ω → PathSpace d m T := procWin m T a Z with hf
  set f' : Ω → PathSpace d m T := fun ω => if ω ∈ Nᶜ then f ω else 0 with hf'
  have hgood : ∀ ω ∈ Nᶜ, ContinuousOn (fun t => Z t ω) (Set.Ici 0) := by
    intro ω hω
    by_contra h
    exact hω (hNsub h)
  have hae : f =ᵐ[P] f' := by
    have : ∀ᵐ ω ∂P, ω ∈ Nᶜ := by
      rw [ae_iff]
      simpa using hN0
    filter_upwards [this] with ω hω
    show f ω = f' ω
    simp only [hf']
    exact (if_pos hω).symm
  have hG' : ∀ (p : ℕ) (ts : Fin p → Set.Icc (0 : ℝ) T) (φ : Fin p → Torus d → ℝ),
      (∀ i, Torus.IsSmooth (φ i)) →
      Measurable fun ω => eqgwG ts φ (f' ω) := by
    intro p ts φ hφ
    have hm : Measurable fun ω => (WithLp.toLp 2 fun i => NegSobolev.eval (Z (a + (ts i : ℝ)) ω) (φ i) :
        EuclideanSpace ℝ (Fin p)) := by
      refine (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 fun i => ?_)
      exact (eqgw_eval_continuous (hφ i)).measurable.comp (hmeas _)
    have : (fun ω => eqgwG ts φ (f' ω)) = fun ω => if ω ∈ Nᶜ then
        (WithLp.toLp 2 fun i => NegSobolev.eval (Z (a + (ts i : ℝ)) ω) (φ i) :
          EuclideanSpace ℝ (Fin p)) else eqgwG ts φ (0 : PathSpace d m T) := by
      funext ω
      by_cases hω : ω ∈ Nᶜ
      · simp only [hf', if_pos hω]
        unfold eqgwG
        simp only [hf]
        congr 1
        funext i
        rw [gw_procWin_at T a ha Z ω (hgood ω hω)]
      · simp only [hf', if_neg hω]
    rw [this]
    exact Measurable.ite hNm.compl hm measurable_const
  have hmeas' : Measurable f' := by
    have h1 : @Measurable _ _ _ (MeasurableSpace.generateFrom (eqgwCyl d m T)) f' := by
      refine measurable_generateFrom ?_
      rintro S ⟨p, ts, φ, B, hφ, hB, rfl⟩
      exact hG' p ts φ hφ hB
    exact h1.mono le_rfl (by rw [← eqgw_borel_eq_generateFrom])
  exact hmeas'.aemeasurable.congr hae.symm

end HRS.MC.Q714.GW
