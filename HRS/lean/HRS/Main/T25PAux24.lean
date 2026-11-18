import HRS.Main.T25PAux23

/-!
# T25P, part 24: the enlarged comparison (coupling + core estimate) for the prepared data of Theorem 2.5
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Complex
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.Main

variable {d : ℕ}

/-- `a.s.` continuity of the fluctuation process on `[0, a+T]` (from the mild decomposition). -/
theorem t25p_fluc_cont (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {m : ℝ}
    (hm : (d : ℝ) + 2 < m) {T : ℝ} (hT : 0 < T) {Cr cr : ℝ} (hCr : 0 < Cr) (hcr : 0 < cr) {Cmax : ℝ}
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m} (hdual : IsDualEvolution htr.dyn ρ m Vev)
    (hEv : T25Ev m Cr cr T Cmax Vev) {N : ℕ} (hN : 2 ≤ N) {a : ℝ} (ha : 0 ≤ a)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsParticleSystem P htr.dyn (a + T) X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsFilteredSolution P ℱ W' W X) :
    ∀ᵐ ω ∂P, ContinuousOn (fun t => flucProc m (Real.sqrt N) X ρ t ω) (Set.Icc 0 (a + T)) := by
  obtain ⟨Mart, Z, hM, hZS, hZc, hZm, hRc, hRm, hRb⟩ :=
    t25p_stage1 hd htr hm hT hCr hcr hdual hEv hN ha P X₀ W X hX ℱ W' hF
  have hT' : 0 < a + T := by linarith
  have hplain := hEv.plain (a + T) hT'.le
  filter_upwards [hZc, hRc] with ω h1 h2
  have h3 := (HRS.Uniform.Comp28.continuousOn_V_zero Vev hplain.2.2
    (flucProc m (Real.sqrt N) X ρ 0 ω))
  have := (h2.add h3).add h1
  refine this.congr fun t _ => ?_
  simp only [Pi.add_apply]
  abel

/-- The initial field map `x ↦ η_N^0(x) = √N(μ_N(x) - μ°)`. -/
theorem t25p_etaE_measurable (S : PreparedData d) (m : ℝ) (hm0 : (d : ℝ) / 2 < m) (N : ℕ) :
    Measurable (fun x : Config d N => etaE m x S.μ0) :=
  (gf_measurable_ofMeasureDiff_proof (N := N) m hm0 S.μ0).const_smul (Real.sqrt N)

/-- The law of a window of the pulled-back process equals the law of the window. -/
theorem t25p_law_pullback {Ω Ω' B : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace B]
    {P : Measure Ω} {P' : Measure Ω'} {π : Ω' → Ω} (hπ : MeasurePreserving π P' P) {F : Ω → B}
    (hF : AEMeasurable F P) : P'.map (fun ω' => F (π ω')) = P.map F := by
  have : AEMeasurable F (P'.map π) := by rw [hπ.map_eq]; exact hF
  rw [← hπ.map_eq]
  exact (AEMeasurable.map_map_of_aemeasurable this hπ.aemeasurable).symm

end HRS.T25P
