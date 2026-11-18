import HRS.MC.S7PIDefs
import HRS.MC.S7PIG4Aux
import HRS.MC.S7PIG1
import HRS.MC.S7PIG3
import HRS.MC.S7PIS1Drift
import HRS.MC.S7PIS1Path2
import HRS.MC.S7PIL1
import HRS.Sections.Q17Aux3

/-!
# Packet piG4 (PI-G4): the drift Riemann-Stieltjes integral, removal of the projection

`s7_PIG_RS_drift_proof`.  Route: `measure_projection_proof` with `E = X`, `F s = driftInc b 0 s`,
`A τ = D u_Φ(τ, 𝖳_τ w)`, `A_L τ = projHeatD γ Φ (Pj L) 1 τ (𝖳_τ w)` (G3), the identification of the sums
by `s7_PIG_proj_deriv_proof` (G1), and the bounds by `s7_PIS_drift_facts_proof` (S3).
Namespace `HRS.MC.Sec7.S7PIG4`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIG4

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

/-- completeness of the path space (local instance) -/
local instance S7PIG4_complete {m T : ℝ} : CompleteSpace (PathSpace d m T) :=
  inferInstanceAs (CompleteSpace C(Set.Icc (0 : ℝ) T, NegSobolev d m))

/-- the first derivative as a continuous linear form -/
theorem S7PIG4_curry_iter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (x : E) :
    continuousMultilinearCurryFin1 ℝ E ℝ (iteratedFDeriv ℝ 1 f x) = fderiv ℝ f x := by
  ext δ
  simp [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]

theorem s7_PIG_RS_drift_proof (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (γ : ℝ → Measure (PathSpace d m T)) (hγ : ∀ u ∈ Set.Icc (0 : ℝ) T, IsFutureGaussian R.D R.ρ m T u (γ u))
    (hγp : ∀ u, IsProbabilityMeasure (γ u)) (Pj : ℕ → (PathSpace d m T →L[ℝ] PathSpace d m T))
    (hPj : ∀ L w, Pj L w = projPoly m T hT.le L w) (hP1 : ∀ L, ‖Pj L‖ ≤ 1)
    (hconv : ∀ w, Tendsto (fun L => Pj L w) atTop (𝓝 w)) :
    ∃ C : ℝ, ∀ Φ : PathSpace d m T → ℝ, MemCb 5 Φ → ∀ (w : PathSpace d m T) (b : ℝ → NegSobolev d m),
      MemLp b 1 (volume.restrict (Set.Icc (0 : ℝ) T)) →
      ∃ I : ℝ, IsRS T (fun τ a b' => fderiv ℝ (heatFn γ Φ τ) (predicted R.D R.ρ w τ)
          (driftInc R.D R.ρ m T b a b')) I ∧ |I| ≤ C * cbNorm 5 Φ * ∫ u in Set.Ioc 0 T, ‖b u‖ ∧
        ∃ IL : ℕ → ℝ, (∀ L, IsRS T (fun τ a b' => fderiv ℝ (heatFn γ (fun x => Φ (Pj L x)) τ)
            (predicted R.D R.ρ w τ) (driftInc R.D R.ρ m T b a b')) (IL L)) ∧
          (∀ L, |IL L| ≤ C * cbNorm 5 Φ * ∫ u in Set.Ioc 0 T, ‖b u‖) ∧ Tendsto IL atTop (𝓝 I) := by
  obtain ⟨C0, hC0⟩ := HRS.MC.Sec7.S7PIS1.s7_PIS_drift_facts_proof R m hm T hT
  have hpath := (HRS.MC.Sec7.S7PIS1.s7_PIS_path_facts_proof R m hm T hT).2.2
  refine ⟨max C0 0, fun Φ hΦ w b hb => ?_⟩
  obtain ⟨-, hadd, hbd, hF0, hBV⟩ := hC0 b hb
  set Y : ℝ → PathSpace d m T := fun τ => predicted R.D R.ρ w τ with hYdef
  have hY : ContinuousOn Y (Set.Icc 0 T) := continuousOn_iff_continuous_domRestrict.2 (hpath w)
  obtain ⟨hc1, hc2, hc3⟩ := HRS.MC.Sec7.S7PIG3.s7_PIG_conv_equicont_proof R m hm T hT γ hγ hγp Pj hPj hP1 hconv
    hΦ Y hY 1 (by norm_num)
  have hK0 : 0 ≤ cbNorm 5 Φ := HRS.MC.Sec7.S7PIL.S7PIL_cbNorm_nonneg hΦ 0
  set Cv := continuousMultilinearCurryFin1 ℝ (PathSpace d m T) ℝ with hCv
  set A : ℝ → (PathSpace d m T →L[ℝ] ℝ) := fun τ => Cv (iteratedFDeriv ℝ 1 (heatFn γ Φ τ) (Y τ)) with hA
  set AL : ℕ → ℝ → (PathSpace d m T →L[ℝ] ℝ) := fun L τ => Cv (projHeatD γ Φ (Pj L) 1 τ (Y τ)) with hAL
  have hAc : ContinuousOn A (Set.Icc 0 T) := Cv.continuous.comp_continuousOn hc1
  have hALc : ∀ L, ContinuousOn (AL L) (Set.Icc 0 T) := fun L => Cv.continuous.comp_continuousOn (hc2 L)
  have hAu : ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ L ≥ L₀, ∀ u ∈ Set.Icc (0 : ℝ) T, ‖AL L u - A u‖ ≤ ε := by
    intro ε hε
    obtain ⟨L₀, hL₀⟩ := hc3 ε hε
    refine ⟨L₀, fun L hL u hu => ?_⟩
    have := hL₀ L hL u hu
    simp only [hA, hAL]
    rw [← map_sub, LinearIsometryEquiv.norm_map]
    exact this
  obtain ⟨I, hI, IL, hIL, hlim⟩ := measure_projection_proof Pj 1 hP1 hconv T hT
    (fun s => driftInc R.D R.ρ m T b 0 s) hBV hF0 A AL hAc hALc hAu
  -- the increments
  have hinc : ∀ a b', 0 ≤ a → a ≤ b' → b' ≤ T →
      driftInc R.D R.ρ m T b 0 b' - driftInc R.D R.ρ m T b 0 a = driftInc R.D R.ρ m T b a b' := by
    intro a b' ha hab hb'
    have := hadd 0 a b' le_rfl ha hab hb'
    rw [← this]; abel
  have hAeq : ∀ τ (δ : PathSpace d m T), A τ δ = fderiv ℝ (heatFn γ Φ τ) (Y τ) δ := by
    intro τ δ
    simp only [hA, hCv, S7PIG4_curry_iter]
  have hALeq : ∀ L τ (δ : PathSpace d m T), AL L τ (Pj L δ) =
      fderiv ℝ (heatFn γ (fun x => Φ (Pj L x)) τ) (Y τ) δ := by
    intro L τ δ
    have := HRS.MC.Sec7.S7PIG1.s7_PIG_proj_deriv_proof γ hγp (Pj L) hΦ 1 (by norm_num) τ (Y τ) (fun _ => δ)
    rw [iteratedFDeriv_one_apply] at this
    simp only [hAL, hCv, continuousMultilinearCurryFin1_apply]
    have e : (Fin.snoc (0 : Fin 0 → PathSpace d m T) (Pj L δ) : Fin 1 → PathSpace d m T) =
        fun _ => Pj L δ := by
      ext i; fin_cases i; simp
    rw [e, ← this]
  -- bound on the cell values of the projected sums
  have hALb : ∀ L τ, ‖AL L τ‖ ≤ cbNorm 5 Φ := by
    intro L τ
    have := hγp τ
    simp only [hAL, hCv, LinearIsometryEquiv.norm_map]
    unfold projHeatD
    have h1 : ‖∫ z, iteratedFDeriv ℝ 1 Φ (Pj L (Y τ + z)) ∂(γ τ)‖ ≤ cbNorm 5 Φ * (γ τ).real Set.univ :=
      norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun z =>
        HRS.MC.Sec7.S7PIL.S7PIL_le_cbNorm hΦ (by norm_num) _)
    simpa using h1
  have hint : IntegrableOn (fun u => ‖b u‖) (Set.Icc 0 T) := (hb.integrable le_rfl).norm
  have hCI : ∀ a b', 0 ≤ a → a ≤ b' → b' ≤ T → 0 ≤ ∫ u in Set.Ioc a b', ‖b u‖ :=
    fun a b' _ _ _ => setIntegral_nonneg measurableSet_Ioc fun _ _ => norm_nonneg _
  -- the projected integrals
  have hILT : ∀ L, IsRS T (fun τ a b' => fderiv ℝ (heatFn γ (fun x => Φ (Pj L x)) τ)
      (predicted R.D R.ρ w τ) (driftInc R.D R.ρ m T b a b')) (IL L) := by
    intro L
    refine S7PIG4_RS_congr (hIL L) fun τ a b' ha h1 h2 hb' => ?_
    show AL L τ (Pj L (driftInc R.D R.ρ m T b 0 b' - driftInc R.D R.ρ m T b 0 a)) = _
    rw [hinc a b' ha (h1.trans h2) hb', hALeq]
  have hILb : ∀ L, |IL L| ≤ max C0 0 * cbNorm 5 Φ * ∫ u in Set.Ioc 0 T, ‖b u‖ := by
    intro L
    have := S7PIG4_RS_bound hT (hILT L) (fun u => ‖b u‖) hint
      (mul_nonneg (le_max_right _ _) hK0) (c := max C0 0 * cbNorm 5 Φ) ?_
    · exact this
    intro τ a b' ha h1 h2 hb'
    have hab := h1.trans h2
    rw [← hALeq L τ]
    have hδ := hbd a b' ha hab hb'
    have hCn : 0 ≤ ∫ u in Set.Ioc a b', ‖b u‖ := hCI a b' ha hab hb'
    calc |AL L τ (Pj L (driftInc R.D R.ρ m T b a b'))|
        ≤ ‖AL L τ‖ * ‖Pj L (driftInc R.D R.ρ m T b a b')‖ := by
          rw [← Real.norm_eq_abs]; exact (AL L τ).le_opNorm _
      _ ≤ cbNorm 5 Φ * ‖driftInc R.D R.ρ m T b a b'‖ := by
          gcongr
          · exact hALb L τ
          · exact ((Pj L).le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_right (hP1 L) (norm_nonneg (driftInc R.D R.ρ m T b a b')))
      _ ≤ cbNorm 5 Φ * (max C0 0 * ∫ u in Set.Ioc a b', ‖b u‖) := by
          gcongr
          exact hδ.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hCn)
      _ = max C0 0 * cbNorm 5 Φ * ∫ u in Set.Ioc a b', ‖b u‖ := by ring
  have hIT : IsRS T (fun τ a b' => fderiv ℝ (heatFn γ Φ τ) (predicted R.D R.ρ w τ)
      (driftInc R.D R.ρ m T b a b')) I := by
    refine S7PIG4_RS_congr hI fun τ a b' ha h1 h2 hb' => ?_
    show A τ (driftInc R.D R.ρ m T b 0 b' - driftInc R.D R.ρ m T b 0 a) = _
    rw [hinc a b' ha (h1.trans h2) hb', hAeq]
  refine ⟨I, hIT, ?_, IL, hILT, hILb, hlim⟩
  exact le_of_tendsto' hlim.abs hILb

end HRS.MC.Sec7.S7PIG4

end
