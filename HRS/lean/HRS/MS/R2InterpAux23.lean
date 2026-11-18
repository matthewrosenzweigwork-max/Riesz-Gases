import HRS.MS.R2InterpAux22
import HRS.MC.S7PIG4Aux

/-!
# S10.2 (worker S102), part 23 (packet G4): the drift Riemann--Stieltjes integral, removal of the projection

Whole-space port of `s7_PIG_RS_drift_proof`: `measure_projection_proof` with `E = 𝒳`, `F s = r2DriftInc b 0 s`, `A τ = Du_Φ(τ,Y_τ)`,
`A_L τ = projHeatD Φ P_L 1 τ Y_τ` (G3), the identification of the sums by `s102_proj_deriv` (G1), and the bounds from the drift facts
(`s102_driftInc_norm_le`, `s102_drift_bv`, `s102_driftInc_add`).  `Y` is any path `τ ↦ Y_τ ∈ 𝒳` continuous on `[0,T]` (the predicted paths).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}
  {b : ℝ → (Euc d → ℝ) → ℝ} {Mb : ℝ → ℝ}

theorem s102_curry_iter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ) (x : E) :
    continuousMultilinearCurryFin1 ℝ E ℝ (iteratedFDeriv ℝ 1 f x) = fderiv ℝ f x := by
  ext δ
  simp [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]

theorem s102_RS_drift (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) (hlin : S102Lin C m T)
    (hb : S102Drift C m T r Pw b Mb) (hT : 0 < T)
    (γ : ℝ → Measure (OscPath d m T)) (hγp : ∀ u, IsProbabilityMeasure (γ u))
    (Pj : ℕ → (OscPath d m T →L[ℝ] OscPath d m T)) (hP1 : ∀ L, ‖Pj L‖ ≤ 1)
    (hconv : ∀ w, Tendsto (fun L => Pj L w) atTop (𝓝 w)) (hLP : S102LipProj γ Pj)
    {Φ : OscPath d m T → ℝ} (hΦ : MemCb 5 Φ) (Y : ℝ → OscPath d m T) (hY : ContinuousOn Y (Set.Icc 0 T)) :
    ∃ I : ℝ, IsR2RS T (fun τ a b' => fderiv ℝ (r2HeatFn γ Φ τ) (Y τ) (r2DriftInc C m T b a b')) I ∧
      |I| ≤ s102_KV d r Pw c * cbNorm 5 Φ * ∫ u in Set.Ioc 0 T, Mb u ∧
      ∃ IL : ℕ → ℝ, (∀ L, IsR2RS T (fun τ a b' => fderiv ℝ (r2HeatFn γ (fun x => Φ (Pj L x)) τ) (Y τ)
          (r2DriftInc C m T b a b')) (IL L)) ∧
        (∀ L, |IL L| ≤ s102_KV d r Pw c * cbNorm 5 Φ * ∫ u in Set.Ioc 0 T, Mb u) ∧ Tendsto IL atTop (𝓝 I) := by
  have hT0 : 0 ≤ T := hT.le
  set KV := s102_KV d r Pw c with hKV
  have hKV0 : 0 ≤ KV := s102_KV_nonneg d r Pw c
  obtain ⟨hBV, hF0⟩ := s102_drift_bv hP hD hlin hb hT0
  obtain ⟨hc1, hc2, hc3⟩ := s102_conv_equicont γ hγp Pj hP1 hconv hLP hΦ Y hY 1 (by norm_num)
  have hK0 : 0 ≤ cbNorm 5 Φ := HRS.MC.Sec7.S7PIL.S7PIL_cbNorm_nonneg hΦ 0
  set Cv := continuousMultilinearCurryFin1 ℝ (OscPath d m T) ℝ with hCv
  set A : ℝ → (OscPath d m T →L[ℝ] ℝ) := fun τ => Cv (iteratedFDeriv ℝ 1 (r2HeatFn γ Φ τ) (Y τ)) with hA
  set AL : ℕ → ℝ → (OscPath d m T →L[ℝ] ℝ) := fun L τ => Cv (s102_projHeatD γ Φ (Pj L) 1 τ (Y τ)) with hAL
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
  obtain ⟨I, hI, IL, hIL, hlim⟩ := HRS.Sec7.measure_projection_proof Pj 1 hP1 hconv T hT
    (fun s => r2DriftInc C m T b 0 s) hBV hF0 A AL hAc hALc hAu
  have hinc : ∀ a b', 0 ≤ a → a ≤ b' → b' ≤ T →
      r2DriftInc C m T b 0 b' - r2DriftInc C m T b 0 a = r2DriftInc C m T b a b' := by
    intro a b' ha hab hb'
    have := s102_driftInc_add hP hD hlin hb hT0 (a := 0) (a' := a) (a'' := b') le_rfl ha hab
    rw [← this]; abel
  have hAeq : ∀ τ (δ : OscPath d m T), A τ δ = fderiv ℝ (r2HeatFn γ Φ τ) (Y τ) δ := by
    intro τ δ
    simp only [hA, hCv, s102_curry_iter]
  have hALeq : ∀ L τ (δ : OscPath d m T), AL L τ (Pj L δ) =
      fderiv ℝ (r2HeatFn γ (fun x => Φ (Pj L x)) τ) (Y τ) δ := by
    intro L τ δ
    have := s102_proj_deriv γ hγp (Pj L) hΦ 1 (by norm_num) τ (Y τ) (fun _ => δ)
    rw [iteratedFDeriv_one_apply] at this
    simp only [hAL, hCv, continuousMultilinearCurryFin1_apply]
    have e : (Fin.snoc (0 : Fin 0 → OscPath d m T) (Pj L δ) : Fin 1 → OscPath d m T) =
        fun _ => Pj L δ := by
      ext i; fin_cases i; simp
    rw [e, ← this]
  have hALb : ∀ L τ, ‖AL L τ‖ ≤ cbNorm 5 Φ := by
    intro L τ
    haveI := hγp τ
    simp only [hAL, hCv, LinearIsometryEquiv.norm_map]
    unfold s102_projHeatD
    have h1 : ‖∫ z, iteratedFDeriv ℝ 1 Φ (Pj L (Y τ + z)) ∂(γ τ)‖ ≤ cbNorm 5 Φ * (γ τ).real Set.univ :=
      norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun z =>
        HRS.MC.Sec7.S7PIL.S7PIL_le_cbNorm hΦ (by norm_num) _)
    simpa using h1
  have hint : IntegrableOn Mb (Set.Icc 0 T) := hb.Mb_int
  have hCI : ∀ a b', 0 ≤ a → a ≤ b' → b' ≤ T → 0 ≤ ∫ u in Set.Ioc a b', Mb u :=
    fun a b' _ _ _ => setIntegral_nonneg measurableSet_Ioc fun u _ => hb.Mb_nonneg u
  have hILT : ∀ L, IsR2RS T (fun τ a b' => fderiv ℝ (r2HeatFn γ (fun x => Φ (Pj L x)) τ) (Y τ)
      (r2DriftInc C m T b a b')) (IL L) := by
    intro L
    refine (s102_isR2RS_iff _ _ _).2 (HRS.MC.Sec7.S7PIG4.S7PIG4_RS_congr (hIL L) fun τ a b' ha h1 h2 hb' => ?_)
    show AL L τ (Pj L (r2DriftInc C m T b 0 b' - r2DriftInc C m T b 0 a)) = _
    rw [hinc a b' ha (h1.trans h2) hb', hALeq]
  have hILb : ∀ L, |IL L| ≤ KV * cbNorm 5 Φ * ∫ u in Set.Ioc 0 T, Mb u := by
    intro L
    refine HRS.MC.Sec7.S7PIG4.S7PIG4_RS_bound hT ((s102_isR2RS_iff _ _ _).1 (hILT L)) Mb hint (mul_nonneg hKV0 hK0)
      (c := KV * cbNorm 5 Φ) ?_
    intro τ a b' ha h1 h2 hb'
    have hab := h1.trans h2
    rw [← hALeq L τ]
    have hδ := s102_driftInc_norm_le hP hD hlin hb hT0 ha hab hb'
    have hCn : 0 ≤ ∫ u in Set.Ioc a b', Mb u := hCI a b' ha hab hb'
    calc |AL L τ (Pj L (r2DriftInc C m T b a b'))|
        ≤ ‖AL L τ‖ * ‖Pj L (r2DriftInc C m T b a b')‖ := by
          rw [← Real.norm_eq_abs]; exact (AL L τ).le_opNorm _
      _ ≤ cbNorm 5 Φ * ‖r2DriftInc C m T b a b'‖ := by
          gcongr
          · exact hALb L τ
          · exact ((Pj L).le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_right (hP1 L) (norm_nonneg (r2DriftInc C m T b a b')))
      _ ≤ cbNorm 5 Φ * (KV * ∫ u in Set.Ioc a b', Mb u) := by
          gcongr
      _ = KV * cbNorm 5 Φ * ∫ u in Set.Ioc a b', Mb u := by ring
  have hIT : IsR2RS T (fun τ a b' => fderiv ℝ (r2HeatFn γ Φ τ) (Y τ) (r2DriftInc C m T b a b')) I := by
    refine (s102_isR2RS_iff _ _ _).2 (HRS.MC.Sec7.S7PIG4.S7PIG4_RS_congr hI fun τ a b' ha h1 h2 hb' => ?_)
    show A τ (r2DriftInc C m T b 0 b' - r2DriftInc C m T b 0 a) = _
    rw [hinc a b' ha (h1.trans h2) hb', hAeq]
  refine ⟨I, hIT, ?_, IL, hILT, hILb, hlim⟩
  exact le_of_tendsto' hlim.abs hILb

end HRS.MS.R2Interp

end
