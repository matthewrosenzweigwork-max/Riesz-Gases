import HRS.MC.Q714HICanon

/-!
# Packet HI (row 7.14), part 3: translation invariance of the law of the flow
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Q714.HI

open HRS HRS.MD.EQLawPath HRS.MD.EQLawFlow HRS.Sec7

variable {d N : ℕ}

theorem hi_law_shift (hd : 2 ≤ d) (hN : 1 ≤ N) (D : DynData d) (hM : D.M = -1)
    (hV : D.V = fun _ => 0) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Q₀ : Measure (Config d N)) (hQ0 : ∀ᵐ X ∂Q₀, X ∉ collisionSet d N)
    (hQ0inv : ∀ θ : Torus d, Q₀.map (shiftC θ) = Q₀)
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hreal : PreparedRealization D P Q₀ X₀ W X) (t : ℝ≥0) (θ : Torus d) :
    (P.map (X t)).map (shiftC θ) = P.map (X t) := by
  classical
  have hstr : ∀ T : ℝ, IsStrongSolution P D T X₀ W X := hreal.solution
  have hQ0p : IsProbabilityMeasure Q₀ := by
    rw [← hreal.law_init]
    infer_instance
  have hmapX0 : P.map (X 0) = Q₀ := by
    rw [← hreal.law_init]
    exact Measure.map_congr (hstr 0).init
  obtain ⟨ℱ, W', hF⟩ := hreal.filtered
  have hBF := hF.brownian
  have hs := isBrownianFiltration_shift hBF 0
  have hXm : Measurable[ℱ (((0 : ℝ≥0) : ℝ))] (X 0) := hF.adapted 0
  have hJm : Measurable (fun ω => ((X 0 ω, bfPath hs ω) : Sig d N)) :=
    measurable_eqlawJ hBF 0 (hXm.mono (ℱ.le _) le_rfl)
  have hmapJ : P.map (fun ω => ((X 0 ω, bfPath hs ω) : Sig d N)) =
      Q₀.prod (P.map (bfPath hs)) := by
    have := eqlawJ_map hBF 0 hXm
    rw [hmapX0] at this
    exact this
  have : IsProbabilityMeasure (P.map (bfPath hs)) := inferInstance
  set Q : Measure (Sig d N) := Q₀.prod (P.map (bfPath hs)) with hQ
  have hdist : ∀ᵐ σ ∂Q, σ.1 ∉ collisionSet d N := by
    have hmp : MeasurePreserving (Prod.fst : Sig d N → Config d N) Q Q₀ :=
      ⟨measurable_fst, by rw [hQ, Measure.map_fst_prod, measure_univ, one_smul]⟩
    exact hmp.quasiMeasurePreserving.ae hQ0
  have hBrQ : IsVectorBrownian Q (sigW d N) := by
    have := eqlaw_isVectorBrownian_map (P := P) _ hJm measurable_sigW continuous_sigW
      (isVectorBrownian_of_isBrownianFiltration P (shiftFil ℱ 0) (shiftProc W' 0) hs)
    rw [hmapJ] at this
    exact this
  have hwpath : Measurable fun (c : WSp d N) (t : ℝ≥0) (i : Fin N) =>
      (WithLp.toLp 2 fun j => c t (i, j) : Euc d) :=
    measurable_pi_iff.2 fun t => measurable_pi_iff.2 fun i => (WithLp.measurable_toLp 2 _).comp
      (measurable_pi_iff.2 fun j => (measurable_pi_apply (i, j)).comp
        (ContinuousMap.measurable_eval t))
  have hindQ : IndepFun Prod.fst (fun σ : Sig d N => fun t => sigW d N t σ) Q :=
    indepFun_prod (μ := Q₀) (ν := P.map (bfPath hs)) (X := id)
      (Y := fun (c : WSp d N) (t : ℝ≥0) (i : Fin N) =>
        (WithLp.toLp 2 fun j => c t (i, j) : Euc d))
      measurable_id hwpath
  set T : ℝ := (t : ℝ) + 1 with hT
  have hT0 : 0 < T := by positivity
  obtain ⟨Xσ, hXσ⟩ := hi_exists_canon hd hN D hM hV Q hdist hBrQ hindQ T hT0
  have hb := hi_locLip (N := N) hd D hV
  -- the flow is `Xσ ∘ J`
  have hdrv : ∀ᵐ ω ∂P, ∀ r : ℝ≥0, (fun i => W (0 + r) ω i - W 0 ω i) =
      ofCoords (shiftProc W' 0) r ω := by
    filter_upwards [hF.coords] with ω hω r
    funext i
    ext j
    simp [ofCoords, shiftProc, hω]
  have hstr' : IsStrongSolution P D (((0 : ℝ≥0) : ℝ) + T) X₀ W X := by
    simpa using hstr T
  have hcmp := eqlaw_flow_compare hb P 0 hstr' hs hdrv hJm hmapJ hXσ
  have hlaw : P.map (X t) = Q.map (Xσ t) := by
    calc P.map (X t) = P.map (fun ω => Xσ t ((X 0 ω, bfPath hs ω) : Sig d N)) := by
          refine Measure.map_congr ?_
          filter_upwards [hcmp] with ω hω
          have := hω t (by rw [hT]; linarith)
          simpa using this
      _ = (P.map (fun ω => ((X 0 ω, bfPath hs ω) : Sig d N))).map (Xσ t) :=
          (Measure.map_map (hXσ.adapted t) hJm).symm
      _ = Q.map (Xσ t) := by rw [hmapJ]
  -- translation on the canonical space
  set τ : Sig d N → Sig d N := fun σ => (shiftC θ σ.1, σ.2) with hτ
  have hτm : Measurable τ := ((measurable_shiftC θ).comp measurable_fst).prodMk measurable_snd
  have hQτ : Q.map τ = Q := by
    have : τ = Prod.map (shiftC θ) id := rfl
    rw [this, hQ, ← Measure.map_prod_map _ _ (measurable_shiftC θ) measurable_id, hQ0inv θ,
      Measure.map_id]
  have hA : IsStrongSolution Q D T (fun σ => shiftC θ σ.1) (sigW d N) (fun r σ => Xσ r (τ σ)) :=
    eqlaw_isStrongSolution_comp τ hτm hQτ hXσ
  have hB : IsStrongSolution Q D T (fun σ => shiftC θ σ.1) (sigW d N)
      (fun r σ => shiftC θ (Xσ r σ)) :=
    hi_isStrongSolution_shiftC hV θ hXσ
  have hPU := pathwiseUnique_of_locLipschitz Q D hb T (fun σ : Sig d N => shiftC θ σ.1) (sigW d N) hBrQ
  have hae := hPU _ _ hA hB
  calc (P.map (X t)).map (shiftC θ) = (Q.map (Xσ t)).map (shiftC θ) := by rw [hlaw]
    _ = Q.map (fun σ => shiftC θ (Xσ t σ)) :=
        Measure.map_map (measurable_shiftC θ) (hXσ.adapted t)
    _ = Q.map (fun σ => Xσ t (τ σ)) := by
        refine Measure.map_congr ?_
        filter_upwards [hae] with σ hσ
        exact (hσ t (by rw [hT]; linarith)).symm
    _ = (Q.map τ).map (Xσ t) := (Measure.map_map (hXσ.adapted t) hτm).symm
    _ = Q.map (Xσ t) := by rw [hQτ]
    _ = P.map (X t) := hlaw.symm

end HRS.MC.Q714.HI
