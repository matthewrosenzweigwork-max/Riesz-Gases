import HRS.MD.EQLawPath
import HRS.Sections.Sec5

/-!
# Row 5.10, (S1.): `ret_path_law_proof`

Canonical-space argument of `EQLawPath` for a filtered particle system whose initial law `ν` is only absolutely continuous
with respect to the Gibbs law `G`.  The strong solution `Xσ` on `(Σ, G ⊗ 𝒲)` is also a strong solution on `(Σ, ν ⊗ 𝒲)`
(`IsStrongSolution` only has almost-sure and measure-free fields), and both windows are `(id, Xσ) ∘ J`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.ME.Ret

open HRS HRS.LZ HRS.Uniform HRS.MD HRS.MD.EQLawPath HRS.MD.EQLawFlow

variable {d : ℕ}

/-- `IsStrongSolution` transfers along absolute continuity of the measure. -/
theorem ret_isStrongSolution_ac {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P P' : Measure Ω} (hac : P' ≪ P)
    {D : DynData d} {T : ℝ} {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} (h : IsStrongSolution P D T X₀ W X) :
    IsStrongSolution P' D T X₀ W X where
  lift := by
    obtain ⟨Y, hY, hX⟩ := h.lift
    exact ⟨Y, hac.ae_le hY, hX⟩
  init := hac.ae_le h.init
  cont := hac.ae_le h.cont
  adapted := h.adapted
  no_collision := hac.ae_le h.no_collision

/-- `eqlaw_flow_canon` at `u = 0` for a filtered particle system with arbitrary initial law. -/
theorem ret_flow_canon {N : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hF : IsFilteredSolution P ℱ W' W X) :
    ∃ (ℱ1 : Filtration ℝ mΩ) (W1 : ℝ≥0 → Ω → Fin N × Fin d → ℝ) (hBF : IsBrownianFiltration P ℱ1 W1),
      Measurable (fun ω => ((X 0 ω, bfPath hBF ω) : Sig d N)) ∧
      P.map (fun ω => ((X 0 ω, bfPath hBF ω) : Sig d N)) =
        (P.map (X 0)).prod (P.map (bfPath hBF)) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (fun i => W (0 + t) ω i - W 0 ω i) = ofCoords W1 t ω := by
  classical
  have hBF := hF.brownian
  have hXm : Measurable[ℱ ((0 : ℝ≥0) : ℝ)] (X 0) := hF.adapted 0
  refine ⟨shiftFil ℱ 0, shiftProc W' 0, isBrownianFiltration_shift hBF 0, ?_, ?_, ?_⟩
  · exact measurable_eqlawJ hBF 0 (hXm.mono (ℱ.le _) le_rfl)
  · exact eqlawJ_map hBF 0 hXm
  · filter_upwards [hF.coords] with ω hω t
    funext i
    ext j
    simp [ofCoords, shiftProc, hω]

/-- Pushing a density that factors through the first coordinate along a map preserving it. -/
theorem ret_map_withDensity {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (Q : Measure (α × β)) (Φ : α × β → α × γ) (hΦ : Measurable Φ) (hfst : ∀ σ, (Φ σ).1 = σ.1)
    (f : α → ℝ≥0∞) (hf : Measurable f) :
    (Q.withDensity fun σ => f σ.1).map Φ = (Q.map Φ).withDensity fun z => f z.1 := by
  ext A hA
  rw [Measure.map_apply hΦ hA, withDensity_apply _ (hΦ hA), withDensity_apply _ hA,
    ← lintegral_indicator (hΦ hA), ← lintegral_indicator hA,
    lintegral_map (by exact (hf.comp measurable_fst).indicator hA) hΦ]
  refine lintegral_congr fun σ => ?_
  simp only [Set.indicator, Set.mem_preimage, hfst]
  rfl

theorem ret_path_law_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 2 ≤ N)
    (T : ℝ) (hT : 0 ≤ T)
    {Ω₁ : Type} [MeasurableSpace Ω₁] (P₁ : Measure Ω₁) [IsProbabilityMeasure P₁]
    (X₀₁ : Ω₁ → Config d N) (W₁ : ℝ≥0 → Ω₁ → (Fin N → Euc d)) (X₁ : ℝ≥0 → Ω₁ → Config d N)
    (h₁ : IsParticleSystem P₁ (PDE.mfData d s hs0 hsd V β hβ) T X₀₁ W₁ X₁)
    (hF₁ : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω₁›)
      (W' : ℝ≥0 → Ω₁ → (Fin N × Fin d) → ℝ), IsFilteredSolution P₁ ℱ W' W₁ X₁)
    (hac : law P₁ X₀₁ ≪ canonicalGibbs (periodicRiesz d s) V N β)
    {Ω₂ : Type} [MeasurableSpace Ω₂] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
    (X₀₂ : Ω₂ → Config d N) (W₂ : ℝ≥0 → Ω₂ → (Fin N → Euc d)) (X₂ : ℝ≥0 → Ω₂ → Config d N)
    (h₂ : IsStationaryGibbsFlow P₂ s hs0 hsd V β hβ T X₀₂ W₂ X₂) :
    P₁.map (fun ω => (X₀₁ ω, fun t : {t : ℝ≥0 // (t : ℝ) ≤ T} => X₁ t.1 ω)) =
      (P₂.map (fun ω => (X₀₂ ω, fun t : {t : ℝ≥0 // (t : ℝ) ≤ T} => X₂ t.1 ω))).withDensity
        (fun z => (law P₁ X₀₁).rnDeriv (canonicalGibbs (periodicRiesz d s) V N β) z.1) := by
  classical
  have : BorelSpace (Torus d) := Pi.borelSpace
  have : BorelSpace (Config d N) := Pi.borelSpace
  set G : Measure (Config d N) := canonicalGibbs (periodicRiesz d s) V N β with hG
  have hGp : IsProbabilityMeasure G := eqlaw_gibbs_prob hd hs0 hsd hV hβ (by omega)
  set D : DynData d := PDE.mfData d s hs0 hsd V β hβ with hD
  have hV2 : Torus.IsCk 2 D.V :=
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift V) from hV).of_le
      (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hM : Torus.SymNonpos D.M := eqlaw_symNonpos_neg_one
  have hb : IsLocLipschitzDrift (liftedFree d N) (fun _ Z => liftedDrift D Z) :=
    liftedDrift_locLipschitz D (kernelLocal_of_two_le hd D.hs0 D.hsd).smoothOffZero hV2
  have hstr₁ : IsStrongSolution P₁ D T X₀₁ W₁ X₁ := h₁.sol
  have hstr₂ : IsStrongSolution P₂ D T X₀₂ W₂ X₂ := by
    rcases h₂.flow.flow with ⟨h, _⟩ | ⟨h1, _⟩
    · exact h
    · exfalso; omega
  have hstat₂ : P₂.map (X₂ 0) = G :=
    Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ T hN P₂ X₀₂ W₂ X₂ h₂ 0
      (by simpa using hT)
  -- the two canonical embeddings
  obtain ⟨ℱ₁, W'₁, hFs₁⟩ := hF₁
  obtain ⟨ℱ1, W1, hBF1, hJ1, hmap1, hdrv1⟩ := ret_flow_canon P₁ hFs₁
  obtain ⟨ℱ2, W2, hBF2, hJ2, hmap2, hdrv2⟩ :=
    eqlaw_flow_canon hd hs0 hsd V hV hβ hN P₂ h₂ 0 (by simpa using hT)
  have hLL : P₁.map (bfPath hBF1) = P₂.map (bfPath hBF2) := bf_path_law_eq hBF1 hBF2
  rw [hLL] at hmap1
  have : IsProbabilityMeasure (P₂.map (bfPath hBF2)) := inferInstance
  set 𝒲 : Measure (WSp d N) := P₂.map (bfPath hBF2) with h𝒲
  set Q : Measure (Sig d N) := G.prod 𝒲 with hQ
  -- initial laws
  have hX0₁ : ∀ᵐ ω ∂P₁, X₁ 0 ω = X₀₁ ω := hstr₁.init
  have hX0₂ : ∀ᵐ ω ∂P₂, X₂ 0 ω = X₀₂ ω := hstr₂.init
  have hXm₁ : Measurable (X₁ 0) := hstr₁.adapted 0
  have hνeq : law P₁ X₀₁ = P₁.map (X₁ 0) := (Measure.map_congr hX0₁).symm
  set ν : Measure (Config d N) := law P₁ X₀₁ with hν
  have : IsProbabilityMeasure ν := by
    rw [hνeq]; exact ⟨by rw [Measure.map_apply hXm₁ MeasurableSet.univ]; simp⟩
  set Q' : Measure (Sig d N) := ν.prod 𝒲 with hQ'
  rw [← hνeq] at hmap1
  -- Q' = Q.withDensity (h ∘ fst)
  have hQ'eq : Q' = Q.withDensity fun σ => ν.rnDeriv G σ.1 := by
    rw [hQ', hQ, ← prod_withDensity_left (Measure.measurable_rnDeriv ν G),
      Measure.withDensity_rnDeriv_eq ν G hac]
  have hQ'ac : Q' ≪ Q := by rw [hQ'eq]; exact withDensity_absolutelyContinuous _ _
  -- the canonical solution
  have hdist : ∀ᵐ σ ∂Q, σ.1 ∉ collisionSet d N := by
    have hmp : MeasurePreserving (Prod.fst : Sig d N → Config d N) Q G :=
      ⟨measurable_fst, by rw [hQ, Measure.map_fst_prod, measure_univ, one_smul]⟩
    exact hmp.quasiMeasurePreserving.ae (eqlaw_gibbs_ae_not_collision hd s V β N)
  have hBrQ : IsVectorBrownian Q (sigW d N) := by
    have := eqlaw_isVectorBrownian_map (P := P₂) _ hJ2 measurable_sigW continuous_sigW
      (isVectorBrownian_of_isBrownianFiltration P₂ _ _ hBF2)
    rw [hmap2] at this
    exact this
  have hwpath : Measurable fun (c : WSp d N) (t : ℝ≥0) (i : Fin N) =>
      (WithLp.toLp 2 fun j => c t (i, j) : Euc d) :=
    measurable_pi_iff.2 fun t => measurable_pi_iff.2 fun i => (WithLp.measurable_toLp 2 _).comp
      (measurable_pi_iff.2 fun j => (measurable_pi_apply (i, j)).comp
        (ContinuousMap.measurable_eval t))
  have hindQ : IndepFun Prod.fst (fun σ : Sig d N => fun t => sigW d N t σ) Q :=
    indepFun_prod (μ := G) (ν := 𝒲) (X := id)
      (Y := fun (c : WSp d N) (t : ℝ≥0) (i : Fin N) => (WithLp.toLp 2 fun j => c t (i, j) : Euc d))
      measurable_id hwpath
  obtain ⟨⟨Xσ, hXσ⟩, -⟩ := particle_wellposed_proof Q D hd hN hM hV2 Prod.fst measurable_fst hdist
    (sigW d N) hBrQ hindQ (T + 1) (by linarith)
  have hXσ' : IsStrongSolution Q D T Prod.fst (sigW d N) Xσ :=
    eqlaw_isStrongSolution_mono (by linarith) hXσ
  have hXσ'' : IsStrongSolution Q' D T Prod.fst (sigW d N) Xσ :=
    ret_isStrongSolution_ac hQ'ac hXσ'
  -- comparison
  have hstr₁' : IsStrongSolution P₁ D (((0 : ℝ≥0) : ℝ) + T) X₀₁ W₁ X₁ := by
    simpa using hstr₁
  have hstr₂' : IsStrongSolution P₂ D (((0 : ℝ≥0) : ℝ) + T) X₀₂ W₂ X₂ := by
    simpa using hstr₂
  have hc1 := eqlaw_flow_compare hb P₁ 0 (X₀ := X₀₁) hstr₁' hBF1 hdrv1 hJ1 hmap1 hXσ''
  have hc2 := eqlaw_flow_compare hb P₂ 0 (X₀ := X₀₂) hstr₂' hBF2 hdrv2 hJ2 hmap2 hXσ'
  -- the functional
  set Φ : Sig d N → Config d N × ({t : ℝ≥0 // (t : ℝ) ≤ T} → Config d N) :=
    fun σ => (σ.1, fun t => Xσ t.1 σ) with hΦ
  have hΦm : Measurable Φ :=
    measurable_fst.prodMk (measurable_pi_iff.2 fun t => hXσ'.adapted t.1)
  have e1 : P₁.map (fun ω => (X₀₁ ω, fun t : {t : ℝ≥0 // (t : ℝ) ≤ T} => X₁ t.1 ω)) = Q'.map Φ := by
    calc _ = P₁.map (fun ω => Φ ((X₁ 0 ω, bfPath hBF1 ω) : Sig d N)) := by
          refine Measure.map_congr ?_
          filter_upwards [hX0₁, hc1] with ω h0 hω
          simp only [hΦ]
          refine Prod.ext h0.symm (funext fun t => ?_)
          simpa using hω t.1 t.2
      _ = (P₁.map (fun ω => ((X₁ 0 ω, bfPath hBF1 ω) : Sig d N))).map Φ :=
          (Measure.map_map hΦm hJ1).symm
      _ = Q'.map Φ := by rw [hmap1]
  have e2 : P₂.map (fun ω => (X₀₂ ω, fun t : {t : ℝ≥0 // (t : ℝ) ≤ T} => X₂ t.1 ω)) = Q.map Φ := by
    calc _ = P₂.map (fun ω => Φ ((X₂ 0 ω, bfPath hBF2 ω) : Sig d N)) := by
          refine Measure.map_congr ?_
          filter_upwards [hX0₂, hc2] with ω h0 hω
          simp only [hΦ]
          refine Prod.ext h0.symm (funext fun t => ?_)
          simpa using hω t.1 t.2
      _ = (P₂.map (fun ω => ((X₂ 0 ω, bfPath hBF2 ω) : Sig d N))).map Φ :=
          (Measure.map_map hΦm hJ2).symm
      _ = Q.map Φ := by rw [hmap2]
  rw [e1, e2, hQ'eq]
  exact ret_map_withDensity Q Φ hΦm (fun σ => rfl) (fun x => ν.rnDeriv G x)
    (Measure.measurable_rnDeriv ν G)

end HRS.ME.Ret

end
