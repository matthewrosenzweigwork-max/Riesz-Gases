import HRS.MS.S81pPathSolve

/-!
# S8.1 (worker S81P), item 2, part 2: path-law stationarity of canonical realizations (`S81W2PathStat`)

Namespace `HRS.Whole.S81P`, prefix `s81p_`.

Route (the torus route of `HRS/MD/EQLawPath.lean`, with the maximal solution of `s81p_maximal` in place of `particle_wellposed`):

1. `s81p_canon_data`: for a canonical realization `(P, X₀, W, X)` with its filtration, the map `J ζ = (X_0 ζ, path of W')` into the canonical
   data space `PSig d N` is measurable and has image `Gibbs ⊗ (Brownian path law)`.
2. All Brownian path laws coincide (`bf_path_law_eq`), so two realizations have the same image measure `Q`.
3. `s81p_maximal` on `(PSig, Q)`; `s81p_compare`: for every canonical realization with data image `Q`, `X_t = Y_t ∘ J` a.s. on `[0,T]` and
   `T < τ ∘ J` a.s. (deterministic pathwise uniqueness `ssp1_det_domination`); `T < τ` `Q`-a.s. follows from one realization.
4. The window `ζ_N^{0+·}` is a.s. the fixed functional `Γ ∘ J`, `Γ` a.e. measurable, so the window laws of any two canonical realizations
   are both `Q.map Γ` (`s81p_window_law_eq`).
5. `s81p_pathStat : S81W2PathStat`, via the shifted realization `s81b_isCanonical_shift` and `s79p_zetaPathW_shift`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Whole HRS.MP.SelfSimP1 HRS.MS.S21 HRS.MD.EQLawPath
open scoped ENNReal NNReal BigOperators

namespace HRS.Whole.S81P

variable {d N : ℕ}

section Data

variable {s a β : ℝ} {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}

/-- The map of a filtered realization to the canonical data space. -/
def s81p_J {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsWholeFilteredSolution P ℱ W' W X) : Ω → PSig d N :=
  fun ζ => (X 0 ζ, bfPath hF.brownian ζ)

theorem s81p_J_measurable [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hF : IsWholeFilteredSolution P ℱ W' W X) :
    Measurable (s81p_J hF) := by
  have h0 : Measurable (X 0) := by
    have := hF.adapted 0
    exact this.mono (ℱ.le _) le_rfl
  exact h0.prodMk (measurable_bfPath _)

/-- The image of `P` under the data map: `Gibbs ⊗ (Brownian path law)`. -/
theorem s81p_J_map [IsProbabilityMeasure P] (hR : IsCanonicalRealization d s a β N P X₀ W X)
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsWholeFilteredSolution P ℱ W' W X) :
    P.map (s81p_J hF) =
      (canonicalGibbs (rieszKernel d s) (confinement a) N β).prod (P.map (bfPath hF.brownian)) := by
  have hBF := hF.brownian
  have hX0 : Measurable[ℱ 0] (X 0) := hF.adapted 0
  have hmeas : Measurable (X 0) := hX0.mono (ℱ.le _) le_rfl
  have hbf := measurable_bfPath hBF
  have hind : IndepFun (X 0) (bfPath hBF) P := by
    have h0 := indep_zero_path hBF
    have hle : MeasurableSpace.comap (bfPath hBF) inferInstance ≤
        MeasurableSpace.comap (fun ω => fun t : ℝ≥0 => W' t ω) inferInstance := by
      rw [measurableSpace_continuousMap_eq, MeasurableSpace.comap_comp]
      exact le_rfl
    have hle2 : MeasurableSpace.comap (X 0) inferInstance ≤ ℱ 0 := hX0.comap_le
    exact indep_of_indep_of_le_left (indep_of_indep_of_le_right h0 hle) hle2
  have h1 := (indepFun_iff_map_prod_eq_prod_map_map hmeas.aemeasurable hbf.aemeasurable).1 hind
  have h2 : P.map (X 0) = canonicalGibbs (rieszKernel d s) (confinement a) N β :=
    HRS.Whole.S79.s79p_law_init hR 0
  rw [h2] at h1
  exact h1

end Data

section Compare

variable {s a β : ℝ}

/-- Comparison with the maximal solution: if `P.map J = Q`, then a.s. `T < τ ∘ J` and `Y_t ∘ J = X_t` on `[0,T]`. -/
theorem s81p_compare {T : ℝ} (hT : 0 < T) {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → EucConfig d N} (hR : IsCanonicalRealization d s a β N P X₀ W X)
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsWholeFilteredSolution P ℱ W' W X) {Q : Measure (PSig d N)}
    (hmap : P.map (s81p_J hF) = Q)
    {τ : PSig d N → WithTop ℝ} {Y : ℝ → PSig d N → EucConfig d N}
    (hpos : ∀ σ, 0 < τ σ)
    (hmem : ∀ σ, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ σ → Y t σ ∈ ssp1_U d N)
    (hexit : ∀ σ, τ σ < ⊤ → ∀ K : Set (EucConfig d N), IsCompact K → K ⊆ ssp1_U d N →
        ∀ t₀ : ℝ, (t₀ : WithTop ℝ) < τ σ → ∃ t : ℝ, t₀ < t ∧ (t : WithTop ℝ) < τ σ ∧ Y t σ ∉ K)
    (hY : ∀ᵐ σ ∂Q, IsPathSolution (s21f_b d N s a β) (ssp1_sigma d N β⁻¹) (fun t => σ.2 t) σ.1
      (τ σ) (fun t => Y t σ)) :
    ∀ᵐ ζ ∂P, (T : WithTop ℝ) < τ (s81p_J hF ζ) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, Y t (s81p_J hF ζ) = X (Real.toNNReal t) ζ := by
  have hS := hR.solution T
  have hmp : MeasurePreserving (s81p_J hF) P Q := ⟨s81p_J_measurable hF, hmap⟩
  have hYJ := hmp.quasiMeasurePreserving.ae hY
  filter_upwards [hYJ, hS.eqn, hS.cont, hS.no_collision, hF.coords,
    HRS.IsVectorBrownian.ae_zero hR.brownian] with ζ hpath heqn hcont hnc hw hw0
  have hXc : Continuous fun t => X t ζ := continuous_pi hcont
  have hzc : Continuous fun r : ℝ => X (Real.toNNReal r) ζ := hXc.comp continuous_real_toNNReal
  have hz : IsPathSolution (s21f_b d N s a β) (ssp1_sigma d N β⁻¹) (fun t => (s81p_J hF ζ).2 t)
      (s81p_J hF ζ).1 (T : WithTop ℝ) (fun r => X (Real.toNNReal r) ζ) := by
    refine ⟨by simp [s81p_J], fun t ht htT => ?_⟩
    have htT' : t < T := WithTop.coe_lt_coe.1 htT
    have ht' : ((Real.toNNReal t : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht
    obtain ⟨hint, heq⟩ := heqn (Real.toNNReal t) (by rw [ht']; exact htT'.le)
    rw [ht'] at hint heq
    have hintE : IntegrableOn (fun r : ℝ => s21f_b d N s a β r (X (Real.toNNReal r) ζ))
        (Set.Icc 0 t) := Integrable.of_eval hint
    refine ⟨hzc.continuousOn, hintE, ?_⟩
    funext i
    have h2 := ssp1_integral_apply hintE i
    have hW0i : W 0 ζ i = 0 := by ext j; exact hw0 i j
    have h3 := heq i
    rw [hW0i, sub_zero] at h3
    have hnz := ssp1_noise_eq (N := N) (d := d) β⁻¹
      (w' := fun ij => (s81p_J hF ζ).2 (Real.toNNReal t) ij) (w := W (Real.toNNReal t) ζ)
      (fun i j => hw (Real.toNNReal t) i j)
    rw [hnz]
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [h2]
    exact h3
  have hzU : ∀ t ∈ Set.Icc (0 : ℝ) T, X (Real.toNNReal t) ζ ∈ ssp1_U d N := fun t ht =>
    hnc (Real.toNNReal t) (by rw [Real.coe_toNNReal t ht.1]; exact ht.2)
  exact ssp1_det_domination (ssp1_isOpen_U d N) (s21f_locLipschitz s a β)
    (s81p_J hF ζ).2.continuous hT (hpos _) hpath (fun t ht htτ => hmem _ t ht htτ)
    (fun h K hK hKU t₀ ht₀ => hexit _ h K hK hKU t₀ ht₀) hz hzc.continuousOn hzU

end Compare

section Window

/-- The window functional on the canonical data space. -/
def s81p_Gamma (m T : ℝ) (G : Measure (EucConfig d N)) (Y : ℝ → PSig d N → EucConfig d N)
    (σ : PSig d N) : OscPath d m T :=
  windowPathOf m T 0 (fun t => zetaB m G (Y t σ))

theorem s81p_Gamma_aemeas (hd : 2 ≤ d) (hN : 2 ≤ N) {m T : ℝ} (hm : (d : ℝ) < m) (hT : 0 ≤ T)
    (G : Measure (EucConfig d N)) [IsProbabilityMeasure G] (Q : Measure (PSig d N))
    {Y : ℝ → PSig d N → EucConfig d N} (hYm : ∀ t, Measurable (Y t))
    (hc : ∀ᵐ σ ∂Q, ContinuousOn (fun t => Y t σ) (Set.Icc 0 T)) :
    AEMeasurable (s81p_Gamma m T G Y) Q := by
  haveI : IsProbabilityMeasure (HRS.Whole.meanEmpirical G) :=
    HRS.Whole.meanEmpirical_isProbabilityMeasure G (by omega)
  have hcf : Continuous fun x : EucConfig d N => zetaB m G x :=
    HRS.MS.GenPath.s56_xi_cont_config (d := d) (by omega) hm (Real.sqrt N) (by omega)
      (HRS.Whole.meanEmpirical G)
  have h := HRS.GF.gfb4_aemeasurable_windowPath Q hT (fun t σ => zetaB m G (Y t σ))
    (fun t _ => hcf.measurable.comp (hYm t))
    (by filter_upwards [hc] with σ h; exact hcf.comp_continuousOn h)
  rw [← HRS.MS.GenPath.s56_wpo_eq_windowPath] at h
  exact h

variable {s a β : ℝ}

/-- Law of the window of a canonical realization is the image of the data law under `Γ`. -/
theorem s81p_window_law {m T : ℝ} (hd : 2 ≤ d) (hN : 2 ≤ N) (hm : (d : ℝ) < m) (hT : 0 < T)
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hR : IsCanonicalRealization d s a β N P X₀ W X)
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsWholeFilteredSolution P ℱ W' W X) {Q : Measure (PSig d N)}
    (hmap : P.map (s81p_J hF) = Q)
    {τ : PSig d N → WithTop ℝ} {Y : ℝ → PSig d N → EucConfig d N}
    (hYm : ∀ t, Measurable (Y t))
    (hcmp : ∀ᵐ ζ ∂P, (T : WithTop ℝ) < τ (s81p_J hF ζ) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, Y t (s81p_J hF ζ) = X (Real.toNNReal t) ζ)
    (hΓ : AEMeasurable (s81p_Gamma m T (canonicalGibbs (rieszKernel d s) (confinement a) N β) Y) Q) :
    law P (zetaPathW m T 0 P X) =
      Q.map (s81p_Gamma m T (canonicalGibbs (rieszKernel d s) (confinement a) N β) Y) ∧
    AEMeasurable (zetaPathW m T 0 P X) P := by
  set G := canonicalGibbs (rieszKernel d s) (confinement a) N β with hG
  have hae : zetaPathW m T 0 P X =ᵐ[P] fun ζ => s81p_Gamma m T G Y (s81p_J hF ζ) := by
    filter_upwards [hcmp] with ζ hζ
    unfold zetaPathW s81p_Gamma
    refine HRS.MS.GenPath.s56_wpo_congr fun t ht => ?_
    have h1 : P.map (X (Real.toNNReal t)) = G := HRS.Whole.S79.s79p_law_init hR _
    rw [h1, hζ.2 t ht]
  have hJ := s81p_J_measurable hF
  have hΓ' : AEMeasurable (s81p_Gamma m T G Y) (P.map (s81p_J hF)) := by rw [hmap]; exact hΓ
  refine ⟨?_, ?_⟩
  · calc law P (zetaPathW m T 0 P X)
        = P.map (fun ζ => s81p_Gamma m T G Y (s81p_J hF ζ)) := Measure.map_congr hae
      _ = (P.map (s81p_J hF)).map (s81p_Gamma m T G Y) :=
          (AEMeasurable.map_map_of_aemeasurable hΓ' hJ.aemeasurable).symm
      _ = _ := by rw [hmap]
  · exact (hΓ'.comp_aemeasurable hJ.aemeasurable).congr hae.symm

/-- **Uniqueness in law (window level) of canonical realizations**: for any two canonical realizations of the quadratic gradient
dynamics (possibly on different probability spaces) the exactly centered windows `ζ_N^{0+·}` have the same law. -/
theorem s81p_window_law_eq {m T : ℝ} (hd : 2 ≤ d) (hN : 2 ≤ N) (hm : (d : ℝ) < m) (hT : 0 < T)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hR : IsCanonicalRealization d s a β N P X₀ W X)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X₀' : Ω' → EucConfig d N} {W₂ : ℝ≥0 → Ω' → (Fin N → Euc d)} {X' : ℝ≥0 → Ω' → EucConfig d N}
    (hR' : IsCanonicalRealization d s a β N P' X₀' W₂ X') :
    law P (zetaPathW m T 0 P X) = law P' (zetaPathW m T 0 P' X') ∧
      AEMeasurable (zetaPathW m T 0 P X) P := by
  classical
  obtain ⟨ℱ, W₁, hF⟩ := hR.filtered
  obtain ⟨ℱ', W₁', hF'⟩ := hR'.filtered
  have hBF := hF.brownian
  have hBF' := hF'.brownian
  set G := canonicalGibbs (rieszKernel d s) (confinement a) N β with hG
  have hJ := s81p_J_measurable hF
  have hJ' := s81p_J_measurable hF'
  have hmap := s81p_J_map hR hF
  have hmap' := s81p_J_map hR' hF'
  have hL : P'.map (bfPath hBF') = P.map (bfPath hBF) := bf_path_law_eq hBF' hBF
  rw [hL] at hmap'
  have hX0 : Measurable (X 0) := (hF.adapted 0).mono (ℱ.le _) le_rfl
  haveI hGp : IsProbabilityMeasure G := by
    have : P.map (X 0) = G := HRS.Whole.S79.s79p_law_init hR 0
    rw [← this]
    infer_instance
  haveI hLp : IsProbabilityMeasure (P.map (bfPath hBF)) := inferInstance
  set Q : Measure (PSig d N) := G.prod (P.map (bfPath hBF)) with hQ
  -- the canonical data law
  have hBrQ : IsVectorBrownian Q (psigW d N) := by
    have := eqlaw_isVectorBrownian_map (P := P) (s81p_J hF) hJ (B := psigW d N)
      s81p_measurable_psigW s81p_continuous_psigW
      (isVectorBrownian_of_isBrownianFiltration P ℱ W₁ hBF)
    rw [hmap] at this
    exact this
  have hwpath : Measurable fun (c : WSp d N) (t : ℝ≥0) (i : Fin N) =>
      (WithLp.toLp 2 fun j => c t (i, j) : Euc d) :=
    measurable_pi_iff.2 fun t => measurable_pi_iff.2 fun i => (WithLp.measurable_toLp 2 _).comp
      (measurable_pi_iff.2 fun j => (measurable_pi_apply (i, j)).comp
        (ContinuousMap.measurable_eval t))
  have hindQ : IndepFun Prod.fst (fun σ : PSig d N => fun t => psigW d N t σ) Q :=
    indepFun_prod (μ := G) (ν := P.map (bfPath hBF)) (X := id)
      (Y := fun (c : WSp d N) (t : ℝ≥0) (i : Fin N) => (WithLp.toLp 2 fun j => c t (i, j) : Euc d))
      measurable_id hwpath
  have hdist : ∀ᵐ σ ∂Q, σ.1 ∉ eucCollisionSet d N := by
    have h0 : ∀ᵐ ζ ∂P, X 0 ζ ∉ eucCollisionSet d N := by
      filter_upwards [(hR.solution 0).no_collision] with ζ h using h 0 (by simp)
    have hms : MeasurableSet {σ : PSig d N | σ.1 ∉ eucCollisionSet d N} :=
      measurable_fst (ssp1_isClosed_coll d N).measurableSet.compl
    rw [← hmap]
    exact (ae_map_iff hJ.aemeasurable hms).2 h0
  obtain ⟨τ, Y, hYm, hτm, hpos, hmem, hexit, hY⟩ := s81p_maximal s a β Q hBrQ hindQ hdist
  have hc1 := s81p_compare hT hR hF hmap hpos hmem hexit hY
  have hc2 := s81p_compare hT hR' hF' hmap' hpos hmem hexit hY
  have htauQ : ∀ᵐ σ ∂Q, (T : WithTop ℝ) < τ σ := by
    rw [← hmap]
    exact (ae_map_iff hJ.aemeasurable (hτm T)).2 (hc1.mono fun ζ h => h.1)
  have hc : ∀ᵐ σ ∂Q, ContinuousOn (fun t => Y t σ) (Set.Icc 0 T) := by
    filter_upwards [hY, htauQ] with σ h1 h2
    exact (h1.2 T hT.le h2).1
  have hΓ := s81p_Gamma_aemeas hd hN hm hT.le G Q hYm hc
  have e1 := s81p_window_law hd hN hm hT hR hF hmap hYm hc1 hΓ
  have e2 := s81p_window_law hd hN hm hT hR' hF' hmap' hYm hc2 hΓ
  exact ⟨e1.1.trans e2.1.symm, e1.2⟩

end Window

/-- **Path-law stationarity** `S81W2PathStat`: for a canonical realization the exactly centered window started at `u ≥ 0` has the law of
the window started at `0`.  The shifted realization (`s81b_isCanonical_shift`) is a second canonical realization on the same space, so
this is `s81p_window_law_eq` (uniqueness in law of canonical realizations, via the deterministic pathwise uniqueness of `ssp1_det_domination`). -/
theorem s81p_pathStat : HRS.Whole.S81W2.S81W2PathStat := by
  intro d hd a β ha hβ m hm T hT N hN Ω _ P _ X₀ W X hR u hu
  have hm' : (d : ℝ) < m := by
    have h1 : ((24 * d + 240 : ℕ) : ℝ) = 24 * (d : ℝ) + 240 := by push_cast; ring
    have h2 : (wholeSpaceIndex d : ℝ) = 24 * (d : ℝ) + 240 := h1
    have h3 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hR' := HRS.Whole.BreakdownS81.s81b_isCanonical_shift hR u.toNNReal
  have hz : zetaPathW m T u P X = zetaPathW m T 0 P (HRS.Whole.S79.s79p_shiftX u.toNNReal X) :=
    funext fun ζ => HRS.Whole.S79.s79p_zetaPathW_shift P T X hu ζ
  rw [hz]
  exact (s81p_window_law_eq hd hN hm' hT hR' hR).1

end HRS.Whole.S81P
