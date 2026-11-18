import HRS.MS.IidInitAux7

/-!
# SA27, part 8: path tightness and convergence in law on `C([0,T]; H^{-q})`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

noncomputable section

namespace HRS.MS.IidInit

open HRS HRS.Whole HRS.MP.HNegInfra HRS.MP.RdProp HRS.U5 HRS.Whole.AppendixA HRS.Whole.AppendixALemmas
open HRS.Whole.AppendixALemmas (AdjointInputOneD AdjointDerivInput)

variable {d : ℕ}

/-- Two continuous versions of the same process have a.s. the same path. -/
theorem sa27_pathLaw_congr {E : Type*} [NormedAddCommGroup E] (T : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z₁ Z₂ Y : ℝ → Ω → E)
    (h1 : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ζ ∂P, Z₁ t ζ = Y t ζ)
    (h2 : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ζ ∂P, Z₂ t ζ = Y t ζ)
    (c1 : ∀ᵐ ζ ∂P, Continuous fun t : Set.Icc (0 : ℝ) T => Z₁ t ζ)
    (c2 : ∀ᵐ ζ ∂P, Continuous fun t : Set.Icc (0 : ℝ) T => Z₂ t ζ) :
    (fun ζ => contPathOf T fun t => Z₁ t ζ) =ᵐ[P] fun ζ => contPathOf T fun t => Z₂ t ζ := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Set.Icc (0 : ℝ) T)
  have hD : ∀ᵐ ζ ∂P, ∀ t ∈ D, Z₁ t ζ = Z₂ t ζ :=
    (ae_ball_iff hDc).2 fun t _ => by
      filter_upwards [h1 t.1 t.2, h2 t.1 t.2] with ζ a b
      rw [a, b]
  filter_upwards [hD, c1, c2] with ζ hDζ hc1 hc2
  unfold contPathOf
  rw [dif_pos hc1, dif_pos hc2]
  ext t
  have := hc1.ext_on hDd hc2 (fun t ht => hDζ t ht)
  exact congrFun this t

/-- Tightness and convergence of the finite-dimensional marginals in `W₁`. -/
theorem sa27_path_conv_w1 (q T : ℝ) (μ : ℕ → Measure C(Set.Icc (0 : ℝ) T, HNeg d q))
    [∀ n, IsProbabilityMeasure (μ n)] (μ' : Measure C(Set.Icc (0 : ℝ) T, HNeg d q))
    [IsProbabilityMeasure μ'] (htight : IsTightMeasureSet (Set.range μ))
    (hw : ∀ (p : ℕ) (g : Fin p → Set.Icc (0 : ℝ) T × sa27_Tst d q),
      Tendsto (fun n => wassersteinE 1 ((μ n).map (sa27_fd (sa27_pathF T (sa27_pf d q)) g))
        (μ'.map (sa27_fd (sa27_pathF T (sa27_pf d q)) g))) atTop (𝓝 0)) :
    ∀ F : C(Set.Icc (0 : ℝ) T, HNeg d q) →ᵇ ℝ,
      Tendsto (fun n => ∫ w, F w ∂(μ n)) atTop (𝓝 (∫ w, F w ∂μ')) := by
  refine sa27_hneg_path_conv q T μ μ' htight fun p g h => ?_
  have hF : Continuous (sa27_fd (sa27_pathF T (sa27_pf d q)) g) :=
    sa27_fd_continuous _ (sa27_pathF_continuous T (sa27_pf d q) (sa27_pf_continuous q)) g
  haveI : ∀ n, IsProbabilityMeasure ((μ n).map (sa27_fd (sa27_pathF T (sa27_pf d q)) g)) := fun n =>
    inferInstance
  haveI : IsProbabilityMeasure (μ'.map (sa27_fd (sa27_pathF T (sa27_pf d q)) g)) :=
    inferInstance
  exact sa27_tendsto_of_w1 (fun n => (μ n).map (sa27_fd (sa27_pathF T (sa27_pf d q)) g))
    (μ'.map (sa27_fd (sa27_pathF T (sa27_pf d q)) g)) (hw p g) h

theorem sa27_conv_shift {E : Type*} [TopologicalSpace E] [MeasurableSpace E] (μ : ℕ → Measure E)
    (ν : Measure E)
    (h : ∀ F : E →ᵇ ℝ, Tendsto (fun n => ∫ w, F w ∂(μ (n + 1))) atTop (𝓝 (∫ w, F w ∂ν))) :
    HRS.Main.ConvergesInLaw μ ν := fun F => (tendsto_add_atTop_iff_nat 1).1 (h F)

/-- The main assembly: tightness and convergence in law of the two transported field paths. -/
theorem sa27_main (S : WholeMainData d) (L : LimitCoeffsRd d) (R : ∀ N, RealizationRd d N)
    (hid : IidSettingRd S R) (hX0 : ∀ N : ℕ, 1 ≤ N → Measurable (R N).X₀) (q m m₀ : ℕ)
    (Kadj Kst : ℝ) (hm₀ : 1 ≤ m₀)
    (hAdj : AdjointDerivInput (q : ℝ) (m₀ + 1) S.coeff S.T Kadj)
    (hAdjL : AdjointInputOneD (q : ℝ) (m₀ + 1) (L.coeff S) S.T Kadj)
    (hStab : AdjointStabilityInputRd S L q (m₀ + 1) m Kst)
    (hΔ : Tendsto (fun N => coeffDiscrepancyRd S L m N) atTop (𝓝 0))
    (Iq Jq Zemp Zη : ∀ N, ℝ → (R N).Ω → HNeg d (q : ℝ)) (hrepr : IsInitReprRd S R q Iq Jq)
    (hZe : ∀ N : ℕ, 1 ≤ N → HasContVersion S.T (R N).P (Iq N) (Zemp N) ∧
      Measurable fun ζ => contPathOf S.T fun t => Zemp N t ζ)
    (hZη : ∀ N : ℕ, 1 ≤ N → HasContVersion S.T (R N).P (Jq N) (Zη N) ∧
      Measurable fun ζ => contPathOf S.T fun t => Zη N t ζ)
    (hCe : ∃ Zc, ContVersionTight S.T (fun N => (R N).P) (fun N t ζ => Iq N t ζ) Zc)
    (hCj : ∃ Zc, ContVersionTight S.T (fun N => (R N).P) (fun N t ζ => Jq N t ζ) Zc)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η' : Ω' → (Euc d → ℝ) → ℝ) (hη' : IsGaussianBridgeW P' S.μ0 η')
    (J Jc : ℝ → Ω' → HNeg d (q : ℝ)) (hJm : ∀ t, Measurable (J t))
    (hJ : ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ φ, IsSobolevTest (q : ℝ) φ → ∀ᵐ ζ ∂P',
      HNeg.pairing φ (J t ζ) = L.A * η' ζ (propagatorW (L.coeff S) 0 t φ))
    (hJc : HasContVersion S.T P' J Jc) (hΦc : Measurable fun ζ => contPathOf S.T fun t => Jc t ζ) :
    HRS.Main.ConvergesInLaw (fun N => pathLaw S.T (R N).P (Zemp N)) (pathLaw S.T P' Jc) ∧
    HRS.Main.ConvergesInLaw (fun N => pathLaw S.T (R N).P (Zη N)) (pathLaw S.T P' Jc) ∧
    IsTightMeasureSet {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = pathLaw S.T (R N).P (Zemp N)} ∧
    IsTightMeasureSet {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = pathLaw S.T (R N).P (Zη N)} := by
  haveI := S.hμ0
  have hprobE : ∀ N : ℕ, 1 ≤ N → IsProbabilityMeasure (pathLaw S.T (R N).P (Zemp N)) := fun N hN =>
    inferInstance
  have hprobJ : ∀ N : ℕ, 1 ≤ N → IsProbabilityMeasure (pathLaw S.T (R N).P (Zη N)) := fun N hN =>
    inferInstance
  haveI hprobL : IsProbabilityMeasure (pathLaw S.T P' Jc) := inferInstance
  -- fixed-time tightness in `H^{-q}`
  have hft : ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      IsTightMeasureSet {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = (R N).P.map (Iq N t)} ∧
      IsTightMeasureSet {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = (R N).P.map (Jq N t)} := by
    intro t ht
    obtain ⟨h1, h2⟩ := sa27_fixed_time S L R hid hX0 q m m₀ Kadj Kst hm₀ hAdj hAdjL hStab hΔ Iq Jq hrepr
      P' η' hη' J hJm hJ ht
    haveI : ∀ n : ℕ, IsProbabilityMeasure (law (R (n + 1)).P (Iq (n + 1) t)) := fun n =>
      inferInstance
    haveI : ∀ n : ℕ, IsProbabilityMeasure (law (R (n + 1)).P (Jq (n + 1) t)) := fun n =>
      inferInstance
    haveI : IsProbabilityMeasure (law P' (J t)) := inferInstance
    refine ⟨?_, ?_⟩
    · have := sa27_tight_of_tendsto (fun n : ℕ => law (R (n + 1)).P (Iq (n + 1) t)) (law P' (J t))
        (sa27_tendsto_of_w1 _ _ h2)
      have hset : {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = (R N).P.map (Iq N t)} =
          Set.range (fun n : ℕ => law (R (n + 1)).P (Iq (n + 1) t)) := by
        ext μ
        simp only [Set.mem_ofPred_eq, Set.mem_range]
        constructor
        · rintro ⟨N, hN, rfl⟩
          exact ⟨N - 1, by rw [Nat.sub_add_cancel hN]⟩
        · rintro ⟨n, rfl⟩
          exact ⟨n + 1, by omega, rfl⟩
      rw [hset]; exact this
    · have := sa27_tight_of_tendsto (fun n : ℕ => law (R (n + 1)).P (Jq (n + 1) t)) (law P' (J t))
        (sa27_tendsto_of_w1 _ _ h1)
      have hset : {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = (R N).P.map (Jq N t)} =
          Set.range (fun n : ℕ => law (R (n + 1)).P (Jq (n + 1) t)) := by
        ext μ
        simp only [Set.mem_ofPred_eq, Set.mem_range]
        constructor
        · rintro ⟨N, hN, rfl⟩
          exact ⟨N - 1, by rw [Nat.sub_add_cancel hN]⟩
        · rintro ⟨n, rfl⟩
          exact ⟨n + 1, by omega, rfl⟩
      rw [hset]; exact this
  -- path tightness through the continuous versions
  obtain ⟨Zce, hZce⟩ := hCe
  obtain ⟨Zcj, hZcj⟩ := hCj
  have hcongE : ∀ N : ℕ, 1 ≤ N →
      (R N).P.map (fun ζ => contPathOf S.T fun t => Zce N t ζ) = pathLaw S.T (R N).P (Zemp N) := by
    intro N hN
    refine Measure.map_congr (sa27_pathLaw_congr S.T (R N).P (Zce N) (Zemp N) (Iq N)
      (fun t ht => hZce.1 N hN t ht) (fun t ht => (hZe N hN).1.1 t ht) (hZce.2.1 N hN)
      ((hZe N hN).1.2.mono fun ζ h => continuousOn_iff_continuous_restrict.1 h))
  have hcongJ : ∀ N : ℕ, 1 ≤ N →
      (R N).P.map (fun ζ => contPathOf S.T fun t => Zcj N t ζ) = pathLaw S.T (R N).P (Zη N) := by
    intro N hN
    refine Measure.map_congr (sa27_pathLaw_congr S.T (R N).P (Zcj N) (Zη N) (Jq N)
      (fun t ht => hZcj.1 N hN t ht) (fun t ht => (hZη N hN).1.1 t ht) (hZcj.2.1 N hN)
      ((hZη N hN).1.2.mono fun ζ h => continuousOn_iff_continuous_restrict.1 h))
  have htightE : IsTightMeasureSet {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = pathLaw S.T (R N).P (Zemp N)} := by
    have h := hZce.2.2.2.2 fun t ht => (hft t ht).1
    have hset : {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = pathLaw S.T (R N).P (Zemp N)} =
        {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = (R N).P.map (fun ζ => contPathOf S.T fun t => Zce N t ζ)} := by
      ext μ
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨N, hN, rfl⟩
        exact ⟨N, hN, (hcongE N hN).symm⟩
      · rintro ⟨N, hN, rfl⟩
        exact ⟨N, hN, hcongE N hN⟩
    rw [hset]; exact h
  have htightJ : IsTightMeasureSet {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = pathLaw S.T (R N).P (Zη N)} := by
    have h := hZcj.2.2.2.2 fun t ht => (hft t ht).2
    have hset : {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = pathLaw S.T (R N).P (Zη N)} =
        {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = (R N).P.map (fun ζ => contPathOf S.T fun t => Zcj N t ζ)} := by
      ext μ
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨N, hN, rfl⟩
        exact ⟨N, hN, (hcongJ N hN).symm⟩
      · rintro ⟨N, hN, rfl⟩
        exact ⟨N, hN, hcongJ N hN⟩
    rw [hset]; exact h
  refine ⟨?_, ?_, htightE, htightJ⟩
  · refine sa27_conv_shift _ _ ?_
    haveI : ∀ n : ℕ, IsProbabilityMeasure (pathLaw S.T (R (n + 1)).P (Zemp (n + 1))) := fun n =>
      hprobE (n + 1) (by omega)
    refine sa27_path_conv_w1 (q : ℝ) S.T (fun n : ℕ => pathLaw S.T (R (n + 1)).P (Zemp (n + 1)))
      (pathLaw S.T P' Jc) ?_ fun p g => ?_
    · refine htightE.subset ?_
      rintro _ ⟨n, rfl⟩
      exact ⟨n + 1, by omega, rfl⟩
    · exact (sa27_fdd_w1 S L R hid hX0 q m m₀ Kadj Kst hm₀ hAdj hAdjL hStab hΔ Iq Jq Zemp Zη hrepr hZe
        hZη P' η' hη' J Jc hJ hJc hΦc g).2
  · refine sa27_conv_shift _ _ ?_
    haveI : ∀ n : ℕ, IsProbabilityMeasure (pathLaw S.T (R (n + 1)).P (Zη (n + 1))) := fun n =>
      hprobJ (n + 1) (by omega)
    refine sa27_path_conv_w1 (q : ℝ) S.T (fun n : ℕ => pathLaw S.T (R (n + 1)).P (Zη (n + 1)))
      (pathLaw S.T P' Jc) ?_ fun p g => ?_
    · refine htightJ.subset ?_
      rintro _ ⟨n, rfl⟩
      exact ⟨n + 1, by omega, rfl⟩
    · exact (sa27_fdd_w1 S L R hid hX0 q m m₀ Kadj Kst hm₀ hAdj hAdjL hStab hΔ Iq Jq Zemp Zη hrepr hZe
        hZη P' η' hη' J Jc hJ hJc hΦc g).1

end HRS.MS.IidInit
