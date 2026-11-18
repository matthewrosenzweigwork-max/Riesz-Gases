import HRS.MS.MainRdPathAux28

/-!
# S.A.10, part 3: the fixed-time and multi-time initial conditions for i.i.d. data

For the i.i.d. setting (`IidSettingRd`) the hypotheses `TransportedConvergesFixedTime` and `EmpiricalInitialVectorConverges`
of `main_rd_path` are consequences of S.B.2 (`iid_init_field_rd`) and the `L²` coupling of S.A.27.  The a.e.-measurability
of the realization fields `(R N).η` is needed (explicit hypothesis `hηm`): otherwise the law `law (R N).P (R N).η` is a
junk Dirac mass.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

namespace HRS.MS.MainRdPath

open HRS HRS.Whole HRS.MP.HNegInfra HRS.MP.RdProp HRS.U5 HRS.Whole.AppendixA HRS.Whole.AppendixALemmas
  HRS.MS.IidInit
open HRS.Whole.AppendixALemmas (AdjointInputOneD AdjointDerivInput)

variable {d : ℕ}

theorem sa9_init_repr (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (hid : IidSettingRd S R)
    (hX0 : ∀ N : ℕ, 1 ≤ N → Measurable (R N).X₀) (q : ℕ) (K : ℝ)
    (hFI : AdjointFieldInput (q : ℝ) S.coeff S.T K) :
    ∃ Iq Jq : ∀ N, ℝ → (R N).Ω → HNeg d (q : ℝ), IsInitReprRd S R q Iq Jq := by
  haveI := S.hμ0
  obtain ⟨C, hC⟩ := iid_init_field_rd_proof (d := d) S.hd q S.T K (∫ x, ‖x‖ ^ 2 ∂S.μ0)
  have hex : ∀ (N : ℕ) (t : ℝ), ∃ Ie Je : (R N).Ω → HNeg d (q : ℝ), Measurable Ie ∧ Measurable Je ∧
      (1 ≤ N → t ∈ Set.Icc (0 : ℝ) S.T → ∀ φ : Euc d → ℝ, IsSobolevTest (q : ℝ) φ →
        ∀ᵐ ζ ∂(R N).P,
          HNeg.pairing φ (Ie ζ) = S.AN N * (S.κ N *
            (HRS.Whole.pair (HRS.Whole.empirical ((R N).X₀ ζ)) (propagatorW (S.coeff N) 0 t φ) -
              HRS.Whole.pair S.μ0 (propagatorW (S.coeff N) 0 t φ))) ∧
          HNeg.pairing φ (Je ζ) = S.AN N * (R N).η ζ (propagatorW (S.coeff N) 0 t φ)) := by
    intro N t
    by_cases h : 1 ≤ N ∧ t ∈ Set.Icc (0 : ℝ) S.T
    · obtain ⟨hN, ht⟩ := h
      have hh := hC S.coeff S.invβ S.hinvβ hFI S.μ0 S.hμ0 hid.second_moment le_rfl N hN t ht
      obtain ⟨⟨Iemp, hIm, hIp⟩, hJ, -⟩ := hh
      obtain ⟨Je, hJem, hJep⟩ := hJ (R N).P (R N).η (hid.bridge N hN)
      have hA : S.AN N = fieldAmp N (S.invβ N) := sa27_fieldAmp_eq S hid.kappa N hN
      refine ⟨fun ζ => Iemp ((R N).X₀ ζ), Je, hIm.comp (hX0 N hN), hJem, fun _ _ φ hφ => ?_⟩
      filter_upwards [hJep φ hφ] with ζ h2
      refine ⟨?_, ?_⟩
      · show HNeg.pairing φ (Iemp ((R N).X₀ ζ)) = _
        rw [hIp φ hφ, hid.kappa N hN, hA]; ring
      · rw [h2, hA]
    · exact ⟨0, 0, measurable_const, measurable_const, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose Ie Je hIe hJe hrep using hex
  exact ⟨Ie, Je, fun N hN t => ⟨hIe N t, hJe N t⟩, fun N hN t ht φ hφ => hrep N t hN ht φ hφ⟩

theorem sa9_bridge_transfer (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (hid : IidSettingRd S R)
    (hηm : ∀ N : ℕ, 1 ≤ N → AEMeasurable (R N).η (R N).P) (νη : Measure ((Euc d → ℝ) → ℝ))
    (hνη : ∀ N : ℕ, 1 ≤ N → law (R N).P (R N).η = νη)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η₀ : Ω' → (Euc d → ℝ) → ℝ) (hlaw : law P' η₀ = νη) (hη₀m : AEMeasurable η₀ P') :
    IsGaussianBridgeW P' S.μ0 (hη₀m.mk η₀) := by
  refine ⟨fun ψ _ => (measurable_pi_apply ψ).comp hη₀m.measurable_mk, fun p ψ hψ => ?_⟩
  have hF : Measurable (fun x : (Euc d → ℝ) → ℝ =>
      (WithLp.toLp 2 fun a => x (ψ a) : EuclideanSpace ℝ (Fin p))) :=
    (MeasurableEquiv.toLp 2 (Fin p → ℝ)).measurable.comp (measurable_pi_iff.2 fun a => measurable_pi_apply (ψ a))
  have h2 : law P' (hη₀m.mk η₀) = νη := (Measure.map_congr hη₀m.ae_eq_mk.symm).trans hlaw
  have h1 : law P' (fun ζ => (WithLp.toLp 2 fun a => hη₀m.mk η₀ ζ (ψ a) : EuclideanSpace ℝ (Fin p))) =
      (law P' (hη₀m.mk η₀)).map (fun x : (Euc d → ℝ) → ℝ =>
        (WithLp.toLp 2 fun a => x (ψ a) : EuclideanSpace ℝ (Fin p))) :=
    (Measure.map_map hF hη₀m.measurable_mk).symm
  have h3 : (law (R 1).P (R 1).η).map (fun x : (Euc d → ℝ) → ℝ =>
        (WithLp.toLp 2 fun a => x (ψ a) : EuclideanSpace ℝ (Fin p))) =
      law (R 1).P (fun ζ => (WithLp.toLp 2 fun a => (R 1).η ζ (ψ a) : EuclideanSpace ℝ (Fin p))) :=
    AEMeasurable.map_map_of_aemeasurable hF.aemeasurable (hηm 1 le_rfl)
  rw [h1, h2, ← hνη 1 le_rfl, h3]
  exact (hid.bridge 1 le_rfl).2 p ψ hψ

theorem sa9_iid_fix (S : WholeMainData d) (L : LimitCoeffsRd d) (R : ∀ N, RealizationRd d N)
    (hid : IidSettingRd S R) (hηm : ∀ N : ℕ, 1 ≤ N → AEMeasurable (R N).η (R N).P)
    (q m m₀ : ℕ) (Kadj Kst : ℝ) (hm₀ : 1 ≤ m₀)
    (hAdj : AdjointDerivInput (q : ℝ) (m₀ + 1) S.coeff S.T Kadj)
    (hAdjL : AdjointInputOneD (q : ℝ) (m₀ + 1) (L.coeff S) S.T Kadj)
    (hStab : AdjointStabilityInputRd S L q (m₀ + 1) m Kst)
    (hΔ : Tendsto (fun N => coeffDiscrepancyRd S L m N) atTop (𝓝 0)) :
    TransportedConvergesFixedTime S R L q := by
  intro t ht νη hνη Ω' _ P' _ η₀ hlaw hη₀m J hJm hJ I' hI'
  have hbr := sa9_bridge_transfer S R hid hηm νη hνη P' η₀ hlaw hη₀m
  have hJ' : ∀ φ : Euc d → ℝ, IsSobolevTest (q : ℝ) φ → ∀ᵐ ζ ∂P',
      HNeg.pairing φ (J ζ) = L.A * (hη₀m.mk η₀) ζ (propagatorW (L.coeff S) 0 t φ) := fun φ hφ => by
    filter_upwards [hJ φ hφ, hη₀m.ae_eq_mk] with ζ h1 h2
    rw [h1, h2]
  have hw := sa9_fix_w1 S L R hid q m m₀ Kadj Kst hm₀ hAdj hAdjL hStab hΔ ht I' hI' P'
    (hη₀m.mk η₀) hbr J hJm hJ'
  haveI : ∀ n : ℕ, IsProbabilityMeasure (law (R (n + 1)).P (I' (n + 1))) := fun n => inferInstance
  haveI : IsProbabilityMeasure (law P' J) := inferInstance
  exact sa27_conv_shift _ _ (sa27_tendsto_of_w1 (fun n : ℕ => law (R (n + 1)).P (I' (n + 1)))
    (law P' J) hw)

theorem sa9_iid_emp (S : WholeMainData d) (L : LimitCoeffsRd d) (R : ∀ N, RealizationRd d N)
    (hid : IidSettingRd S R) (hX0 : ∀ N : ℕ, 1 ≤ N → Measurable (R N).X₀)
    (hηm : ∀ N : ℕ, 1 ≤ N → AEMeasurable (R N).η (R N).P)
    (q m m₀ : ℕ) (Kadj Kst : ℝ) (hm₀ : 1 ≤ m₀)
    (hAdj : AdjointDerivInput (q : ℝ) (m₀ + 1) S.coeff S.T Kadj)
    (hAdjL : AdjointInputOneD (q : ℝ) (m₀ + 1) (L.coeff S) S.T Kadj)
    (hStab : AdjointStabilityInputRd S L q (m₀ + 1) m Kst)
    (hΔ : Tendsto (fun N => coeffDiscrepancyRd S L m N) atTop (𝓝 0))
    (Iq Jq : ∀ N, ℝ → (R N).Ω → HNeg d (q : ℝ)) (hrepr : IsInitReprRd S R q Iq Jq)
    {p : ℕ} (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T)
    (hφ : ∀ a, IsSobolevTest (q : ℝ) (φ a)) :
    EmpiricalInitialVectorConverges S R L ts φ := by
  intro νη hνη Ω' _ P' _ η₀ hlaw hη₀m
  have hbr := sa9_bridge_transfer S R hid hηm νη hνη P' η₀ hlaw hη₀m
  have hw := sa9_vec_w1 S L R hid hX0 q m m₀ Kadj Kst hm₀ hAdj hAdjL hStab hΔ Iq Jq hrepr P'
    (hη₀m.mk η₀) hbr (p := p) (fun a => ((⟨ts a, hts a⟩ : Set.Icc (0 : ℝ) S.T), (⟨φ a, hφ a⟩ : sa27_Tst d (q : ℝ))))
  have hconv := sa27_tendsto_of_w1 _ _ hw
  have hL : ∀ n : ℕ, law (R (n + 1)).P (fun ζ => (WithLp.toLp 2 fun a => S.AN (n + 1) * (S.κ (n + 1) *
        (HRS.Whole.pair (HRS.Whole.empirical ((R (n + 1)).X₀ ζ)) (propagatorW (S.coeff (n + 1)) 0 (ts a) (φ a)) -
          HRS.Whole.pair S.μ0 (propagatorW (S.coeff (n + 1)) 0 (ts a) (φ a)))) : EuclideanSpace ℝ (Fin p))) =
      (R (n + 1)).P.map (fun ζ => (WithLp.toLp 2 fun a => HNeg.pairing (φ a) (Iq (n + 1) (ts a) ζ) :
        EuclideanSpace ℝ (Fin p))) := by
    intro n
    refine Measure.map_congr ?_
    have : ∀ᵐ ζ ∂(R (n + 1)).P, ∀ a, HNeg.pairing (φ a) (Iq (n + 1) (ts a) ζ) = S.AN (n + 1) *
        (S.κ (n + 1) * (HRS.Whole.pair (HRS.Whole.empirical ((R (n + 1)).X₀ ζ))
          (propagatorW (S.coeff (n + 1)) 0 (ts a) (φ a)) -
          HRS.Whole.pair S.μ0 (propagatorW (S.coeff (n + 1)) 0 (ts a) (φ a)))) :=
      ae_all_iff.2 fun a => by
        filter_upwards [hrepr.2 (n + 1) (by omega) (ts a) (hts a) (φ a) (hφ a)] with ζ h
        exact h.1
    filter_upwards [this] with ζ hζ
    ext a
    exact (hζ a).symm
  have hR : law P' (fun ζ => (WithLp.toLp 2 fun a => L.A * η₀ ζ (propagatorW (L.coeff S) 0 (ts a) (φ a)) :
        EuclideanSpace ℝ (Fin p))) =
      P'.map (fun ζ => (WithLp.toLp 2 fun a => L.A * (hη₀m.mk η₀) ζ
        (propagatorW (L.coeff S) 0 (ts a) (φ a)) : EuclideanSpace ℝ (Fin p))) := by
    refine Measure.map_congr ?_
    filter_upwards [hη₀m.ae_eq_mk] with ζ h
    ext a
    simp [h]
  rw [hR]
  refine sa27_conv_shift _ _ fun F => ?_
  refine (hconv F).congr fun n => ?_
  rw [hL n]

end HRS.MS.MainRdPath
