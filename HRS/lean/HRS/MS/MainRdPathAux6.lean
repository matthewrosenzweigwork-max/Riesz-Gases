import HRS.MS.MainRdPathAux5

/-!
# S.A.9, packets P1-P4: the data bundle and the conditional tightness theorem

`Sa9Bundle`: the particle field `Z`, its decomposition `Z = Iq + Mq + Rm` at the index `q = Γ+2` and the continuous
version `Ic` of `Iq` (S.A.23).  `sa9_bundle_exists` builds it from the hypotheses of `main_rd_path`;
`sa9_pathRepr_exists` is the existence part (a) of `RdPathConclusion`; `sa9_tight_reps` is the tightness of the path
laws of every representative, given the fixed-time tightness of the bundle's `Z`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdPath

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.RdMart HRS.MP.RdProp
  HRS.MP.HNegInfra HRS.MP.RdRem HRS.MS.MainRdField HRS.MH.DualityRd HRS.MP.RdGen HRS.MP.KC

variable {d : ℕ}

theorem sa9_test_mono {Γ q : ℕ} (hΓq : Γ ≤ q) {φ : Euc d → ℝ} (hφ : IsSobolevTest (q : ℝ) φ) :
    IsSobolevTest (Γ : ℝ) φ :=
  ⟨hφ.1, HRS.PDE.ToolboxRd.FourierAux.memSobolev_mono (by exact_mod_cast hΓq) hφ.2⟩

/-- The bundle of the particle field, its decomposition and the continuous version of the initial term. -/
structure Sa9Bundle (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (Γ : ℕ) where
  Z : ∀ N, ℝ → (R N).Ω → HNeg d ((Γ + 2 : ℕ) : ℝ)
  Iq : ∀ N, ℝ → (R N).Ω → HNeg d ((Γ + 2 : ℕ) : ℝ)
  Mq : ∀ N, ℝ → (R N).Ω → HNeg d ((Γ + 2 : ℕ) : ℝ)
  Rm : ∀ N, ℝ → (R N).Ω → HNeg d ((Γ + 2 : ℕ) : ℝ)
  Ic : ∀ N, ℝ → (R N).Ω → HNeg d ((Γ + 2 : ℕ) : ℝ)
  ℱ : ∀ N, Filtration ℝ (R N).mΩ
  W' : ∀ N, ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ
  hfilt : ∀ N : ℕ, 1 ≤ N → IsWholeFilteredSolution (R N).P (ℱ N) (W' N) (R N).W (R N).X
  hMq : ∀ N : ℕ, 1 ≤ N → IsStochConvW (R N).P (ℱ N) (W' N) (S.coeff N)
    (S.sigma N * Real.sqrt (2 * S.invβ N) / N) (Γ + 2) S.T (R N).X (fun _ => S.T) (Mq N)
  hRm : ∀ N : ℕ, 1 ≤ N → IsRemainderW S R N (Γ + 2) (Rm N)
  hdec : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ ζ, Rm N t ζ = Z N t ζ - Iq N t ζ - Mq N t ζ
  hZm : ∀ N : ℕ, 1 ≤ N → ∀ t, Measurable (Z N t)
  hZp : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ ζ, ∀ φ : Euc d → ℝ,
    IsSobolevTest ((Γ + 2 : ℕ) : ℝ) φ → HNeg.pairing φ (Z N t ζ) = S.sigma N *
      (HRS.Whole.pair (HRS.Whole.empirical ((R N).X (Real.toNNReal t) ζ)) φ -
        HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N t)) φ)
  hZc : ∀ N : ℕ, 1 ≤ N → ∀ᵐ ζ ∂(R N).P, Continuous fun t : Set.Icc (0 : ℝ) S.T => Z N t.1 ζ
  hIqm : ∀ N : ℕ, 1 ≤ N → ∀ t, Measurable (Iq N t)
  hIqp : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ φ : Euc d → ℝ,
    IsSobolevTest ((Γ + 2 : ℕ) : ℝ) φ → ∀ᵐ ζ ∂(R N).P, HNeg.pairing φ (Iq N t ζ) = S.AN N * (S.κ N *
      (HRS.Whole.pair (HRS.Whole.empirical ((R N).X₀ ζ)) (propagatorW (S.coeff N) 0 t φ) -
        HRS.Whole.pair S.μ0 (propagatorW (S.coeff N) 0 t φ)))
  hIc : ContVersionTight S.T (fun N => (R N).P) Iq Ic

section Build

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {𝔈 : ℕ → ℝ}
  {Γ : ℕ}

theorem sa9_bundle_exists (s : ℝ) (fd : FieldDensityRd d s)
    (ν₀ MB Λ ΛV G₀ νbar T Kad Kadj Cw Cin : ℝ) (m₀ : ℕ) (hm₀ : 1 ≤ m₀) (hm₀' : m₀ ≤ mStar d)
    (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ)
    (S : WholeMainData d) (hs : S.s = s) (hT : S.T = T) (hinv : ∀ N, S.invβ N ≤ νbar)
    (hHold : fd.Holds S ν₀) (R : ∀ N, RealizationRd d N) (C₀ m20 : ℝ) (𝔈 : ℕ → ℝ)
    (hS : RdStanding S R MB Λ ΛV G₀ m20 (fd.Gamma + 5) (fd.Gamma + 5) C₀ 𝔈)
    (ε : ℕ → ℝ) (hinit : InitialFluctuationRd S R χ m₀ Cin ε (fun _ => ∅))
    (εf : ℕ → ℝ) (Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (fd.Gamma : ℝ))
    (hTIF : TransportedInitialFieldRd S R fd.Gamma Cin εf Iemp I)
    (hdist : InitialFieldDist S R fd.Gamma εf Iemp I)
    (hFA : FieldAdjointInputRd fd S Kad)
    (hAdjP : AdjointDerivInput ((fd.Gamma + 2 : ℕ) : ℝ) (m₀ + 1) S.coeff S.T Kadj)
    (hW : ∀ N : ℕ, 1 ≤ N → ∃ U, IsWeightedExtension (S.coeff N) (m₀ + 1) (fd.Gamma + 2) S.T Cw U) :
    ∃ C₁ : ℝ, (∀ N : ℕ, 1 ≤ N → KernelBoundRd (S.coeff N) S.T (fd.Gamma + 2) C₁) ∧
      Nonempty (Sa9Bundle S R fd.Gamma) := by
  classical
  have hT0 : 0 ≤ S.T := S.hT.le
  have hPA : PathAdjointInput S fd.Gamma m₀ Kadj Cw := ⟨hAdjP, hW⟩
  obtain ⟨C₁, hC₁⟩ := rpa_core s fd ν₀ MB Λ ΛV G₀ νbar T Kadj Cw m₀ hm₀'
  have hker : ∀ N : ℕ, 1 ≤ N → KernelBoundRd (S.coeff N) S.T (fd.Gamma + 2) C₁ := fun N hN => by
    have := ((hC₁ S hs hT hinv hHold hS.matrix_bound hS.mean_field hS.potential hPA).1 N hN).2
    rw [hT]; exact this
  refine ⟨C₁, hker, ?_⟩
  have hle : ((fd.Gamma + 2 : ℕ) : ℝ) ≤ ((fd.Gamma + 2 : ℕ) : ℝ) := le_rfl
  have hadjQ : AdjointDerivInput ((fd.Gamma + 2 : ℕ) : ℝ) (mStar d) S.coeff S.T (max Kad 0) :=
    sa9_adjDeriv_mono (a := (fd.Gamma : ℝ)) (by exact_mod_cast Nat.le_add_right fd.Gamma 2) hFA.deriv
  have hB : sa9_TestBd d (fd.Gamma + 2) ((d + 1) * |Kadj|) :=
    sa9_testBd_of_adj hT0 (Nat.le_add_left 1 m₀) (hAdjP 1 le_rfl)
  obtain ⟨Z, hZm, hZp, hZc⟩ := sa9_exists_Zf hS hB
  obtain ⟨ℱ, W', Iq, Mq, Rm, hfilt, hMq, hIq, hRm, hdec⟩ :=
    sa9_decomp hS hadjQ hker Z hZm hZp
  -- the lift of the Gaussian initial field
  obtain ⟨ι, hι⟩ := sa9_exists_lift (d := d) (Nat.le_add_right fd.Gamma 2)
  let Jq : ∀ N, ℝ → (R N).Ω → HNeg d ((fd.Gamma + 2 : ℕ) : ℝ) :=
    fun N t ζ => ι (I N (mrrClamp S.T t) ζ)
  have hrepr : IsInitReprRd S R (fd.Gamma + 2) Iq Jq := by
    refine ⟨fun N hN t => ⟨(hIq N hN).1 t, ?_⟩, fun N hN t ht φ hφ => ?_⟩
    · refine mrm_measurable_of_pairings fun φ hφ => ?_
      have hc := mrrClamp_mem hT0 t
      have : (fun ζ => HNeg.pairing φ (Jq N t ζ)) = fun ζ => HNeg.pairing φ (I N (mrrClamp S.T t) ζ) := by
        funext ζ; exact hι _ φ hφ
      rw [this]
      exact (mhn_continuous_pairing (sa9_test_mono (Nat.le_add_right fd.Gamma 2) hφ)).measurable.comp
        (hTIF.meas N hN _ hc).2
    · filter_upwards [(hIq N hN).2 t ht φ hφ,
        hTIF.repr N hN t ht φ (sa9_test_mono (Nat.le_add_right fd.Gamma 2) hφ)] with ζ h1 h2
      refine ⟨h1, ?_⟩
      show HNeg.pairing φ (ι (I N (mrrClamp S.T t) ζ)) = _
      rw [hι _ φ hφ, mrrClamp_of_mem ht, h2]
  obtain ⟨C, hC⟩ := HRS.MP.RdInitClose.path_initial_modulus_rd_proof s fd ν₀ MB Λ ΛV G₀ νbar T Kadj Cw Cin
    m₀ hm₀' χ hχ
  obtain ⟨-, ⟨Ic, hIc⟩, -⟩ := hC S hs hT hinv hHold hS.matrix_bound hS.mean_field hS.potential hPA R ε
    (fun _ => ∅) hinit εf Iemp I hTIF hdist Iq Jq hrepr
  exact ⟨⟨Z, Iq, Mq, Rm, Ic, ℱ, W', hfilt, hMq, hRm, hdec, hZm, hZp, hZc, fun N hN => (hIq N hN).1, fun N hN => (hIq N hN).2, by rw [hT]; exact hIc⟩⟩

end Build

end HRS.MS.MainRdPath
