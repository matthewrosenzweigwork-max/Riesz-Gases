import HRS.MS.MainRdFieldAux10
import HRS.MS.MainRdFieldAux2

/-!
# S.A.6, packet P6: the `d_{C²}` estimate for one `N` and one time `t`

`sa6_core_dC2`: for `N ≥ 2`, `t ∈ [0,T]`, every Gaussian `ν_G` with `IsLinearFieldNoiseRd` and every measurable
representative `Ξ` of `σ_N(μ_N^t - μ_{β_N}^t)`,
`d_{C²}(Law Ξ, Law(I_N^t) ∗ ν_G) ≤ (σ_N/2) K' T (𝔈_N + e_N) + ½ t (2 q_N C_p C_k 𝔴_N) + ε_N^f`.
The proof builds `I' = Riesz(σ_N(μ_N^0 - μ°)∘U^{0,t})` (`ℱ_0`-measurable, a.s. equal to `Iemp`), the Hilbert martingale
`M` of the kernel integrand, and `R := Ξ - I' - M_t`, so that `Ξ = I' + M_t + R` holds identically.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdField

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.RdMart HRS.MP.RdProp
  HRS.MP.HNegInfra HRS.MP.RdRem HRS.MH.DualityRd

variable {d : ℕ}

lemma sa6_meas_pair_emp {Ω : Type*} {m : MeasurableSpace Ω} {N : ℕ} (hN : 0 < N)
    {X : Ω → EucConfig d N} (hX : Measurable X) {ψ : Euc d → ℝ} (hψ : Continuous ψ) :
    Measurable (fun ζ => HRS.Whole.pair (HRS.Whole.empirical (X ζ)) ψ) := by
  simp_rw [HRS.Whole.pair_empirical hN]
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    hψ.measurable.comp ((measurable_pi_apply i).comp hX))

lemma sa6_AN_mul_kappa (S : WholeMainData d) (N : ℕ) : S.AN N * S.κ N = S.sigma N := by
  have hκ := S.hκ N
  unfold WholeMainData.AN WholeMainData.sigma Ascale sigmaScale
  by_cases h0 : S.invβ N = 0
  · simp [h0]
  · simp only [if_neg h0]
    field_simp

section Core

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {𝔈 : ℕ → ℝ}
  {Γ : ℕ} {e : ℕ → ℝ} {Kad K' Cp Ck m₂ Cin : ℝ} {χ : Euc d → ℝ} {εf : ℕ → ℝ}
  {Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (Γ : ℝ)}

theorem sa6_decomp
    (hS : RdStanding S R MB Λ ΛV G₀ m20 (Γ + 3) (Γ + 3) C₀ 𝔈) (hΛ : 1 ≤ Λ)
    (hadj : AdjointDerivInput (Γ : ℝ) (mStar d) S.coeff S.T Kad) (he : ∀ N, 0 ≤ e N)
    (hsel : SelectedCommutatorInput S (Γ : ℝ) S.T K' C₀ Λ e)
    (hinit : TransportedInitialFieldRd S R Γ Cin εf Iemp I)
    {N : ℕ} (hN : 2 ≤ N) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T)
    (hinj : ∀ᵐ ζ ∂(R N).P, ∀ᵐ ρ ∂(volume.restrict (Set.Icc (0 : ℝ) S.T)),
      Function.Injective ((R N).X (Real.toNNReal ρ) ζ))
    {Kk : ℝ} {Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (Γ : ℝ)}
    (hK : Sa6Kern (S.coeff N) S.T Γ Kk Kern)
    {Ξ : (R N).Ω → HNeg d (Γ : ℝ)} (hΞm : Measurable Ξ) (hΞ : IsFluctFieldRepr S R N Γ t Ξ) :
    ∃ (ℱ : Filtration ℝ (R N).mΩ) (W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ)
      (M : ℝ → (R N).Ω → HNeg d (Γ : ℝ)) (I' Rr : (R N).Ω → HNeg d (Γ : ℝ)),
      IsWholeFilteredSolution (R N).P ℱ W' (R N).W (R N).X ∧ (∀ τ, Measurable[ℱ τ] (M τ)) ∧
      (∀ T', IsHilbertMartingaleWithCovariation (R N).P ℱ T' M
        (fun r ω => hsCovForm (mrmZ Kern (sa6_cN S N) t (fun _ => S.T) (R N).X r ω))) ∧
      IsHilbertItoIntegral (R N).P ℱ W' (mrmZ Kern (sa6_cN S N) t (fun _ => S.T) (R N).X) M ∧
      @Measurable _ _ (ℱ 0) _ I' ∧ Measurable I' ∧ Measurable (M t) ∧ Measurable Rr ∧
      (∀ ω, Ξ ω = I' ω + M t ω + Rr ω) ∧ (∀ᵐ ζ ∂(R N).P, Iemp N t ζ = I' ζ) ∧
      (∀ᵐ ζ ∂(R N).P, ‖Rr ζ‖ₑ ≤ ENNReal.ofReal (S.sigma N / 2 * max K' 0) *
        ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (sa6_Gc S R N C₀ Λ e r ζ)) := by
  classical
  have hN1 : 1 ≤ N := by omega
  have hN0 : 0 < N := by omega
  have hT : 0 ≤ S.T := S.hT.le
  have htT : t ≤ S.T := ht.2
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N
  have hadjN := hadj N hN1
  obtain ⟨M, hMad, hM, hIto, hMp⟩ := sa6_M_exists hF hK ht
  have hex : ∀ ζ, ∃ k : HNeg d (Γ : ℝ), ∀ φ : Euc d → ℝ, IsSobolevTest (Γ : ℝ) φ →
      HNeg.pairing φ k = S.sigma N * ((∫ x, propagatorW (S.coeff N) 0 t φ x ∂(HRS.Whole.empirical ((R N).X 0 ζ))) -
        ∫ x, propagatorW (S.coeff N) 0 t φ x ∂S.μ0) := by
    intro ζ
    haveI := HRS.Whole.empirical_isProbabilityMeasure hN0 ((R N).X 0 ζ)
    haveI := S.hμ0
    exact sa6_riesz_U hT hadjN ht.1 htT _ _ _
  choose I' hI' using hex
  have hUc : ∀ φ : Euc d → ℝ, IsSobolevTest (Γ : ℝ) φ → Continuous (propagatorW (S.coeff N) 0 t φ) :=
    fun φ hφ => ((hadjN 0 t le_rfl ht.1 htT φ hφ).2.1).continuous
  have hI'meas0 : @Measurable _ _ (ℱ 0) _ I' := by
    refine @mrm_measurable_of_pairings d (Γ : ℝ) (R N).Ω (ℱ 0) I' (fun φ hφ => ?_)
    have : (fun ζ => HNeg.pairing φ (I' ζ)) = fun ζ => S.sigma N *
        (HRS.Whole.pair (HRS.Whole.empirical ((R N).X 0 ζ)) (propagatorW (S.coeff N) 0 t φ) -
          HRS.Whole.pair S.μ0 (propagatorW (S.coeff N) 0 t φ)) := by
      funext ζ; exact hI' ζ φ hφ
    rw [this]
    exact (((sa6_meas_pair_emp (m := ℱ 0) hN0 (hF.adapted 0) (hUc φ hφ)).sub_const _).const_mul _)
  have hI'meas : Measurable I' := hI'meas0.mono (ℱ.le 0) le_rfl
  have hX0eq : ∀ᵐ ζ ∂(R N).P, (R N).X 0 ζ = (R N).X₀ ζ := (flow_contact (hS.flow N hN1)).1.init
  have hae : ∀ᵐ ζ ∂(R N).P, Iemp N t ζ = I' ζ := by
    have := mrm_ae_eq_of_pairings (μ := (R N).P) (F := Iemp N t) (G := I') (fun _ => True)
      (fun ℓ => by
        filter_upwards [hinit.repr_emp N hN1 t ht _ (mrm_e_test (Γ : ℝ) ℓ), hX0eq] with ζ h1 h2 _
        rw [h1, hI' ζ _ (mrm_e_test (Γ : ℝ) ℓ), ← h2, ← sa6_AN_mul_kappa S N]
        simp only [HRS.Whole.pair]
        ring)
    filter_upwards [this] with ζ h
    exact h trivial
  set Rr : (R N).Ω → HNeg d (Γ : ℝ) := fun ζ => Ξ ζ - I' ζ - M t ζ with hRr
  have hMt : Measurable (M t) := (hMad t).mono (ℱ.le t) le_rfl
  have hRm : Measurable Rr := (hΞm.sub hI'meas).sub hMt
  have hRid := fun φ hφ => sa6_pairing_identity hS hadj hN1 ht hF hK M hMp Ξ I' hΞ
    (fun φ hφ => ae_of_all _ fun ζ => hI' ζ φ hφ) φ hφ
  have hpath := sa6_remainder_pathwise hS hΛ he hsel hN hinj ht Rr hRid
  refine ⟨ℱ, W', M, I', Rr, hF, hMad, hM, hIto, hI'meas0, hI'meas, hMt, hRm, fun ω => ?_, hae, hpath⟩
  simp only [hRr]; abel

theorem sa6_core_dC2
    (hS : RdStanding S R MB Λ ΛV G₀ m20 (Γ + 3) (Γ + 3) C₀ 𝔈) (hΛ : 1 ≤ Λ)
    (hadj : AdjointDerivInput (Γ : ℝ) (mStar d) S.coeff S.T Kad) (he : ∀ N, 0 ≤ e N)
    (hsel : SelectedCommutatorInput S (Γ : ℝ) S.T K' C₀ Λ e)
    (hCk : 0 ≤ Ck)
    (hCp : ∀ Λ' : ℝ, 1 ≤ Λ' → ∀ N' : ℕ, 2 ≤ N' → ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ Λ') →
      Integrable (fun x => ‖x‖ ^ 2 * ρ x) → ∀ X : EucConfig d N', Function.Injective X →
      ∀ h : Euc d → ℝ, cNormE χ h < ⊤ → ∀ Rr : ℝ, 1 ≤ Rr →
        |HRS.Whole.pair (HRS.Whole.empirical X) h - HRS.Whole.pair (HRS.Whole.withDensityReal ρ) h| ≤ Cp * (cNormE χ h).toReal *
          (Rr ^ ((d : ℝ) / 2) * (smearScale d N' Λ' + Real.sqrt (rieszModulatedEnergy d S.s X
            (HRS.Whole.withDensityReal ρ) + oNΛ d S.s C₀ Λ' N')) +
            (secondMomentOf (HRS.Whole.empirical X) + secondMomentOf (HRS.Whole.withDensityReal ρ)) / Rr ^ 2))
    (hm₂ : 0 ≤ m₂) (hm2 : PropagatedSecondMoment S R m₂)
    (hinit : TransportedInitialFieldRd S R Γ Cin εf Iemp I) (hdist : InitialFieldDist S R Γ εf Iemp I)
    {N : ℕ} (hN : 2 ≤ N) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T)
    (hinj : ∀ᵐ ζ ∂(R N).P, ∀ᵐ ρ ∂(volume.restrict (Set.Icc (0 : ℝ) S.T)),
      Function.Injective ((R N).X (Real.toNNReal ρ) ζ))
    {Kk : ℝ} {Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (Γ : ℝ)}
    (hK : Sa6Kern (S.coeff N) S.T Γ Kk Kern)
    (hcN : ∀ B : HNeg d (Γ : ℝ) →L[ℝ] HNeg d (Γ : ℝ),
      (∀ u v, inner ℝ (B u) v = inner ℝ u (B v)) → ‖B‖ ≤ 1 → ∀ σ ∈ Set.Icc (0 : ℝ) t,
        cNormE χ (fun z => ∑ j, inner ℝ (B (Kern j σ t z)) (Kern j σ t z)) ≤ ENNReal.ofReal Ck)
    {νG : Measure (HNeg d (Γ : ℝ))} (hνG : IsLinearFieldNoiseRd (S.coeff N) (S.qN N) t Γ νG)
    {Ξ : (R N).Ω → HNeg d (Γ : ℝ)} (hΞm : Measurable Ξ) (hΞ : IsFluctFieldRepr S R N Γ t Ξ) :
    smoothDist 2 (law (R N).P Ξ) (linearFieldLawRd (R N).P (I N t) νG) ≤
      (S.sigma N / 2 * max K' 0) * S.T * (𝔈 N + e N) +
        (1 / 2) * (t * (2 * S.qN N * max Cp 0 * Ck * wN d N (𝔈 N) m₂)) + εf N := by
  classical
  have hN1 : 1 ≤ N := by omega
  have hT : 0 ≤ S.T := S.hT.le
  have htT : t ≤ S.T := ht.2
  have hq := sa6_qN_nonneg S N
  have hσ := mrr_sigma_nonneg S N
  obtain ⟨ℱ, W', M, I', Rr, hF, hMad, hM, hIto, hI'meas0, hI'meas, hMt, hRm, hΞeq, hae, hpath⟩ :=
    sa6_decomp hS hΛ hadj he hsel hinit hN ht hinj hK hΞm hΞ
  have hlaw : law (R N).P (Iemp N t) = law (R N).P I' := Measure.map_congr hae
  have hc0 : 0 ≤ S.sigma N / 2 * max K' 0 := mul_nonneg (by positivity) (le_max_right _ _)
  have hL1 := sa6_remainder_L1 hS he hN1 hc0 Rr hpath hF
  have hkb : ∀ σ : ℝ, Sa6KBdd (fun j z => Kern j σ t z) Kk := fun σ => sa6_kslice hK htT σ
  have hprob : ∀ σ : ℝ, HRS.Whole.IsProbDensity (S.ρ N (mrrClamp S.T σ)) := fun σ =>
    (hS.mean_field.solution N hN1).density _ (mrrClamp_mem hT σ)
  have hρm : Measurable (fun p : ℝ × Euc d => S.ρ N (mrrClamp S.T p.1) p.2) := mrr_rho_meas hS hN1
  have hKm : ∀ j, Measurable (fun p : ℝ × Euc d => Kern j p.1 t p.2) :=
    fun j => sa6_kern_meas_joint hK htT j
  have hγ := sa6_gamma hK ht.1 htT hq hkb hprob hρm hνG
  have hsb := sa6_sb_det (q := S.qN N) (hkb := hkb) (ρ := fun σ => S.ρ N (mrrClamp S.T σ))
    (hprob := hprob) hq hρm hKm
  have hD := sa6_covDiscrepancy_le hS hΛ hN ht hF hK hkb hprob hinj hCk hcN hCp hm₂ hm2 M hM
  haveI : IsProbabilityMeasure (law (R N).P (I N t)) :=
    (Measure.isProbabilityMeasure_map_iff (hinit.meas N hN1 t ht).2.aemeasurable).2 inferInstance
  have h𝔈 : 0 ≤ 𝔈 N := (hS.energy.pos N hN1).le
  have hρR0 : 0 ≤ S.sigma N / 2 * max K' 0 * S.T * (𝔈 N + e N) :=
    mul_nonneg (mul_nonneg hc0 hT) (add_nonneg h𝔈 (he N))
  have hass := sa6_dC2_assembly (R N).P (hM t) ht.1 hsb hγ I' Rr hI'meas0 hRm.aemeasurable
    (law (R N).P (I N t)) _ hρR0 hL1
  have hfun : (fun ω => I' ω + M t ω + Rr ω) = Ξ := by
    funext ω; exact (hΞeq ω).symm
  rw [hfun] at hass
  have hsd : smoothDist 2 (law (R N).P I') (law (R N).P (I N t)) ≤ εf N := by
    rw [← hlaw]; exact hdist N hN1 t ht
  unfold linearFieldLawRd
  linarith [hass, hD, hsd]

end Core

end HRS.MS.MainRdField
