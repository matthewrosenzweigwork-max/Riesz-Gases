import HRS.MS.MainRdPathAux19

/-!
# S.A.9, packet P3n: fixed-time tightness of the particle field `Z_N^t`, and the tightness of the path laws

* `sa9_Rm_L1`: `E‖Rm_N^t‖ ≤ C T σ_N(𝔈_N + e_N)` (from the sup bound of S.A.25 for the continuous version);
* `sa9_fix_tight`: for `t ∈ [0,T]` the laws of `Z_N^t`, `N ≥ 1`, are tight in `H^{-(Γ+2)}`
  (tails of `Iq`, `Mq`, `L¹`-smallness of `Rm`);
* `sa9_path_tight`: the laws of every measurable path representative `Ξ_N`, `N ≥ 2`, are tight in `C([0,T]; H^{-(Γ+2)})`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdPath

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.HNegInfra HRS.MP.RdInit
  HRS.MP.RdMart HRS.MP.RdRem HRS.MP.RdProp HRS.MS.MainRdField HRS.MP.KC

variable {d : ℕ} {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {Γ : ℕ}

theorem sa9_Rm_L1 {MB Λ ΛV G₀ m20 C₀ : ℝ} {𝔈 : ℕ → ℝ} {C₁ m₂ K' : ℝ} {e : ℕ → ℝ}
    (B : Sa9Bundle S R Γ) (hS : RdStanding S R MB Λ ΛV G₀ m20 (Γ + 5) (Γ + 5) C₀ 𝔈) (hΛ : 1 ≤ Λ)
    (hm₂ : PropagatedSecondMoment S R m₂)
    (hker : ∀ N : ℕ, 1 ≤ N → KernelBoundRd (S.coeff N) S.T (Γ + 2) C₁)
    (he : ∀ N, 0 ≤ e N) (hsel : SelectedCommutatorInput S (Γ : ℝ) S.T K' C₀ Λ e)
    {N : ℕ} (hN : 2 ≤ N) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) :
    ∫⁻ ζ, ‖B.Rm N t ζ‖ₑ ∂(R N).P ≤
      ENNReal.ofReal (max K' 0 / 2 * S.T * S.sigma N * (𝔈 N + e N)) := by
  classical
  have hMc := sa9_martingale_tight hS hm₂ hker B.ℱ B.W' B.hfilt B.Mq B.hMq
  set Mc : ∀ N, ℝ → (R N).Ω → HNeg d ((Γ + 2 : ℕ) : ℝ) := fun N => mkc_Zc (B.Mq N) S.T mrmR with hMcdef
  set Rc : ∀ N, ℝ → (R N).Ω → HNeg d ((Γ + 2 : ℕ) : ℝ) :=
    fun N t ζ => B.Z N t ζ - B.Ic N t ζ - Mc N t ζ with hRcdef
  have hHas : HasContVersion S.T (R N).P (B.Rm N) (Rc N) := by
    refine ⟨fun t ht => ?_, ?_⟩
    · filter_upwards [B.hIc.1 N (by omega) t ht, hMc.1 N (by omega) t ht] with ζ h1 h2
      simp only [hRcdef]
      rw [B.hdec N (by omega) t ht ζ, h1, h2]
    · filter_upwards [B.hZc N (by omega), B.hIc.2.1 N (by omega), hMc.2.1 N (by omega)] with ζ h1 h2 h3
      exact continuousOn_iff_continuous_restrict.2 ((h1.sub h2).sub h3)
  have hper := sa9_perN hS hΛ he hsel hN (sa6_inj_N hS (by omega)) (B.Rm N) (Rc N) (B.hRm N (by omega)) hHas
  refine le_trans (lintegral_mono_ae ?_) hper
  filter_upwards [hHas.1 t ht] with ζ h
  rw [← h]
  exact le_iSup₂ (f := fun t' (_ : t' ∈ Set.Icc (0 : ℝ) S.T) => ‖Rc N t' ζ‖ₑ) t ht

theorem sa9_fix_tight {MB Λ ΛV G₀ m20 C₀ : ℝ} {𝔈 : ℕ → ℝ} {C₁ m₂ K' : ℝ} {e : ℕ → ℝ}
    (B : Sa9Bundle S R Γ) (hS : RdStanding S R MB Λ ΛV G₀ m20 (Γ + 5) (Γ + 5) C₀ 𝔈) (hΛ : 1 ≤ Λ)
    (hm₂0 : 0 ≤ m₂) (hm₂ : PropagatedSecondMoment S R m₂)
    (hker : ∀ N : ℕ, 1 ≤ N → KernelBoundRd (S.coeff N) S.T (Γ + 2) C₁)
    (he : ∀ N, 0 ≤ e N) (hsel : SelectedCommutatorInput S (Γ : ℝ) S.T K' C₀ Λ e)
    (hsmall : Tendsto (fun N => S.sigma N * (𝔈 N + e N)) atTop (𝓝 0))
    {m₀ : ℕ} (hm₀ : 1 ≤ m₀) {χ : Euc d → ℝ} {Cin : ℝ} {ε : ℕ → ℝ}
    (hinit : InitialFluctuationRd S R χ m₀ Cin ε (fun _ => ∅))
    {εf : ℕ → ℝ} {Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (Γ : ℝ)}
    (hTIF : TransportedInitialFieldRd S R Γ Cin εf Iemp I)
    {Kadj Kst : ℝ} (hAdjP : AdjointDerivInput ((Γ + 2 : ℕ) : ℝ) (m₀ + 1) S.coeff S.T Kadj)
    (L : LimitCoeffsRd d) (hAdjL : AdjointInputOneD ((Γ + 2 : ℕ) : ℝ) (m₀ + 1) (L.coeff S) S.T Kadj)
    (hStab : AdjointStabilityInputRd S L (Γ + 2) (m₀ + 1) Γ Kst)
    (hΔ : Tendsto (fun N => coeffDiscrepancyRd S L Γ N) atTop (𝓝 0))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) :
    IsTightMeasureSet {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = (R N).P.map (B.Z N t)} := by
  classical
  obtain ⟨h, hP⟩ := mri_parseval_h (d := d) ((Γ + 2 : ℕ) : ℝ)
  have hc := sa9_cH_parseval (q := Γ + 2) h hP
  set J : Set ℕ := {N | 1 ≤ N} with hJ
  have hconv : ∀ (F : ∀ N, (R N).Ω → HNeg d ((Γ + 2 : ℕ) : ℝ)) (Lc N : ℕ),
      ∫⁻ ζ, ENNReal.ofReal (sa9_tail (sa9_cH (Γ + 2) h) Lc (F N ζ)) ∂(R N).P =
        ∫⁻ ζ, ∑' l, ENNReal.ofReal ((HNeg.pairing (mhn_phi (h (l + Lc))) (F N ζ)) ^ 2) ∂(R N).P :=
    fun F Lc N => lintegral_congr fun ζ => by rw [sa9_ofReal_tail hc]; simp only [sa9_cH_apply]
  have hIqT : Sa9TightFam J (fun N => (R N).P) (fun N ζ => B.Iq N t ζ) := by
    refine sa9_tightFam_of_tails (fun N => (R N).P) hc J (fun N ζ => B.Iq N t ζ)
      (fun N hN => B.hIqm N hN t) (B := Cin ^ 2) (fun N hN => ?_) ?_
    · have := sa9_Iq_moment B hTIF hN ht
      exact this
    · refine sa9_tails_all (fun N => (R N).P) hc J _ (fun N hN => B.hIqm N hN t) (fun N hN =>
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top (sa9_Iq_moment B hTIF hN ht)) ?_
      intro η hη
      obtain ⟨Lc, N₀, hLN⟩ := sa9_Iq_tail B h hP hinit hAdjP L hAdjL hStab hΔ ht hη
      exact ⟨Lc, N₀, fun N hN hNN => by rw [hconv (fun N ζ => B.Iq N t ζ)]; exact hLN N hNN hN⟩
  have hMqT : Sa9TightFam J (fun N => (R N).P) (fun N ζ => B.Mq N t ζ) := by
    refine sa9_tightFam_of_tails (fun N => (R N).P) hc J (fun N ζ => B.Mq N t ζ)
      (fun N hN => (B.hMq N hN).1 t) (B := 2 * d * Kadj ^ 2 * t) (fun N hN => ?_) ?_
    · exact sa9_Mq_moment B h hP hN (hAdjP N hN) ht
    · refine sa9_tails_all (fun N => (R N).P) hc J _ (fun N hN => (B.hMq N hN).1 t) (fun N hN =>
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top (sa9_Mq_moment B h hP hN (hAdjP N hN) ht)) ?_
      intro η hη
      obtain ⟨Lc, N₀, hLN⟩ := sa9_Mq_tail B h hP hm₀ hAdjP L hAdjL hStab hΔ hm₂0 hm₂ ht hη
      exact ⟨Lc, N₀, fun N hN hNN => by rw [hconv (fun N ζ => B.Mq N t ζ)]; exact hLN N hNN hN⟩
  have hRmT : Sa9TightFam J (fun N => (R N).P) (fun N ζ => B.Rm N t ζ) := by
    have hc0 : Tendsto (fun N => max K' 0 / 2 * S.T * S.sigma N * (𝔈 N + e N)) atTop (𝓝 0) := by
      have := hsmall.const_mul (max K' 0 / 2 * S.T)
      rw [mul_zero] at this
      refine this.congr fun N => ?_
      ring
    have h2 := sa9_tightFam_of_l1 (fun N => (R N).P) {N | 2 ≤ N} (fun N ζ => B.Rm N t ζ)
      (fun N hN => (B.hRm N (by simp at hN; omega)).1 t)
      (fun N => max K' 0 / 2 * S.T * S.sigma N * (𝔈 N + e N)) hc0
      (fun N hN => sa9_Rm_L1 B hS hΛ hm₂ hker he hsel hN ht)
    have h1 := sa9_tightFam_single (fun N => (R N).P) 1 (fun N ζ => B.Rm N t ζ) ((B.hRm 1 le_rfl).1 t)
    refine sa9_tightFam_mono _ (sa9_tightFam_union _ h1 h2) ?_
    intro N hN
    by_cases hN1 : N = 1
    · exact Or.inl hN1
    · have hN' : 1 ≤ N := hN
      exact Or.inr (show 2 ≤ N by omega)
  have hsum := sa9_tightFam_add _ (sa9_tightFam_add _ hIqT hMqT) hRmT
  have hZT : Sa9TightFam J (fun N => (R N).P) (fun N ζ => B.Z N t ζ) := by
    intro ε hε
    obtain ⟨K, hK, hKe⟩ := hsum ε hε
    refine ⟨K, hK, fun N hN => ?_⟩
    refine le_trans (le_of_eq (congrArg _ ?_)) (hKe N hN)
    ext ζ
    simp only [Set.mem_ofPred_eq]
    rw [B.hdec N hN t ht ζ]
    congr! 2
    abel
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨K, hK, hKe⟩ := hZT ε hε
  refine ⟨K, hK, ?_⟩
  rintro _ ⟨N, hN, rfl⟩
  rw [Measure.map_apply (B.hZm N hN t) hK.isClosed.measurableSet.compl]
  exact hKe N hN

/-- **P1-P4.**  Under the hypotheses of `main_rd_path` (at the level `Γ + 2`) the laws of every measurable path
representative `Ξ_N`, `N ≥ 2`, are tight in `C([0,T]; H^{-(Γ+2)})`; the bundle `B` exists by `sa9_bundle_exists`. -/
theorem sa9_path_tight {MB Λ ΛV G₀ m20 C₀ : ℝ} {𝔈 : ℕ → ℝ} {C₁ m₂ K' : ℝ} {e : ℕ → ℝ}
    (B : Sa9Bundle S R Γ) (hS : RdStanding S R MB Λ ΛV G₀ m20 (Γ + 5) (Γ + 5) C₀ 𝔈) (hΛ : 1 ≤ Λ)
    (hm₂0 : 0 ≤ m₂) (hm₂ : PropagatedSecondMoment S R m₂)
    (hker : ∀ N : ℕ, 1 ≤ N → KernelBoundRd (S.coeff N) S.T (Γ + 2) C₁)
    (he : ∀ N, 0 ≤ e N) (hsel : SelectedCommutatorInput S (Γ : ℝ) S.T K' C₀ Λ e)
    (hsmall : Tendsto (fun N => S.sigma N * (𝔈 N + e N)) atTop (𝓝 0))
    {m₀ : ℕ} (hm₀ : 1 ≤ m₀) {χ : Euc d → ℝ} {Cin : ℝ} {ε : ℕ → ℝ}
    (hinit : InitialFluctuationRd S R χ m₀ Cin ε (fun _ => ∅))
    {εf : ℕ → ℝ} {Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (Γ : ℝ)}
    (hTIF : TransportedInitialFieldRd S R Γ Cin εf Iemp I)
    {Kadj Kst : ℝ} (hAdjP : AdjointDerivInput ((Γ + 2 : ℕ) : ℝ) (m₀ + 1) S.coeff S.T Kadj)
    (L : LimitCoeffsRd d) (hAdjL : AdjointInputOneD ((Γ + 2 : ℕ) : ℝ) (m₀ + 1) (L.coeff S) S.T Kadj)
    (hStab : AdjointStabilityInputRd S L (Γ + 2) (m₀ + 1) Γ Kst)
    (hΔ : Tendsto (fun N => coeffDiscrepancyRd S L Γ N) atTop (𝓝 0))
    (Ξ : ∀ N, (R N).Ω → HNegPath d ((Γ + 2 : ℕ) : ℝ) S.T)
    (hΞ : ∀ N : ℕ, 1 ≤ N → IsFluctPathRepr S R N (Γ + 2) (Ξ N)) :
    IsTightMeasureSet {μ | ∃ N : ℕ, 2 ≤ N ∧ μ = (R N).P.map (Ξ N)} :=
  sa9_tight_reps B hS hΛ hm₂ hker he hsel hsmall (fun t ht =>
    sa9_fix_tight B hS hΛ hm₂0 hm₂ hker he hsel hsmall hm₀ hinit hTIF hAdjP L hAdjL hStab hΔ ht) Ξ hΞ

end HRS.MS.MainRdPath
