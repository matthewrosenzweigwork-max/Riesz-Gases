import HRS.Sections.AdjKEAux4

/-!
# ADJKE part 5: pairing of the particle martingale with non-smooth test functions

For the particle martingale `M` (any process with the smooth-test pairing property `hMid` of `B0`), the pairing with a test function
`ψ ∈ C² ∩ H^m` is the Itô integral of `η_ψ(s, ω, (i,j)) = (c₀/N) ∂_jψ(x_i(s))`, `c₀ = √N √(2β⁻¹)`:
`M_τ(ψ) = ∫_0^τ η_ψ dW'` a.s.  Route: the canonical Hilbert version `Mart` of the noise integral (as in B0), `M_τ = Mart_τ` a.s.
(equal smooth pairings), and `⟨Mart_τ, lpFun ψ⟩ = ∫ η_ψ dW'` (`gfb3_pair_ito`, `inner_bVec_lpFun`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjK

open HRS HRS.Uniform HRS.GF HRS.Uniform.Q54c

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

/-- The integrand `η_ψ(s, ω, (i,j)) = c ∂_jψ(x_i(s))` of the pairing of the noise with `ψ`. -/
def adjkeEta {Ω : Type*} {N : ℕ} (c : ℝ) (X : ℝ≥0 → Ω → Config d N) (ψ : Torus d → ℝ) :
    ℝ → Ω → (Fin N × Fin d) → ℝ :=
  fun s ω k => c * Torus.partialDeriv k.2 ψ (X (Real.toNNReal s) ω k.1)

theorem adjke_eta_L2 {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {N : ℕ} (c : ℝ) {X : ℝ≥0 → Ω → Config d N}
    (hX : IsProgressive ℱ (ofNNRealTime X)) {ψ : Torus d → ℝ} (h2 : Torus.IsCk 2 ψ) :
    IsProgressiveL2 P ℱ (adjkeEta c X ψ) := by
  have h1 : Torus.IsCk 1 ψ := h2.of_le (by norm_num)
  have hprog : IsProgressive ℱ (adjkeEta c X ψ) := by
    intro i
    have hg : Measurable fun x : Config d N => fun k : Fin N × Fin d =>
        c * Torus.partialDeriv k.2 ψ (x k.1) :=
      measurable_pi_iff.2 fun k => measurable_const.mul
        ((HRS.PDE.continuous_partialDeriv k.2 ψ h1).measurable.comp (measurable_pi_apply k.1))
    exact hg.comp (hX i)
  exact IsProgressiveL2.of_bounded P hprog (|c| * Torus.cbNorm 2 ψ) (fun s ω k => by
    unfold adjkeEta
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (HRS.PDE.MFPair.abs_partialDeriv_le (L := 2) (by norm_num) h2 _ _) (abs_nonneg _))

theorem adjke_eval_realMode {m : ℝ} (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.eval F (Torus.realMode k) = NegSobolev.fourierCoeff F k := by
  classical
  unfold NegSobolev.eval
  rw [tsum_eq_single k]
  · unfold Torus.funRealCoeff
    rw [Torus.realMode_orthonormal k k]
    simp
  · intro l hl
    unfold Torus.funRealCoeff
    rw [Torus.realMode_orthonormal l k, if_neg hl]
    simp

/-- The canonical Hilbert version of the particle noise integral at level `m`. -/
theorem adjke_mart (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    {m : ℝ} (hn : (d : ℝ) / 2 + 2 < m) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsFilteredSolution P ℱ W' W X) :
    ∃ Mart : ℝ → Ω → NegSobolev d m, IsHilbertItoIntegral P ℱ W'
      (noiseIntegrand m (Real.sqrt N * Real.sqrt (2 * β⁻¹)) (fun r => X (Real.toNNReal r))) Mart := by
  set c0 : ℝ := Real.sqrt N * Real.sqrt (2 * β⁻¹) with hc0
  have hW : IsCylindricalBrownian P ℱ W' := gfb3_isCylindricalBrownian_of_filtration hF.brownian
  have hZ := HRS.AdjKC.adjkc_noise_isHS hn N c0 P ℱ W' W X hF
  obtain ⟨Mart, hc', had, hz, hJ⟩ := gfb3_exists_hilbert_version hW hZ
  refine ⟨Mart, hc', had, hz, ?_⟩
  intro τ hτ x
  obtain ⟨J, hIJ, hae⟩ := hJ x
  refine (hIJ.approx τ hτ).congr fun s => ?_
  refine lintegral_congr_ae ?_
  filter_upwards [hae τ hτ] with ω h
  rw [h]
  rfl

/-- The pairing of `Mart_τ` with `lpFun m ψ` is the Itô integral of `η_ψ`. -/
theorem adjke_mart_pair {m : ℝ} (hn : (d : ℝ) / 2 + 2 < m) {N : ℕ}
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N} {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hF : IsFilteredSolution P ℱ W' W X) (c0 : ℝ)
    {Mart : ℝ → Ω → NegSobolev d m}
    (hMart : IsHilbertItoIntegral P ℱ W' (noiseIntegrand m c0 (fun r => X (Real.toNNReal r))) Mart)
    {ψ : Torus d → ℝ} (h2 : Torus.IsCk 2 ψ) (hψm : MemSobolev m ψ) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∀ᵐ ω ∂P, inner ℝ (Mart τ ω) (lpFun m ψ) = itoIntegral P ℱ W' (adjkeEta (c0 / N) X ψ) τ ω := by
  have hc : Continuous ψ :=
    Torus.continuous_of_continuous_lift (show ContDiff ℝ 2 (Torus.lift ψ) from h2).continuous
  have h1 : Torus.IsCk 1 ψ := h2.of_le (by norm_num)
  have hpairη : ∀ s ω k, inner ℝ (noiseIntegrand m c0 (fun r => X (Real.toNNReal r)) s ω k)
      (lpFun m ψ) = adjkeEta (c0 / N) X ψ s ω k := by
    intro s ω k
    unfold noiseIntegrand adjkeEta
    rw [real_inner_smul_left, inner_bVec_lpFun hn hψm hc h1]
  have hη_L2 : IsProgressiveL2 P ℱ (adjkeEta (c0 / N) X ψ) := adjke_eta_L2 _ hF.progressive h2
  have hfun : (fun r' ω (k : Fin N × Fin d) => inner ℝ
      (noiseIntegrand m c0 (fun r => X (Real.toNNReal r)) r' ω k) (lpFun m ψ)) =
      adjkeEta (c0 / N) X ψ := by
    funext r' ω k; exact hpairη r' ω k
  have hξ' : IsProgressiveL2 P ℱ (fun r' ω (k : (Finset.univ : Finset (Fin N × Fin d))) =>
      inner ℝ (noiseIntegrand m c0 (fun r => X (Real.toNNReal r)) r' ω k) (lpFun m ψ)) := by
    have := gfb3_isProgressiveL2_restrict_univ hη_L2
    have heq : (fun r' ω (k : (Finset.univ : Finset (Fin N × Fin d))) =>
        inner ℝ (noiseIntegrand m c0 (fun r => X (Real.toNNReal r)) r' ω k) (lpFun m ψ)) =
        fun r' ω (k : (Finset.univ : Finset (Fin N × Fin d))) => adjkeEta (c0 / N) X ψ r' ω k := by
      funext r' ω k; exact hpairη r' ω k
    rw [heq]; exact this
  have hpair := gfb3_pair_ito hF.brownian hMart (lpFun m ψ) hξ' hτ
  rw [hfun] at hpair
  exact hpair

/-- `∫ η_φ dW' = √N · M_N[φ]` on `[0,T]`, for the constant-in-time test `φ ∈ C²`. -/
theorem adjke_ito_eta_eq (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {N : ℕ} (hN : 0 < N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N} {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hF : IsFilteredSolution P ℱ W' W X) {T : ℝ} (hT : 0 ≤ T)
    {φ : Torus d → ℝ} (hφ2 : Torus.IsCk 2 φ) :
    ∀ᵐ ω ∂P, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      itoIntegral P ℱ W' (adjkeEta ((Real.sqrt N * Real.sqrt (2 * β⁻¹)) / N) X φ) τ ω =
        Real.sqrt N * empiricalMartingale P ℱ W' htr.dyn T (fun _ => φ) X τ ω := by
  have hC : IsC12Test T (fun _ : ℝ => φ) (fun _ _ => (0 : ℝ)) := by
    have hlift : ContDiff ℝ 2 (Torus.lift φ) := hφ2
    exact ⟨fun _ _ => hφ2, fun j hj => (hlift.continuous_iteratedFDeriv (m := j)
        (by exact_mod_cast hj)).comp continuous_snd,
      fun x r _ => hasDerivAt_const _ _, continuous_const⟩
  set η := adjkeEta ((Real.sqrt N * Real.sqrt (2 * β⁻¹)) / N) X φ with hη
  set E := empiricalNoiseIntegrand htr.dyn T (fun _ : ℝ => φ) X with hE
  have hη_L2 : IsProgressiveL2 P ℱ η := adjke_eta_L2 _ hF.progressive hφ2
  have hEL2 : IsProgressiveL2 P ℱ E := isProgressiveL2_empiricalNoiseIntegrand hF.progressive hT hC
  have hEη : ∀ s ∈ Set.Ioc (0 : ℝ) T, ∀ ω k, η s ω k = Real.sqrt N * E s ω k := by
    intro s hs ω k
    have hs' : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1.le, hs.2⟩
    simp only [hE, hη, adjkeEta, empiricalNoiseIntegrand, if_pos hs']
    rw [HRS.Duality.grad_apply_eq_partialDeriv]
    show (Real.sqrt N * Real.sqrt (2 * β⁻¹)) / N * _ = Real.sqrt N * (Real.sqrt (2 * β⁻¹) / N * _)
    ring
  set A : ℝ → Ω → (Fin N × Fin d) → ℝ := fun s ω =>
    Set.indicator (Set.Ioc (0 : ℝ) T) (fun _ => η s ω) s with hA
  have hAL2 : IsProgressiveL2 P ℱ A := by
    have hΨ : A = restrictFun η 0 T Set.univ := by
      funext s ω; simp [hA, restrictFun, Set.indicator]
    rw [hΨ]
    exact hη_L2.restrictFun (MeasurableSet.univ : MeasurableSet[ℱ 0] (Set.univ : Set Ω))
  have hind := itoIntegral_indicator_Ioc hF.brownian hη_L2 (le_refl (0 : ℝ)) hT
  have hcongr : ∀ᵐ ω ∂P, ∀ t, itoIntegral P ℱ W' A t ω =
      itoIntegral P ℱ W' (fun s ω => Real.sqrt N • E s ω) t ω := by
    refine itoIntegral_congr hF.brownian hAL2 (hEL2.smul _) fun T' => ?_
    unfold sqIntegralOn
    have h0 : ∀ᵐ s : ℝ ∂(volume : Measure ℝ), s ≠ 0 := by rw [ae_iff]; simp
    have hpt : ∀ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∑ k, ‖(A s ω - Real.sqrt N • E s ω) k‖ₑ ^ 2 = 0 := by
      intro ω
      have hae : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T')),
          ∑ k, ‖(A s ω - Real.sqrt N • E s ω) k‖ₑ ^ 2 = 0 :=
        ae_restrict_of_ae (h0.mono fun s hs0 => Finset.sum_eq_zero fun k _ => by
          have hk : (A s ω - Real.sqrt N • E s ω) k = 0 := by
            by_cases hs : s ∈ Set.Ioc (0 : ℝ) T
            · simp only [hA, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Set.indicator_of_mem hs]
              rw [hEη s hs ω k]; ring
            · have hsn : s ∉ Set.Icc (0 : ℝ) T := fun h => hs ⟨lt_of_le_of_ne h.1 (Ne.symm hs0), h.2⟩
              simp only [hA, hE, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Set.indicator_of_notMem hs,
                empiricalNoiseIntegrand, if_neg hsn]
              simp
          rw [hk]; simp)
      exact (lintegral_congr_ae hae).trans lintegral_zero
    simp only [hpt, lintegral_zero]
  have hsm := itoIntegral_smul hF.brownian hEL2 (Real.sqrt N)
  filter_upwards [hind, hcongr, hsm] with ω h2 h3 h4 τ hτ
  have h5 := h2 τ
  rw [min_eq_left hτ.2, min_eq_right hτ.1, itoIntegral_of_nonpos P ℱ W' η (le_refl (0 : ℝ)) ω,
    sub_zero] at h5
  rw [← h5, h3 τ, h4 τ]
  rfl

/-- **Pairing of `M_τ` with a `C² ∩ H^m` test function.** -/
theorem adjke_pairing (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    {m : ℝ} (hn : (d : ℝ) / 2 + 2 < m) (T : ℝ) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N} {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hF : IsFilteredSolution P ℱ W' W X) (hT : 0 ≤ T)
    (M : ℝ → Ω → NegSobolev d m)
    (hMid : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
      NegSobolev.eval (M t ω) φ =
        Real.sqrt N * empiricalMartingale P ℱ W' htr.dyn T (fun _ => φ) X t ω)
    {ψ : Torus d → ℝ} (h2 : Torus.IsCk 2 ψ) (hψm : MemSobolev m ψ) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) T) :
    ∀ᵐ ω ∂P, NegSobolev.eval (M τ ω) ψ =
      itoIntegral P ℱ W' (adjkeEta ((Real.sqrt N * Real.sqrt (2 * β⁻¹)) / N) X ψ) τ ω := by
  obtain ⟨Mart, hMart⟩ := adjke_mart hd htr hn hN P W X ℱ W' hF
  set c0 : ℝ := Real.sqrt N * Real.sqrt (2 * β⁻¹) with hc0
  -- equality of the smooth pairings
  have hsm : ∀ k : NonzeroLattice d, ∀ᵐ ω ∂P,
      NegSobolev.eval (M τ ω) (Torus.realMode k) = NegSobolev.eval (Mart τ ω) (Torus.realMode k) := by
    intro k
    have hφ : Torus.IsSmooth (Torus.realMode k) := HRS.FieldSingAux.isSmooth_realMode k
    obtain ⟨hφ2, hφm⟩ := gf_smooth_mem_proof hφ m
    have hN0 : 0 < N := by omega
    filter_upwards [hMid _ hφ τ hτ, adjke_mart_pair hn P hF c0 hMart hφ2 hφm hτ.1,
      adjke_ito_eta_eq htr hN0 P hF hT hφ2] with ω h1 h2 h3
    rw [h1, eval_lpFun (Mart τ ω) hφm, h2, h3 τ hτ]
  have hall : ∀ᵐ ω ∂P, ∀ k : NonzeroLattice d,
      NegSobolev.eval (M τ ω) (Torus.realMode k) = NegSobolev.eval (Mart τ ω) (Torus.realMode k) :=
    ae_all_iff.2 hsm
  have heq : ∀ᵐ ω ∂P, M τ ω = Mart τ ω := by
    filter_upwards [hall] with ω hω
    refine NegSobolev_ext fun k => ?_
    have h1 := hω k
    rw [adjke_eval_realMode, adjke_eval_realMode] at h1
    have hj : Lattice.jp k.1 ^ m ≠ 0 := (Real.rpow_pos_of_pos (Torus.jp_pos k.1) m).ne'
    have e1 : NegSobolev.fourierCoeff (M τ ω) k = Lattice.jp k.1 ^ m * NegSobolev.coord (M τ ω) k := rfl
    have e2 : NegSobolev.fourierCoeff (Mart τ ω) k = Lattice.jp k.1 ^ m * NegSobolev.coord (Mart τ ω) k := rfl
    rw [e1, e2] at h1
    exact mul_left_cancel₀ hj h1
  filter_upwards [heq, adjke_mart_pair hn P hF c0 hMart h2 hψm hτ.1] with ω h1 h2'
  rw [h1, eval_lpFun (Mart τ ω) hψm, h2']

end HRS.AdjK
