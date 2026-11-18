import HRS.Sections.AdjKCAux4
import HRS.Duality.PairingExpansion

/-!
# ADJKC Aux5: packet B0, the particle martingale and the identification of its pairings
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjKC

open HRS HRS.Uniform HRS.GF HRS.Uniform.Q54c

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem adjkc_particle_martingale (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    (n : ℝ) (hn : (d : ℝ) / 2 + 2 < n) (T : ℝ) (hT : 0 < T) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsParticleSystem P htr.dyn T X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsFilteredSolution P ℱ W' W X) :
    ∃ M : ℝ → Ω → NegSobolev d n,
      IsHilbertMartingaleWithCovariation P ℱ T M
        (fun r ω => covForm n β⁻¹ (empirical (X r.toNNReal ω))) ∧
      ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
        NegSobolev.eval (M t ω) φ =
          Real.sqrt N * empiricalMartingale P ℱ W' htr.dyn T (fun _ => φ) X t ω := by
  have hq : 0 ≤ β⁻¹ := inv_nonneg.2 htr.hβ.le
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set c0 : ℝ := Real.sqrt N * Real.sqrt (2 * β⁻¹) with hc0
  have hc : (c0 / N) ^ 2 = 2 * β⁻¹ / N := by
    rw [hc0, div_pow, mul_pow, Real.sq_sqrt hNr.le, Real.sq_sqrt (by positivity)]
    field_simp
  have hW : IsCylindricalBrownian P ℱ W' := gfb3_isCylindricalBrownian_of_filtration hF.brownian
  have hZ := adjkc_noise_isHS hn N c0 P ℱ W' W X hF
  obtain ⟨Mart, hc', had, hz, hJ⟩ := gfb3_exists_hilbert_version hW hZ
  have hMartIto : IsHilbertItoIntegral P ℱ W'
      (noiseIntegrand n c0 (fun r => X (Real.toNNReal r))) Mart := by
    refine ⟨hc', had, hz, ?_⟩
    intro τ hτ x
    obtain ⟨J, hIJ, hae⟩ := hJ x
    refine (hIJ.approx τ hτ).congr fun s => ?_
    refine lintegral_congr_ae ?_
    filter_upwards [hae τ hτ] with ω h
    rw [h]
    rfl
  refine ⟨Mart, ?_, ?_⟩
  · have hM := HRS.Uniform.Q07c.isHM_of_ito hW (fun T => adjkc_noise_isHS hn N c0 P ℱ W' W X hF T)
      hc' had hz hJ T
    have hfun : (fun r ω => hsCovForm
        (noiseIntegrand n c0 (fun r => X (Real.toNNReal r)) r ω)) =
        fun r ω => covForm n β⁻¹ (empirical (X (Real.toNNReal r) ω)) := by
      funext r ω
      exact adjkc_hsCov_eq_covForm hn hq N (by omega) c0 hc _
    rw [hfun] at hM
    exact hM
  · intro φ hφ t ht
    obtain ⟨hφ2, hφm⟩ := gf_smooth_mem_proof hφ n
    have hφc : Continuous φ :=
      Torus.continuous_of_continuous_lift (show ContDiff ℝ 2 (Torus.lift φ) from hφ2).continuous
    have hφ1 : Torus.IsCk 1 φ := hφ2.of_le (by norm_num)
    set η : ℝ → Ω → (Fin N × Fin d) → ℝ := fun s ω k =>
      (c0 / N) * Torus.partialDeriv k.2 φ (X (Real.toNNReal s) ω k.1) with hη
    have hη_prog : IsProgressive ℱ η := by
      intro i
      have hg : Measurable fun x : Config d N => fun k : Fin N × Fin d =>
          (c0 / N) * Torus.partialDeriv k.2 φ (x k.1) :=
        measurable_pi_iff.2 fun k => measurable_const.mul
          ((HRS.PDE.continuous_partialDeriv k.2 φ hφ1).measurable.comp (measurable_pi_apply k.1))
      exact hg.comp (hF.progressive i)
    have hη_L2 : IsProgressiveL2 P ℱ η :=
      IsProgressiveL2.of_bounded P hη_prog (|c0 / N| * Torus.cbNorm 2 φ) (fun s ω k => by
        rw [hη]; simp only
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (HRS.PDE.MFPair.abs_partialDeriv_le (L := 2) (by norm_num) hφ2 _ _) (abs_nonneg _))
    have hpairη : ∀ s ω k, inner ℝ (noiseIntegrand n c0 (fun r => X (Real.toNNReal r)) s ω k)
        (lpFun n φ) = η s ω k := by
      intro s ω k
      unfold noiseIntegrand
      rw [real_inner_smul_left, inner_bVec_lpFun hn hφm hφc hφ1]
    have hfun : (fun r' ω (k : Fin N × Fin d) => inner ℝ
        (noiseIntegrand n c0 (fun r => X (Real.toNNReal r)) r' ω k) (lpFun n φ)) = η := by
      funext r' ω k; exact hpairη r' ω k
    have hξ' : IsProgressiveL2 P ℱ (fun r' ω (k : (Finset.univ : Finset (Fin N × Fin d))) =>
        inner ℝ (noiseIntegrand n c0 (fun r => X (Real.toNNReal r)) r' ω k) (lpFun n φ)) := by
      have := gfb3_isProgressiveL2_restrict_univ hη_L2
      have heq : (fun r' ω (k : (Finset.univ : Finset (Fin N × Fin d))) =>
          inner ℝ (noiseIntegrand n c0 (fun r => X (Real.toNNReal r)) r' ω k) (lpFun n φ)) =
          fun r' ω (k : (Finset.univ : Finset (Fin N × Fin d))) => η r' ω k := by
        funext r' ω k; exact hpairη r' ω k
      rw [heq]; exact this
    have hpair := gfb3_pair_ito hF.brownian hMartIto (lpFun n φ) hξ' ht.1
    rw [hfun] at hpair
    -- the empirical integrand
    have hC : IsC12Test T (fun _ : ℝ => φ) (fun _ _ => (0 : ℝ)) := by
      have hlift : ContDiff ℝ 2 (Torus.lift φ) := hφ2
      exact ⟨fun _ _ => hφ2, fun j hj => (hlift.continuous_iteratedFDeriv (m := j)
          (by exact_mod_cast hj)).comp continuous_snd,
        fun x r _ => hasDerivAt_const _ _, continuous_const⟩
    set E := empiricalNoiseIntegrand htr.dyn T (fun _ : ℝ => φ) X with hE
    have hEL2 : IsProgressiveL2 P ℱ E :=
      isProgressiveL2_empiricalNoiseIntegrand hF.progressive hT.le hC
    have hEη : ∀ s ∈ Set.Ioc (0 : ℝ) T, ∀ ω k, η s ω k = Real.sqrt N * E s ω k := by
      intro s hs ω k
      have hs' : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1.le, hs.2⟩
      simp only [hE, hη, empiricalNoiseIntegrand, if_pos hs']
      rw [HRS.Duality.grad_apply_eq_partialDeriv]
      show c0 / N * _ = Real.sqrt N * (Real.sqrt (2 * β⁻¹) / N * _)
      rw [hc0]; ring
    set A : ℝ → Ω → (Fin N × Fin d) → ℝ := fun s ω =>
      Set.indicator (Set.Ioc (0 : ℝ) T) (fun _ => η s ω) s with hA
    have hAL2 : IsProgressiveL2 P ℱ A := by
      have hΨ : A = restrictFun η 0 T Set.univ := by
        funext s ω; simp [hA, restrictFun, Set.indicator]
      rw [hΨ]
      exact hη_L2.restrictFun (MeasurableSet.univ : MeasurableSet[ℱ 0] (Set.univ : Set Ω))
    have hind := itoIntegral_indicator_Ioc hF.brownian hη_L2 (le_refl (0 : ℝ)) hT.le
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
    filter_upwards [hpair, hind, hcongr, hsm] with ω h1 h2 h3 h4
    have h5 := h2 t
    rw [min_eq_left ht.2, min_eq_right ht.1, itoIntegral_of_nonpos P ℱ W' η (le_refl (0 : ℝ)) ω,
      sub_zero] at h5
    rw [eval_lpFun (Mart t ω) hφm, h1, ← h5, h3 t, h4 t]
    rfl

end HRS.AdjKC
