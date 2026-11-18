import HRS.Equilibrium.Parametrix.PXFIDAuxP
import HRS.Equilibrium.PairPoissonFull

/-!
# Packet PX-FID, file Q: the weak form of the pair Poisson equation for any pair corrector
-/

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal

noncomputable section

namespace HRS.Parx.PXFID

variable {d : ℕ} {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ}

/-- **The distributional form** of `-(𝒜_x + 𝒜_y)ψ = H_f` for every pair corrector (no construction
needed): the integrations by parts have no flux on the diagonal. -/
theorem weak_of_corrector (H : FidHyp d s V β ρ) {f : Torus d → ℝ} {K₁ : ℝ}
    {ψ : Torus d → Torus d → ℝ} (hψ : IsPairCorrector d s V β ρ f K₁ ψ) :
    IsWeakPairPoisson d s β ρ f ψ := by
  have hd1 : 1 ≤ d := by have := H.two_le; omega
  have hs1 := H.one_le_s
  have hdens := H.rho_smooth.density
  have hprob : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hdens
  -- constants
  have hρc : Continuous ρ := Torus.continuous_of_continuous_lift
    (show ContDiff ℝ ∞ (Torus.lift ρ) from H.rho_smooth.smooth).continuous
  obtain ⟨Λ, hΛ⟩ : ∃ Λ, ∀ x, ρ x ≤ Λ := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hρc.continuousOn
    exact ⟨C, fun x => (le_abs_self _).trans (by simpa using hC x (Set.mem_univ x))⟩
  obtain ⟨M, hM⟩ := exists_force_bound H.two_le H.s_nonneg H.s_lt H.beta_pos H.V_smooth H.thermal
    H.rho_smooth
  have hK : 0 ≤ K₁ := by
    obtain ⟨x, y, hxy⟩ : ∃ x y : Torus d, x ≠ y := by
      by_contra hcon
      push Not at hcon
      have h0 : (volume : Measure (Torus d)) Set.univ ≤ (volume : Measure (Torus d)) {0} :=
        measure_mono fun z _ => hcon z 0
      rw [volume_singleton_torus hd1 0] at h0
      simp at h0
    have h1 := hψ.jpair_bound x y hxy
    have h2 := PairCorrAux.one_le_wEnv s x y
    have h3 : 0 ≤ K₁ * wEnv s x y := (abs_nonneg _).trans h1
    by_contra hneg
    push Not at hneg
    nlinarith
  set CB : ℝ := β⁻¹ * d * K₁ + M * K₁ with hCB
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hCB0 : 0 ≤ CB := by
    rw [hCB]
    have := H.beta_pos
    positivity
  have wInt := integrable_wEnv_prod H.two_le H.crit hΛ hdens
  have ae_ne := ae_ne_prod hd1 hdens
  -- pointwise bounds
  have hb1 : ∀ x y : Torus d, x ≠ y →
      ‖Bop d s V β ρ (fun z => ψ z y) x‖ ≤ CB * wEnv s x y := by
    intro x y hxy
    have := (singSlice_fst hψ.size y).abs_Bop_le H.beta_pos hM hK hs1 x (by rwa [Torus.mk_rep])
    rwa [Torus.mk_rep] at this
  have hb2 : ∀ x y : Torus d, x ≠ y →
      ‖Bop d s V β ρ (fun z => ψ x z) y‖ ≤ CB * wEnv s x y := by
    intro x y hxy
    have := (singSlice_snd hψ.size x).abs_Bop_le H.beta_pos hM hK hs1 y
      (by rw [Torus.mk_rep]; exact hxy.symm)
    rw [Torus.mk_rep, PairCorrAux.wEnv_symm] at this
    exact this
  have hg1 : ∀ x y : Torus d, x ≠ y → ‖gradFst ψ x y‖ ≤ K₁ * wEnv s x y := by
    intro x y hxy
    have := (singSlice_fst hψ.size y).norm_grad_le hK hs1 x (by rwa [Torus.mk_rep])
    rwa [Torus.mk_rep] at this
  have hg2 : ∀ x y : Torus d, x ≠ y → ‖gradSnd ψ x y‖ ≤ K₁ * wEnv s x y := by
    intro x y hxy
    have := (singSlice_snd hψ.size x).norm_grad_le hK hs1 y (by rw [Torus.mk_rep]; exact hxy.symm)
    rw [Torus.mk_rep, PairCorrAux.wEnv_symm] at this
    exact this
  -- the product measure and a.e. measurability
  set P := (withDensityReal ρ).prod (withDensityReal ρ) with hP
  have mB1 : AEMeasurable (fun p : Torus d × Torus d => Bop d s V β ρ (fun z => ψ z p.2) p.1) P :=
    aem_B1 hψ.size hd1 hdens
  have mB2 : AEMeasurable (fun p : Torus d × Torus d => Bop d s V β ρ (fun z => ψ p.1 z) p.2) P :=
    aem_B2 hψ.size hd1 hdens
  have mG1 : AEMeasurable (fun p : Torus d × Torus d => gradFst ψ p.1 p.2) P :=
    aem_gradFst hψ.size hd1 hdens
  have mG2 : AEMeasurable (fun p : Torus d × Torus d => gradSnd ψ p.1 p.2) P :=
    aem_gradSnd hψ.size hd1 hdens
  have mH : Measurable (fun p : Torus d × Torus d => Hsource d s ρ f p.1 p.2) :=
    measurable_Hsource H.s_lt ρ hdens f
  have hHeq : ∀ᵐ p ∂P, Hsource d s ρ f p.1 p.2 =
      -(Bop d s V β ρ (fun z => ψ z p.2) p.1 + Bop d s V β ρ (fun z => ψ p.1 z) p.2 +
        Jpair d s ρ ψ p.1 p.2) := by
    filter_upwards [ae_ne] with p hp
    exact eq_off_diag H hψ hK p.1 p.2 hp
  have mJ : AEMeasurable (fun p : Torus d × Torus d => Jpair d s ρ ψ p.1 p.2) P := by
    have h1 : AEMeasurable (fun p : Torus d × Torus d =>
        -(Bop d s V β ρ (fun z => ψ z p.2) p.1 + Bop d s V β ρ (fun z => ψ p.1 z) p.2) -
          Hsource d s ρ f p.1 p.2) P :=
      (mB1.add mB2).neg.sub mH.aemeasurable
    refine h1.congr ?_
    filter_upwards [hHeq] with p hp
    rw [hp]; ring
  -- integrability
  have iB1 : Integrable (fun p : Torus d × Torus d => Bop d s V β ρ (fun z => ψ z p.2) p.1) P :=
    Integrable.mono' (wInt.const_mul CB) mB1.aestronglyMeasurable (by
      filter_upwards [ae_ne] with p hp using hb1 p.1 p.2 hp)
  have iB2 : Integrable (fun p : Torus d × Torus d => Bop d s V β ρ (fun z => ψ p.1 z) p.2) P :=
    Integrable.mono' (wInt.const_mul CB) mB2.aestronglyMeasurable (by
      filter_upwards [ae_ne] with p hp using hb2 p.1 p.2 hp)
  have bJ : ∀ᵐ p ∂P, ‖Jpair d s ρ ψ p.1 p.2‖ ≤ K₁ * wEnv s p.1 p.2 := by
    filter_upwards [ae_ne] with p hp
    rw [Real.norm_eq_abs]; exact hψ.jpair_bound p.1 p.2 hp
  have iJ : Integrable (fun p : Torus d × Torus d => Jpair d s ρ ψ p.1 p.2) P :=
    Integrable.mono' (wInt.const_mul K₁) mJ.aestronglyMeasurable bJ
  have bH : ∀ᵐ p ∂P, ‖Hsource d s ρ f p.1 p.2‖ ≤ (2 * CB + K₁) * wEnv s p.1 p.2 := by
    filter_upwards [ae_ne, hHeq] with p hp hq
    rw [hq, norm_neg]
    have h1 := hb1 p.1 p.2 hp
    have h2 := hb2 p.1 p.2 hp
    have h3 := hψ.jpair_bound p.1 p.2 hp
    rw [← Real.norm_eq_abs] at h3
    calc ‖Bop d s V β ρ (fun z => ψ z p.2) p.1 + Bop d s V β ρ (fun z => ψ p.1 z) p.2 +
          Jpair d s ρ ψ p.1 p.2‖
        ≤ ‖Bop d s V β ρ (fun z => ψ z p.2) p.1 + Bop d s V β ρ (fun z => ψ p.1 z) p.2‖ +
          ‖Jpair d s ρ ψ p.1 p.2‖ := norm_add_le _ _
      _ ≤ (‖Bop d s V β ρ (fun z => ψ z p.2) p.1‖ + ‖Bop d s V β ρ (fun z => ψ p.1 z) p.2‖) +
          ‖Jpair d s ρ ψ p.1 p.2‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (2 * CB + K₁) * wEnv s p.1 p.2 := by nlinarith
  have iH : Integrable (fun p : Torus d × Torus d => Hsource d s ρ f p.1 p.2) P :=
    Integrable.mono' (wInt.const_mul (2 * CB + K₁)) mH.aestronglyMeasurable bH
  have iGrad : Integrable (fun p : Torus d × Torus d =>
      ‖gradFst ψ p.1 p.2‖ + ‖gradSnd ψ p.1 p.2‖) P := by
    refine Integrable.mono' (wInt.const_mul (2 * K₁)) (mG1.norm.add mG2.norm).aestronglyMeasurable ?_
    filter_upwards [ae_ne] with p hp
    have h1 := hg1 p.1 p.2 hp
    have h2 := hg2 p.1 p.2 hp
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    nlinarith
  refine ⟨iGrad, iJ, iH, ?_⟩
  intro φ hφ
  obtain ⟨Mφ, hMφ⟩ := exists_bounds_smooth2 hφ
  have hMφ0 : 0 ≤ Mφ := (abs_nonneg _).trans (hMφ 0 0).1
  have hφm := measurable_of_smooth2 hφ
  have gF1 := measurable_gradFst_smooth hφ
  have gF2 := measurable_gradSnd_smooth hφ
  have hgφ1 : ∀ x y, ‖gradFst φ x y‖ ≤ Mφ := fun x y =>
    (norm_gradFst_le_fderiv φ x y (differentiableAt_of_smooth hφ _)).trans (hMφ x y).2
  have hgφ2 : ∀ x y, ‖gradSnd φ x y‖ ≤ Mφ := fun x y =>
    (norm_gradSnd_le_fderiv φ x y (differentiableAt_of_smooth hφ _)).trans (hMφ x y).2
  have hw0 : ∀ p : Torus d × Torus d, 0 ≤ wEnv s p.1 p.2 := fun p =>
    zero_le_one.trans (PairCorrAux.one_le_wEnv s p.1 p.2)
  -- integrability of the products with φ
  have iB1φ : Integrable (fun p : Torus d × Torus d =>
      Bop d s V β ρ (fun z => ψ z p.2) p.1 * φ p.1 p.2) P := by
    refine Integrable.mono' (wInt.const_mul (CB * Mφ)) (mB1.mul hφm.aemeasurable).aestronglyMeasurable ?_
    filter_upwards [ae_ne] with p hp
    rw [norm_mul, Real.norm_eq_abs]
    calc ‖Bop d s V β ρ (fun z => ψ z p.2) p.1‖ * |φ p.1 p.2| ≤ (CB * wEnv s p.1 p.2) * Mφ :=
          mul_le_mul (hb1 p.1 p.2 hp) (hMφ p.1 p.2).1 (abs_nonneg _) (mul_nonneg hCB0 (hw0 p))
      _ = CB * Mφ * wEnv s p.1 p.2 := by ring
  have iB2φ : Integrable (fun p : Torus d × Torus d =>
      Bop d s V β ρ (fun z => ψ p.1 z) p.2 * φ p.1 p.2) P := by
    refine Integrable.mono' (wInt.const_mul (CB * Mφ)) (mB2.mul hφm.aemeasurable).aestronglyMeasurable ?_
    filter_upwards [ae_ne] with p hp
    rw [norm_mul, Real.norm_eq_abs]
    calc ‖Bop d s V β ρ (fun z => ψ p.1 z) p.2‖ * |φ p.1 p.2| ≤ (CB * wEnv s p.1 p.2) * Mφ :=
          mul_le_mul (hb2 p.1 p.2 hp) (hMφ p.1 p.2).1 (abs_nonneg _) (mul_nonneg hCB0 (hw0 p))
      _ = CB * Mφ * wEnv s p.1 p.2 := by ring
  have iG1 : Integrable (fun p : Torus d × Torus d =>
      inner ℝ (gradFst ψ p.1 p.2) (gradFst φ p.1 p.2)) P := by
    refine Integrable.mono' (wInt.const_mul (K₁ * Mφ)) (mG1.inner gF1.aemeasurable).aestronglyMeasurable ?_
    filter_upwards [ae_ne] with p hp
    rw [Real.norm_eq_abs]
    calc |inner ℝ (gradFst ψ p.1 p.2) (gradFst φ p.1 p.2)|
        ≤ ‖gradFst ψ p.1 p.2‖ * ‖gradFst φ p.1 p.2‖ := abs_real_inner_le_norm _ _
      _ ≤ (K₁ * wEnv s p.1 p.2) * Mφ :=
          mul_le_mul (hg1 p.1 p.2 hp) (hgφ1 p.1 p.2) (norm_nonneg _) (mul_nonneg hK (hw0 p))
      _ = K₁ * Mφ * wEnv s p.1 p.2 := by ring
  have iG2 : Integrable (fun p : Torus d × Torus d =>
      inner ℝ (gradSnd ψ p.1 p.2) (gradSnd φ p.1 p.2)) P := by
    refine Integrable.mono' (wInt.const_mul (K₁ * Mφ)) (mG2.inner gF2.aemeasurable).aestronglyMeasurable ?_
    filter_upwards [ae_ne] with p hp
    rw [Real.norm_eq_abs]
    calc |inner ℝ (gradSnd ψ p.1 p.2) (gradSnd φ p.1 p.2)|
        ≤ ‖gradSnd ψ p.1 p.2‖ * ‖gradSnd φ p.1 p.2‖ := abs_real_inner_le_norm _ _
      _ ≤ (K₁ * wEnv s p.1 p.2) * Mφ :=
          mul_le_mul (hg2 p.1 p.2 hp) (hgφ2 p.1 p.2) (norm_nonneg _) (mul_nonneg hK (hw0 p))
      _ = K₁ * Mφ * wEnv s p.1 p.2 := by ring
  have iJφ : Integrable (fun p : Torus d × Torus d => Jpair d s ρ ψ p.1 p.2 * φ p.1 p.2) P := by
    refine Integrable.mono' (wInt.const_mul (K₁ * Mφ)) (mJ.mul hφm.aemeasurable).aestronglyMeasurable ?_
    filter_upwards [ae_ne] with p hp
    rw [norm_mul, Real.norm_eq_abs]
    have h3 := hψ.jpair_bound p.1 p.2 hp
    rw [← Real.norm_eq_abs] at h3
    calc ‖Jpair d s ρ ψ p.1 p.2‖ * |φ p.1 p.2| ≤ (K₁ * wEnv s p.1 p.2) * Mφ :=
          mul_le_mul h3 (hMφ p.1 p.2).1 (abs_nonneg _) (mul_nonneg hK (hw0 p))
      _ = K₁ * Mφ * wEnv s p.1 p.2 := by ring
  -- Fubini and the slice integrations by parts
  have F1 : ∫ p : Torus d × Torus d, Bop d s V β ρ (fun z => ψ z p.2) p.1 * φ p.1 p.2 ∂P =
      -β⁻¹ * ∫ p : Torus d × Torus d, inner ℝ (gradFst ψ p.1 p.2) (gradFst φ p.1 p.2) ∂P := by
    rw [integral_prod_symm _ iB1φ, integral_prod_symm _ iG1]
    have : ∀ y : Torus d, ∫ x, Bop d s V β ρ (fun z => ψ z y) x * φ x y ∂(withDensityReal ρ) =
        -β⁻¹ * ∫ x, inner ℝ (gradFst ψ x y) (gradFst φ x y) ∂(withDensityReal ρ) := fun y =>
      (slice_ibp_fst H hK hψ.size y (isSmooth_slice_fst hφ y)).2.2
    simp_rw [this]
    rw [integral_const_mul]
  have F2 : ∫ p : Torus d × Torus d, Bop d s V β ρ (fun z => ψ p.1 z) p.2 * φ p.1 p.2 ∂P =
      -β⁻¹ * ∫ p : Torus d × Torus d, inner ℝ (gradSnd ψ p.1 p.2) (gradSnd φ p.1 p.2) ∂P := by
    rw [integral_prod _ iB2φ, integral_prod _ iG2]
    have : ∀ x : Torus d, ∫ y, Bop d s V β ρ (fun z => ψ x z) y * φ x y ∂(withDensityReal ρ) =
        -β⁻¹ * ∫ y, inner ℝ (gradSnd ψ x y) (gradSnd φ x y) ∂(withDensityReal ρ) := fun x =>
      (slice_ibp_snd H hK hψ.size x (isSmooth_slice_snd hφ x)).2.2
    simp_rw [this]
    rw [integral_const_mul]
  -- the equation
  have hRHS : ∫ p : Torus d × Torus d, Hsource d s ρ f p.1 p.2 * φ p.1 p.2 ∂P =
      -(∫ p : Torus d × Torus d, Bop d s V β ρ (fun z => ψ z p.2) p.1 * φ p.1 p.2 ∂P) -
        (∫ p : Torus d × Torus d, Bop d s V β ρ (fun z => ψ p.1 z) p.2 * φ p.1 p.2 ∂P) -
        ∫ p : Torus d × Torus d, Jpair d s ρ ψ p.1 p.2 * φ p.1 p.2 ∂P := by
    have h1 : ∀ᵐ p ∂P, Hsource d s ρ f p.1 p.2 * φ p.1 p.2 =
        -(Bop d s V β ρ (fun z => ψ z p.2) p.1 * φ p.1 p.2) -
          Bop d s V β ρ (fun z => ψ p.1 z) p.2 * φ p.1 p.2 - Jpair d s ρ ψ p.1 p.2 * φ p.1 p.2 := by
      filter_upwards [hHeq] with p hp
      rw [hp]; ring
    have j0 : Integrable (fun p : Torus d × Torus d =>
        -(Bop d s V β ρ (fun z => ψ z p.2) p.1 * φ p.1 p.2)) P := iB1φ.neg
    have j1 : Integrable (fun p : Torus d × Torus d =>
        -(Bop d s V β ρ (fun z => ψ z p.2) p.1 * φ p.1 p.2) -
          Bop d s V β ρ (fun z => ψ p.1 z) p.2 * φ p.1 p.2) P := j0.sub iB2φ
    rw [integral_congr_ae h1, integral_sub j1 iJφ, integral_sub j0 iB2φ, integral_neg]
  have hLHS : ∫ p : Torus d × Torus d, (β⁻¹ * (inner ℝ (gradFst ψ p.1 p.2) (gradFst φ p.1 p.2) +
      inner ℝ (gradSnd ψ p.1 p.2) (gradSnd φ p.1 p.2)) - Jpair d s ρ ψ p.1 p.2 * φ p.1 p.2) ∂P =
      β⁻¹ * ((∫ p : Torus d × Torus d, inner ℝ (gradFst ψ p.1 p.2) (gradFst φ p.1 p.2) ∂P) +
        ∫ p : Torus d × Torus d, inner ℝ (gradSnd ψ p.1 p.2) (gradSnd φ p.1 p.2) ∂P) -
        ∫ p : Torus d × Torus d, Jpair d s ρ ψ p.1 p.2 * φ p.1 p.2 ∂P := by
    have k2 : Integrable (fun p : Torus d × Torus d =>
        inner ℝ (gradFst ψ p.1 p.2) (gradFst φ p.1 p.2) +
          inner ℝ (gradSnd ψ p.1 p.2) (gradSnd φ p.1 p.2)) P := iG1.add iG2
    have k1 : Integrable (fun p : Torus d × Torus d =>
        β⁻¹ * (inner ℝ (gradFst ψ p.1 p.2) (gradFst φ p.1 p.2) +
          inner ℝ (gradSnd ψ p.1 p.2) (gradSnd φ p.1 p.2))) P := k2.const_mul β⁻¹
    rw [integral_sub k1 iJφ, integral_const_mul, integral_add iG1 iG2]
  rw [hLHS, hRHS, F1, F2]
  ring

end HRS.Parx.PXFID

end
