import HRS.Equilibrium.Parametrix.PXFIDTAuxC
import HRS.Equilibrium.Parametrix.PXFIDTAuxD

/-!
# Packet PX-FID-T, file E: the remainder in `C^{J+1}` and the assembly with tangential bounds

* `fidt_remainder`: `R_L = diagExt (parxR f L)`, `L = parxL d J`, is `C^{J+1}` (not only `C^J`) with
  `‖R_L‖_{C^{J+1}} ≤ C |f|_{parxK d J + 1}`: the conormal order is `σ_L = -J - 3`, so
  `σ_L + (J+1) + 1 = -1 < 0` and one more conormal derivative of the class is needed.
* `fidt_gen`: `pair_poisson_gen` (same `Ψ f = ψ^loc + Ψ_{R_L}`) with the clause of the tangential
  derivatives up to order four, given a `C^6` bound of the pair inverse on `C^{J+1}` kernels.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx.PXFIDT

variable {d : ℕ} {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ}

theorem fidt_remainder (H : ParxHyp d s V β ρ) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      PDE.IsCk2 (J + 1) (diagExt (parxR d s V β ρ f (parxL d J))) ∧
      PDE.DoublyCentered (withDensityReal ρ) (diagExt (parxR d s V β ρ f (parxL d J))) ∧
      PDE.cbNorm2 (J + 1) (diagExt (parxR d s V β ρ f (parxL d J))) ≤
        C * posSeminorm (parxK d J + 1) f ∧
      (∀ x y, diagExt (parxR d s V β ρ f (parxL d J)) x y =
        diagExt (parxR d s V β ρ f (parxL d J)) y x) := by
  have hL : 2 * parxL d J ≤ px5m d J + 1 := by unfold px5m; omega
  obtain ⟨C, hC0, hC⟩ := parxR_conormal H (px5m d J + 1) (parxL d J) hL
  have e : px5m d J + 1 - 2 * parxL d J = (J + 1) + 1 := by unfold px5m; omega
  have hσ : s - (parxL d J : ℝ) / 2 + (((J + 1 : ℕ) : ℝ) + 1) < 0 := by
    have hc : (parxL d J : ℝ) = 2 * J + d + 6 := by unfold parxL; push_cast; ring
    rw [hc, H.crit]; push_cast; linarith
  obtain ⟨Ce, hCe0, hCe⟩ := conormal_extend H.two_le (J + 1) (s - (parxL d J : ℝ) / 2) 0 hσ
  refine ⟨Ce * C, mul_nonneg hCe0 hC0, fun f hf => ?_⟩
  obtain ⟨hcl, hsym, hdc⟩ := hC f hf
  rw [e] at hcl
  have hB0 : 0 ≤ C * posSeminorm (px5m d J + 1 + 2) f := mul_nonneg hC0 (posSeminorm_nonneg' _ _)
  obtain ⟨h1, h2, h3⟩ := hCe _ _ hB0 hcl
  refine ⟨h1, px5_dc_diagExt (by have := H.two_le; omega) hdc, ?_, ?_⟩
  · have ek : parxK d J + 1 = px5m d J + 1 + 2 := by have := px5_parxK d J; omega
    rw [ek]
    calc _ ≤ Ce * (C * posSeminorm (px5m d J + 1 + 2) f) := h2
      _ = _ := by ring
  · intro x y
    by_cases hxy : x = y
    · subst hxy; rfl
    · have hyx : y ≠ x := Ne.symm hxy
      rw [h3 x y hxy, h3 y x hyx]
      exact hsym x y

theorem fidt_gen (H : ParxHyp d s V β ρ) (J : ℕ) (hspec : PairInverseSpec H J)
    (h6 : ∃ C6 : ℝ, 0 ≤ C6 ∧ ∀ R : Torus d → Torus d → ℝ, PDE.IsCk2 (J + 1) R →
      PDE.IsCk2 6 (PDE.pairInverse H.dyn ρ R) ∧
      PDE.cbNorm2 6 (PDE.pairInverse H.dyn ρ R) ≤ C6 * PDE.cbNorm2 (J + 1) R)
    (hJ : 3 ≤ J) (K : ℕ) (hK : parxK d J + 1 ≤ K) :
    ∃ (Ψ : (Torus d → ℝ) → Torus d → Torus d → ℝ) (C : ℝ),
      (∀ (f f' : Torus d → ℝ) (a b : ℝ), Torus.IsSmooth f → Torus.IsSmooth f' →
        Ψ (a • f + b • f') = a • Ψ f + b • Ψ f') ∧
      ∀ f : Torus d → ℝ, Torus.IsSmooth f →
        IsPairCorrector d s V β ρ f (C * posSeminorm K f) (Ψ f) ∧
        (∃ M : ℝ, ∀ x, |aCoef d s ρ f x| ≤ M) ∧
        eLpNorm (aCoef d s ρ f) 2 (withDensityReal ρ) ≤ ENNReal.ofReal (C * posSeminorm K f) ∧
        (∀ es : List (Euc d), es.length ≤ 4 →
          PsiSize s (C * posSeminorm K f * (es.map fun e => ‖e‖).prod)
            (tanIter es (Ψ f))) := by
  obtain ⟨C₁, G⟩ := parx_gap_proof H J
  have hspec' := hspec
  obtain ⟨Cinv, hCinv0, hinv, hlin, hsym, -⟩ := hspec
  obtain ⟨CJ, hCJ0, hCJ⟩ := jpair_smooth H
  obtain ⟨Ca, hCa0, hCa⟩ := aCoef_bound H
  have : IsProbabilityMeasure (withDensityReal ρ) :=
    PDE.MFSemigroup.isProb_withDensityReal H.rho_smooth.density
  have hC₁ : 0 ≤ C₁ := G.C_nonneg
  obtain ⟨C6, hC6, h6'⟩ := h6
  obtain ⟨Cr, hCr0, hCr⟩ := fidt_remainder H J
  obtain ⟨Cn, hCn0, hCn⟩ := fidt_psi_bnds H (px5m d J) (parxL d J) (by unfold px5m; omega)
  set L := parxL d J with hL
  have hCx0 : 0 ≤ Cn + 3 * C6 * Cr := by positivity
  set Cst : ℝ := C₁ * (1 + Cinv) * (1 + CJ) + Ca + (Cn + 3 * C6 * Cr) with hCst
  have hK0 : parxK d J ≤ K := by omega
  have hK15 : 2 ≤ K := by unfold parxK at hK; omega
  refine ⟨fun f x y => parxPsi d s V β ρ f L x y +
      PDE.pairInverse H.dyn ρ (diagExt (parxR d s V β ρ f L)) x y, Cst, ?_, ?_⟩
  · -- linearity
    intro f f' a b hf hf'
    funext x y
    have h1 := congrFun (congrFun (G.linear_psi f f' a b hf hf') x) y
    have h2 : PDE.pairInverse H.dyn ρ (diagExt (parxR d s V β ρ (a • f + b • f') L)) =
        fun x y => a * PDE.pairInverse H.dyn ρ (diagExt (parxR d s V β ρ f L)) x y +
          b * PDE.pairInverse H.dyn ρ (diagExt (parxR d s V β ρ f' L)) x y := by
      rw [G.linear_R f f' a b hf hf']
      exact hlin _ _ a b (G.remainder_ck f hf).1 (G.remainder_ck f' hf').1
    have h3 := congrFun (congrFun h2 x) y
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [h1, h3]
    ring
  · intro f hf
    obtain ⟨hck, hdc, hnorm, hRsym⟩ := G.remainder_ck f hf
    set Rf := diagExt (parxR d s V β ρ f L) with hRf
    set I := PDE.pairInverse H.dyn ρ Rf with hI
    obtain ⟨hI_ck, hI_dc, hI_norm, hI_eq⟩ := hinv Rf hck hdc
    set P := posSeminorm (parxK d J) f with hP
    set P' := posSeminorm K f with hP'
    have hP0 : 0 ≤ P := posSeminorm_nonneg' _ _
    have hPP : P ≤ P' := posSeminorm_mono' hK0 f
    have hI_bd : PDE.cbNorm2 2 I ≤ Cinv * (C₁ * P) :=
      hI_norm.trans (mul_le_mul_of_nonneg_left hnorm hCinv0)
    have hIcont : Continuous fun p : Torus d × Torus d => I p.1 p.2 :=
      PDE.MFPair.continuous_pair_of_continuous_lift2 hI_ck.continuous
    have hIslice : ∀ x, Continuous fun y => I x y := fun x =>
      hIcont.comp (continuous_const.prodMk continuous_id)
    have hCst1 : C₁ * (1 + Cinv) ≤ Cst := by
      have : 0 ≤ C₁ * (1 + Cinv) * CJ := by positivity
      nlinarith
    have hCst2 : C₁ + CJ * (Cinv * C₁) ≤ Cst := by
      have : 0 ≤ C₁ * Cinv * (1 + CJ) := by positivity
      nlinarith
    have hP'0 : 0 ≤ P' := posSeminorm_nonneg' _ _
    have hCst0 : 0 ≤ Cst := by rw [hCst]; positivity
    have hsmooth := parx_psi_smooth_proof H J hspec' f hf
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · -- measurable
      exact (G.measurable f hf).add hIcont.measurable
    · -- symmetric
      intro x y
      have h2 : I x y = I y x := hsym Rf hck hRsym x y
      exact congrArg₂ (· + ·) (G.symm f hf x y) h2
    · -- canonical
      intro x
      obtain ⟨hi, h0⟩ := G.canonical f hf x
      have hi2 : Integrable (fun y => I x y) (withDensityReal ρ) :=
        (hIslice x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have h02 : ∫ y, I x y ∂(withDensityReal ρ) = 0 := hI_dc.2 x
      exact ⟨hi.add hi2, by rw [integral_add hi hi2, h0, h02]; ring⟩
    · -- size
      have hs1 : PsiSize s (C₁ * P) (parxPsi d s V β ρ f L) := G.size f hf
      have hs2 := PsiSize.add_ck2 hs1 hI_ck hI_bd hsmooth
      refine PsiSize.mono hs2 ?_
      have : C₁ * P + Cinv * (C₁ * P) ≤ Cst * P' := by
        have h1 : C₁ * P + Cinv * (C₁ * P) = C₁ * (1 + Cinv) * P := by ring
        rw [h1]
        calc C₁ * (1 + Cinv) * P ≤ Cst * P := mul_le_mul_of_nonneg_right hCst1 hP0
          _ ≤ Cst * P' := mul_le_mul_of_nonneg_left hPP hCst0
      exact this
    · -- Poisson equation
      intro x y hxy
      obtain ⟨hA1, hA2, -⟩ := G.add_smooth f hf I hI_ck x y hxy
      have htel := G.telescope f hf x y hxy
      have hRxy : Rf x y = parxR d s V β ρ f L x y := by simp [hRf, diagExt, hxy]
      have hg1 : genFst d s V β ρ I x y = PDE.centeredGen H.dyn ρ (fun x' => I x' y) x := by
        have := congrFun (projGen_eq_centeredGen H (fun z => I z y)
          (by simpa using PDE.MFPair.isCk_slice 2 I hI_ck y)) x
        exact this
      have hg2 : genSnd d s V β ρ I x y = PDE.centeredGen H.dyn ρ (fun y' => I x y') y := by
        have := congrFun (projGen_eq_centeredGen H (fun z => I x z)
          (by simpa using PDE.MFPair.isCk_slice2 2 I hI_ck x)) y
        exact this
      have heq := hI_eq x y
      show -(genFst d s V β ρ (fun x y => parxPsi d s V β ρ f L x y + I x y) x y +
        genSnd d s V β ρ (fun x y => parxPsi d s V β ρ f L x y + I x y) x y) = Hsource d s ρ f x y
      rw [hA1, hA2, hg1, hg2]
      linarith
    · -- 𝒥ψ canonical
      intro x
      obtain ⟨hi, h0⟩ := G.jpair_canonical f hf x
      obtain ⟨hcI, -⟩ := hCJ I hI_ck hI_dc
      obtain ⟨hiI, h0I⟩ := hcI x
      have hae : ∀ᵐ y ∂(withDensityReal ρ),
          Jpair d s ρ (fun x y => parxPsi d s V β ρ f L x y + I x y) x y =
            Jpair d s ρ (parxPsi d s V β ρ f L) x y + Jpair d s ρ I x y := by
        have hne : ∀ᵐ y : Torus d, y ≠ x := by
          have := PDE.MFSchauder.ae_add_ne_zero (d := d) (by have := H.two_le; omega) (-x)
          filter_upwards [this] with y hy
          intro hyx; apply hy; rw [hyx]; simp
        have hne' := (withDensity_absolutelyContinuous (volume : Measure (Torus d))
          (fun x => ENNReal.ofReal (ρ x))).ae_le hne
        filter_upwards [hne'] with y hy
        exact (G.add_smooth f hf I hI_ck x y (Ne.symm hy)).2.2
      refine ⟨(integrable_congr hae).mpr (hi.add hiI), ?_⟩
      rw [integral_congr_ae hae, integral_add hi hiI, h0, h0I]; ring
    · -- 𝒥ψ bound
      intro x y hxy
      have h1 := G.jpair_bound f hf x y hxy
      have h2 := (hCJ I hI_ck hI_dc).2 x y
      have hw : 1 ≤ wEnv s x y := PairCorrAux.one_le_wEnv s x y
      have h3 : Jpair d s ρ (fun x y => parxPsi d s V β ρ f L x y + I x y) x y =
          Jpair d s ρ (parxPsi d s V β ρ f L) x y + Jpair d s ρ I x y :=
        (G.add_smooth f hf I hI_ck x y hxy).2.2
      rw [h3]
      have h4 : |Jpair d s ρ I x y| ≤ CJ * (Cinv * (C₁ * P)) :=
        h2.trans (mul_le_mul_of_nonneg_left hI_bd hCJ0)
      have h5 : 0 ≤ P := hP0
      calc |Jpair d s ρ (parxPsi d s V β ρ f L) x y + Jpair d s ρ I x y|
          ≤ |Jpair d s ρ (parxPsi d s V β ρ f L) x y| + |Jpair d s ρ I x y| := abs_add_le _ _
        _ ≤ C₁ * P * wEnv s x y + CJ * (Cinv * (C₁ * P)) * wEnv s x y :=
            add_le_add h1 (h4.trans (le_mul_of_one_le_right (by positivity) hw))
        _ = (C₁ + CJ * (Cinv * C₁)) * P * wEnv s x y := by ring
        _ ≤ Cst * P' * wEnv s x y := by
            have hw0 : 0 ≤ wEnv s x y := by linarith
            have hc0 : 0 ≤ C₁ + CJ * (Cinv * C₁) := by positivity
            have : (C₁ + CJ * (Cinv * C₁)) * P ≤ Cst * P' :=
              mul_le_mul hCst2 hPP hP0 (hc0.trans hCst2)
            exact mul_le_mul_of_nonneg_right this hw0
    · -- a_f bounded
      obtain ⟨-, hb⟩ := hCa f hf
      exact ⟨Ca * posSeminorm 2 f, hb⟩
    · -- a_f in L²
      obtain ⟨hm, hb⟩ := hCa f hf
      have hP2 : posSeminorm 2 f ≤ P' := posSeminorm_mono' hK15 f
      have hae : ∀ᵐ x ∂(withDensityReal ρ), ‖aCoef d s ρ f x‖ ≤ Cst * P' :=
        Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]
          calc |aCoef d s ρ f x| ≤ Ca * posSeminorm 2 f := hb x
            _ ≤ Ca * P' := mul_le_mul_of_nonneg_left hP2 hCa0
            _ ≤ Cst * P' := by
                refine mul_le_mul_of_nonneg_right ?_ hP'0
                have : 0 ≤ C₁ * (1 + Cinv) * (1 + CJ) := by positivity
                linarith
      calc eLpNorm (aCoef d s ρ f) 2 (withDensityReal ρ)
          ≤ (withDensityReal ρ) Set.univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal (Cst * P') :=
            eLpNorm_le_of_ae_bound hm hae
        _ = ENNReal.ofReal (Cst * P') := by simp
    · -- tangential derivatives up to order four
      intro es hes
      have hLm : 2 * parxL d J + es.length ≤ px5m d J := by unfold px5m; omega
      have hΦ : PsiSize s (Cn * posSeminorm (px5m d J + 2) f * (es.map fun e => ‖e‖).prod)
          (tanIter es (parxPsi d s V β ρ f L)) :=
        (hCn es hLm f hf).psiSize (by
          rw [lift2_tanIter]
          exact contDiffOn_top_tanL isOpen_offDiag es (parxPsi_smooth_offDiag H f hf L))
      obtain ⟨hck1, -, hnorm1, -⟩ := hCr f hf
      obtain ⟨hI6c, hI6n⟩ := h6' Rf hck1
      have hIes : PDE.IsCk2 (2 + es.length) I := pxS_isCk2_mono (by omega) hI6c
      have hpr : 0 ≤ (es.map fun e => ‖e‖).prod :=
        List.prod_nonneg (by intro x hx; obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx; exact norm_nonneg _)
      have hP1 : 0 ≤ posSeminorm (parxK d J + 1) f := posSeminorm_nonneg' _ _
      have hM : 3 * (es.map fun e => ‖e‖).prod * PDE.cbNorm2 (2 + es.length) I ≤
          3 * (es.map fun e => ‖e‖).prod * (C6 * (Cr * posSeminorm (parxK d J + 1) f)) := by
        have h1 : PDE.cbNorm2 (2 + es.length) I ≤ PDE.cbNorm2 6 I :=
          PDE.PX7.px7_cbNorm2_mono (by omega) I
        have h2 : PDE.cbNorm2 6 I ≤ C6 * (Cr * posSeminorm (parxK d J + 1) f) :=
          hI6n.trans (mul_le_mul_of_nonneg_left hnorm1 hC6)
        exact mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
      have hfin := fidt_psiSize_tan es hΦ (parxPsi_smooth_offDiag H f hf L) hIes hM hsmooth
      refine PsiSize.mono hfin ?_
      have hPm : posSeminorm (px5m d J + 2) f ≤ P' := by
        have := posSeminorm_mono' hK0 f
        rw [px5_parxK] at this; exact this
      have hPp : posSeminorm (parxK d J + 1) f ≤ P' := posSeminorm_mono' hK f
      have hCstx : Cn + 3 * C6 * Cr ≤ Cst := by
        have : 0 ≤ C₁ * (1 + Cinv) * (1 + CJ) := by positivity
        rw [hCst]; linarith
      calc Cn * posSeminorm (px5m d J + 2) f * (es.map fun e => ‖e‖).prod +
            3 * (es.map fun e => ‖e‖).prod * (C6 * (Cr * posSeminorm (parxK d J + 1) f))
          ≤ Cn * P' * (es.map fun e => ‖e‖).prod +
            3 * (es.map fun e => ‖e‖).prod * (C6 * (Cr * P')) := by gcongr
        _ = (Cn + 3 * C6 * Cr) * P' * (es.map fun e => ‖e‖).prod := by ring
        _ ≤ Cst * P' * (es.map fun e => ‖e‖).prod := by gcongr


end HRS.Parx.PXFIDT

end
