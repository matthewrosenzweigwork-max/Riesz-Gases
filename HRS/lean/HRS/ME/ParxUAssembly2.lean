import HRS.ME.ParxUAssembly1
import HRS.ME.ParxUGlue
import HRS.ME.ParxUPx5b2
import HRS.Equilibrium.Parametrix.Glue
import HRS.Equilibrium.Parametrix.PXSAuxPsi

/-!
# Packet P7 (assembly), part (b): `pair_poisson_gen_unif`

The uniform form of `HRS.Parx.pair_poisson_gen` (Assembly.lean, lines 25-195). The four
constants are chosen before `β, V, ρ`:

* `C₁` from `parx_gap_unif` (part (a)),
* `Cinv` from `pair_inverse_small_unif` (`PairInverseSpecWith U.H (parxJ d) Cinv`),
* `CJ` from `jpair_smooth_unif`, `Ca` from `aCoef_bound_unif`,

and the final constant is `Cst = C₁ * (1 + Cinv) * (1 + CJ) + Ca`, as in `pair_poisson_gen`.
The qualitative smoothness `parx_psi_smooth_proof` is applied with `U.H` and the
`PairInverseSpec U.H (parxJ d)` obtained from `PairInverseSpecWith` by `⟨Cinv, …⟩`.

Level hypotheses: `hd, hs0, hsd, hs` (for part (a) and the glue lemmas), `px5m d (parxJ d) ≤ N`
and `px7_m d + 2 + mStar d + 3 ≤ N` (part (a) and `pair_inverse_small_unif`), `1 ≤ N`
(`jpair_smooth_unif`), and `parxK d (parxJ d) ≤ K`. The constant is nonnegative.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.ParxU

open HRS.Parx

variable {d : ℕ} {s : ℝ} {N : ℕ} {νm νp c₀ Λ₀ : ℝ}

/-- **Uniform pair-Poisson assembly** (part (b)): `pair_poisson_gen` with the constant chosen
before `β, V, ρ`. -/
theorem pair_poisson_gen_unif (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hs : s = (d : ℝ) / 2)
    (hN5 : px5m d (parxJ d) ≤ N) (hN7 : HRS.PDE.PX7.px7_m d + 2 + HRS.PDE.mStar d + 3 ≤ N)
    (hN1 : 1 ≤ N) (K : ℕ) (hK : parxK d (parxJ d) ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ) (U : ParxU d s N νm νp c₀ Λ₀ β V ρ),
      ∃ (Ψ : (Torus d → ℝ) → Torus d → Torus d → ℝ),
        (∀ (f f' : Torus d → ℝ) (a b : ℝ), Torus.IsSmooth f → Torus.IsSmooth f' →
          Ψ (a • f + b • f') = a • Ψ f + b • Ψ f') ∧
        ∀ f : Torus d → ℝ, Torus.IsSmooth f →
          IsPairCorrector d s V β ρ f (C * posSeminorm K f) (Ψ f) ∧
          (∃ M : ℝ, ∀ x, |aCoef d s ρ f x| ≤ M) ∧
          eLpNorm (aCoef d s ρ f) 2 (withDensityReal ρ) ≤ ENNReal.ofReal (C * posSeminorm K f) := by
  obtain ⟨C₁, hC₁0, hG⟩ := parx_gap_unif (N := N) (νm := νm) (νp := νp) (c₀ := c₀)
    (Λ₀ := Λ₀) hd hs0 hsd hs (parxJ d) hN5
  obtain ⟨Cinv, hCinv0, hinvU⟩ := pair_inverse_small_unif hd s hs0.le hsd N hN7 νm νp c₀ Λ₀
  obtain ⟨CJ, hCJ0, hJ⟩ := jpair_smooth_unif (d := d) (s := s) (N := N) (νm := νm)
    (νp := νp) (c₀ := c₀) (Λ₀ := Λ₀) hN1
  obtain ⟨Ca, hCa0, hCa⟩ := aCoef_bound_unif (d := d) (s := s) (N := N) (νm := νm)
    (νp := νp) (c₀ := c₀) (Λ₀ := Λ₀) hd hs0.le hsd
  have hK15 : 2 ≤ K := le_trans (by unfold parxK; omega) hK
  refine ⟨C₁ * (1 + Cinv) * (1 + CJ) + Ca, by positivity, fun β V ρ U => ?_⟩
  set H : ParxHyp d s V β ρ := U.H with hH
  have : IsProbabilityMeasure (withDensityReal ρ) :=
    PDE.MFSemigroup.isProb_withDensityReal H.rho_smooth.density
  have G := hG β V ρ U
  have hspec : PairInverseSpec H (parxJ d) := by
    unfold PairInverseSpec
    exact ⟨Cinv, hCinv0, hinvU β V ρ U⟩
  obtain ⟨hinv, hlin, hsym, -⟩ := hinvU β V ρ U
  set L := parxL d (parxJ d) with hL
  set Cst : ℝ := C₁ * (1 + Cinv) * (1 + CJ) + Ca with hCst
  refine ⟨fun f x y => parxPsi d s V β ρ f L x y +
      PDE.pairInverse H.dyn ρ (diagExt (parxR d s V β ρ f L)) x y, ?_, ?_⟩
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
    set P := posSeminorm (parxK d (parxJ d)) f with hP
    set P' := posSeminorm K f with hP'
    have hP0 : 0 ≤ P := posSeminorm_nonneg' _ _
    have hPP : P ≤ P' := posSeminorm_mono' hK f
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
    have hsmooth := parx_psi_smooth_proof H (parxJ d) hspec f hf
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
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
      obtain ⟨hcI, -⟩ := hJ β V ρ U I hI_ck hI_dc
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
      have h2 := (hJ β V ρ U I hI_ck hI_dc).2 x y
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
      obtain ⟨-, hb⟩ := hCa β V ρ U f hf
      exact ⟨Ca * posSeminorm 2 f, hb⟩
    · -- a_f in L²
      obtain ⟨hm, hb⟩ := hCa β V ρ U f hf
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

end HRS.ME.ParxU

end
