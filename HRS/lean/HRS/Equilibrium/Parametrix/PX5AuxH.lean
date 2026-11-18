import HRS.Equilibrium.Parametrix.PX5AuxG

/-!
# Prop 4.13 parametrix, packet PX5: canonicity of `𝒥ψ^loc`

`∫_y (P_xJ_xψ)(x,y) μ(dy) = 0` follows from `gen_integral_comm` applied to `ψ` for the hypotheses
`ParxHyp d s V β ρ` and `ParxHyp d s V' (β/2) ρ` (whose local generators differ by the factor `2`);
the combination `2 genFst - genFst'` isolates the nonlocal part, whose rows are integrable by
`jop_general`.
-/

open MeasureTheory Filter Topology
noncomputable section

namespace HRS.Parx

open HRS.PDE HRS.PDE.MFAux

variable {d : ℕ} {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ}

theorem px5_genFst_unfold (V : Torus d → ℝ) (β : ℝ) (ψ : Torus d → Torus d → ℝ) (x y : Torus d) :
    genFst d s V β ρ ψ x y =
      (Bop d s V β ρ (fun z => ψ z y) x + Jop d s ρ (fun z => ψ z y) x) -
        ∫ x', (Bop d s V β ρ (fun z => ψ z y) x' + Jop d s ρ (fun z => ψ z y) x') ∂(withDensityReal ρ) :=
  rfl

/-- the key identity (★): rows of `P_x J_x ψ` have zero mean. -/
theorem px5_star (H : ParxHyp d s V β ρ) (J : ℕ) (f : Torus d → ℝ) (hf : Torus.IsSmooth f)
    (x : Torus d) :
    ∫ y, (px5K d s ρ (parxPsi d s V β ρ f (parxL d J)) x y -
      ∫ z, px5K d s ρ (parxPsi d s V β ρ f (parxL d J)) z y ∂(withDensityReal ρ))
      ∂(withDensityReal ρ) = 0 := by
  have hd : 0 < d := by have := H.two_le; omega
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal H.rho_smooth.density
  set ψ := parxPsi d s V β ρ f (parxL d J) with hψ
  obtain ⟨V', H', hB⟩ := px5_scaled_hyp H
  obtain ⟨Cp, hCp0, hCp⟩ := px5_psi_class H J
  obtain ⟨Cn, hCn0, hCn⟩ := px5_psi_bnds H (px5m d J) (parxL d J) (by unfold px5m; omega)
  obtain ⟨CK, hCK0, hCK⟩ := px5_K_class H J
  obtain ⟨Kr, hKr0, hKr⟩ := px5_K_rowcol H
  have hclass := hCp f hf
  have hbnds := hCn f hf
  have hB0 : 0 ≤ CK * posSeminorm (px5m d J + 2) f := mul_nonneg hCK0 (posSeminorm_nonneg' _ _)
  have hKcl : Conormal 0 3 0 (CK * posSeminorm (px5m d J + 2) f) (px5K d s ρ ψ) :=
    ConormalL.mono (hCK f hf) hB0 le_rfl (fun c => le_rfl) (Nat.zero_le _) le_rfl
  obtain ⟨-, hcol⟩ := hKr hB0 hKcl (px5K_diag ψ)
  have hcanon := px5_canonical H J f hf
  have hg1 := (gen_integral_comm H (px5_crit_lt H) (b := 1) (m := J + 3) (by omega) hclass hcanon x)
  have hg2 := (gen_integral_comm H' (px5_crit_lt H') (b := 1) (m := J + 3) (by omega) hclass hcanon x)
  -- integrability of `u y` and `v y` in the first variable
  have hu : ∀ y, Integrable (fun x' => Bop d s V β ρ (fun z => ψ z y) x') (withDensityReal ρ) :=
    fun y => px5_Bop_integrable H hbnds y
  have hv : ∀ y, Integrable (fun x' => Jop d s ρ (fun z => ψ z y) x') (withDensityReal ρ) := by
    intro y
    refine ((hcol y).1).congr ?_
    filter_upwards [px5_ae_ne hd ρ y] with z hz
    simp [px5K, offZero, hz]
  -- the pointwise identity `2 E₁ - E₂ = v_y(x) - ∫ v_y`
  have hcomb : ∀ y, 2 * genFst d s V β ρ ψ x y - genFst d s V' (β / 2) ρ ψ x y =
      Jop d s ρ (fun z => ψ z y) x - ∫ x', Jop d s ρ (fun z => ψ z y) x' ∂(withDensityReal ρ) := by
    intro y
    rw [px5_genFst_unfold, px5_genFst_unfold]
    simp only [hB]
    rw [integral_add (hu y) (hv y), integral_add ((hu y).const_mul 2) (hv y), integral_const_mul]
    ring_nf
  have hint0 : ∫ y, (2 * genFst d s V β ρ ψ x y - genFst d s V' (β / 2) ρ ψ x y)
      ∂(withDensityReal ρ) = 0 := by
    rw [integral_sub (hg1.1.const_mul 2) hg2.1, integral_const_mul, hg1.2.1, hg2.2.1]
    ring
  simp_rw [hcomb] at hint0
  rw [← hint0]
  refine integral_congr_ae ?_
  filter_upwards [px5_ae_ne hd ρ x] with y hy
  have h1 : Jop d s ρ (fun z => ψ z y) x = px5K d s ρ ψ x y := by
    simp [px5K, offZero, Ne.symm hy]
  have h2 : ∫ x', Jop d s ρ (fun z => ψ z y) x' ∂(withDensityReal ρ) =
      ∫ z, px5K d s ρ ψ z y ∂(withDensityReal ρ) := by
    refine integral_congr_ae ?_
    filter_upwards [px5_ae_ne hd ρ y] with z hz
    simp [px5K, offZero, hz]
  rw [h1, h2]

theorem px5_jpair_canonical (H : ParxHyp d s V β ρ) (J : ℕ) (f : Torus d → ℝ)
    (hf : Torus.IsSmooth f) :
    IsCanonicalPair (withDensityReal ρ) (Jpair d s ρ (parxPsi d s V β ρ f (parxL d J))) := by
  have hd : 0 < d := by have := H.two_le; omega
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal H.rho_smooth.density
  set ψ := parxPsi d s V β ρ f (parxL d J) with hψ
  obtain ⟨CK, hCK0, hCK⟩ := px5_K_class H J
  obtain ⟨Kr, hKr0, hKr⟩ := px5_K_rowcol H
  have hB0 : 0 ≤ CK * posSeminorm (px5m d J + 2) f := mul_nonneg hCK0 (posSeminorm_nonneg' _ _)
  have hKcl : Conormal 0 3 0 (CK * posSeminorm (px5m d J + 2) f) (px5K d s ρ ψ) :=
    ConormalL.mono (hCK f hf) hB0 le_rfl (fun c => le_rfl) (Nat.zero_le _) le_rfl
  obtain ⟨hrow, hcol⟩ := hKr hB0 hKcl (px5K_diag ψ)
  have hprod := conormal_prod_int H.two_le H.rho_smooth (σ := (0 : ℝ))
    (by have : (2 : ℝ) ≤ d := by exact_mod_cast H.two_le
        linarith) 3 hB0 hKcl (px5K_diag ψ)
  have hm1 : Integrable (fun y => ∫ z, px5K d s ρ ψ z y ∂(withDensityReal ρ)) (withDensityReal ρ) :=
    hprod.integral_prod_right
  have hsym := px5_symm H J f hf
  intro x
  set m2 : ℝ := ∫ z, px5K d s ρ ψ z x ∂(withDensityReal ρ) with hm2
  have hform : (fun y => Jpair d s ρ ψ x y) =ᵐ[withDensityReal ρ] fun y =>
      (px5K d s ρ ψ x y - ∫ z, px5K d s ρ ψ z y ∂(withDensityReal ρ)) + (px5K d s ρ ψ y x - m2) := by
    filter_upwards [px5_ae_ne hd ρ x] with y hy
    exact px5_jpair_formula hd ψ hsym x y (Ne.symm hy)
  have i1 : Integrable (fun y => px5K d s ρ ψ x y - ∫ z, px5K d s ρ ψ z y ∂(withDensityReal ρ))
      (withDensityReal ρ) := (hrow x).1.sub hm1
  have i2 : Integrable (fun y => px5K d s ρ ψ y x - m2) (withDensityReal ρ) :=
    (hcol x).1.sub (integrable_const _)
  refine ⟨(i1.add i2).congr hform.symm, ?_⟩
  rw [integral_congr_ae hform, integral_add i1 i2, px5_star H J f hf x, integral_sub (hcol x).1
    (integrable_const _), ← hm2]
  simp

end HRS.Parx

end
