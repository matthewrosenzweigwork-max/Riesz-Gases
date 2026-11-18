import HRS.ME.ParxUConormal1
import HRS.Equilibrium.Parametrix.PX3aAuxU
import HRS.Equilibrium.Parametrix.PX2AuxE

/-!
# Packet P1a (part 2): uniform canonical projection, row data and source bound

Uniform versions (constants chosen before `β, V, ρ`, through the bundle `ParxU`) of
`HRS.Parx.canonical_conormal`, `HRS.Parx.row_data` and `HRS.Parx.hsource_conormal_aux`.
Their constants are built from the uniform row constant `conormal_row_smooth_aux_unif`.

Qualitative facts (smoothness of the row for all orders, integrability, double centering) use the
smoothness of `ρ` from the bundle and do not enter any constant.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.ParxU

open HRS.Parx

variable {d : ℕ} {s : ℝ} {N : ℕ} {νm νp c₀ Λ₀ : ℝ}

/-- **Uniform version of `canonical_conormal`.** The constant depends only on `(d, σ, b0, m, Λ₀)`. -/
theorem canonical_conormal_unif (hd : 2 ≤ d) {σ : ℝ} (hσ : σ < d) (b0 m : ℕ) (hN : m ≤ N) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ (b : ℕ → ℕ), (∀ c, b c ≤ b0) → ∀ (B : ℝ) (H : Torus d → Torus d → ℝ),
      0 ≤ B → ConormalL σ b m B H →
      ConormalL σ b m (Cc * B) (canonicalCenter (withDensityReal ρ) H) := by
  obtain ⟨Crow, hCrow0, hCrow⟩ := conormal_row_smooth_aux_unif (s := s) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) (N := N) hd hσ b0 m hN
  obtain ⟨Cs, hCs0, hCs⟩ := conormal_sigma2 (d := d) σ m
  refine ⟨1 + 2 * Cs * Crow, by positivity, fun β V ρ U b hb B H hB hH => ?_⟩
  have hρ : SmoothPosDensity ρ := U.H.rho_smooth
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  have hHc : Conormal σ b0 m B H := conormalL_mono_b hB hb hH
  have hHt : Conormal σ b0 m B (swapK H) := conormalL_mono_b hB hb (conormalL_swap hH)
  obtain ⟨hr1, hcb1⟩ := hCrow β V ρ U B H hB hHc
  obtain ⟨hr2, hcb2⟩ := hCrow β V ρ U B (swapK H) hB hHt
  set r₁ : Torus d → ℝ := fun x => ∫ y, H x y ∂(withDensityReal ρ) with hr₁
  set r₂ : Torus d → ℝ := fun y => ∫ x, swapK H y x ∂(withDensityReal ρ) with hr₂
  set c₀' : ℝ := ∫ x', r₁ x' ∂(withDensityReal ρ) with hc₀
  have hc₀b : |c₀'| ≤ Torus.cbNorm m r₁ := abs_integral_le_cbNorm _ hr1
  have hsig := hCs r₁ r₂ hr1 hr2 c₀' hc₀b
  have hsig' : ConormalL σ b m (Cs * (Torus.cbNorm m r₁ + Torus.cbNorm m r₂))
      (fun x y => -r₁ x - r₂ y + c₀') := by
    refine conormalL_mono_b ?_ (fun c => Nat.zero_le _) hsig
    have h1 : 0 ≤ Torus.cbNorm m r₁ := by
      unfold Torus.cbNorm; exact Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _
    have h2 : 0 ≤ Torus.cbNorm m r₂ := by
      unfold Torus.cbNorm; exact Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _
    positivity
  have hsum := conormalL_add hH hsig'
  have hcc : (fun x y => H x y + (-r₁ x - r₂ y + c₀')) = canonicalCenter (withDensityReal ρ) H := by
    funext x y
    unfold canonicalCenter
    simp only [hr₁, hr₂, hc₀, swapK]
    ring
  rw [hcc] at hsum
  refine conormalL_mono_B hsum ?_ ?_
  · have h1 : 0 ≤ Torus.cbNorm m r₁ := by
      unfold Torus.cbNorm; exact Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _
    have h2 : 0 ≤ Torus.cbNorm m r₂ := by
      unfold Torus.cbNorm; exact Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _
    positivity
  · have : Cs * (Torus.cbNorm m r₁ + Torus.cbNorm m r₂) ≤ Cs * (Crow * B + Crow * B) :=
      mul_le_mul_of_nonneg_left (add_le_add hcb1 hcb2) hCs0
    nlinarith

/-- **Uniform version of `row_data`.** The constant depends only on `(d, s, m, Λ₀)` and on the
kinematic constant of `HTransportConormal`; it is chosen before `β, V, ρ`. -/
theorem row_data_unif (hd : 2 ≤ d) {s : ℝ} (hsd : s < d) (hC : HTransportConormal d s)
    (m : ℕ) (hN : m ≤ N) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      Torus.IsSmooth (fun x => ∫ y, hTransport d s f x y ∂(withDensityReal ρ)) ∧
      Torus.cbNorm m (fun x => ∫ y, hTransport d s f x y ∂(withDensityReal ρ)) ≤
        Cr * posSeminorm (m + 2) f := by
  obtain ⟨C, hC0, hCm⟩ := hC m
  obtain ⟨Cr, hCr0, hCr⟩ := conormal_row_smooth_aux_unif (s := s) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) (N := N) hd hsd 0 m hN
  refine ⟨Cr * C, mul_nonneg hCr0 hC0, fun β V ρ U f hf => ⟨?_, ?_⟩⟩
  · -- smoothness of the row, for all orders: qualitative, uses only the smoothness of `ρ`
    have hρ : SmoothPosDensity ρ := U.H.rho_smooth
    unfold Torus.IsSmooth Torus.IsCk
    rw [contDiff_infty]
    intro n
    obtain ⟨C', hC'0, hC'⟩ := hC n
    obtain ⟨Cr', hCr'0, hCr'⟩ := HRS.Parx.conormal_row_smooth_aux hd hρ hsd 0 n
    exact (hCr' _ _ (mul_nonneg hC'0 (posSeminorm_nonneg _ _)) (hC' f hf)).1
  · have := (hCr β V ρ U _ _ (mul_nonneg hC0 (posSeminorm_nonneg _ _)) (hCm f hf)).2
    calc _ ≤ Cr * (C * posSeminorm (m + 2) f) := this
      _ = _ := by ring

/-- **Uniform version of `hsource_conormal_aux`.** The constant depends only on
`(d, s, m, Λ₀)`, the kinematic classes `ConormalAdd`, `ConormalSmul`, and the parameter facts
`2 ≤ d`, `0 < s < d`; it is chosen before `β, V, ρ`. -/
theorem hsource_conormal_aux_unif (hAdd : ConormalAdd d) (hSmul : ConormalSmul d)
    (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (m : ℕ) (hN : m ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (β : ℝ) (V ρ : Torus d → ℝ), ParxU d s N νm νp c₀ Λ₀ β V ρ →
      ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      Conormal s 0 m (C * posSeminorm (m + 2) f) (offZero (Hsource d s ρ f)) ∧
      IsSymmPair (Hsource d s ρ f) ∧
      HRS.PDE.DoublyCentered (withDensityReal ρ) (offZero (Hsource d s ρ f)) := by
  have hHC := hTransport_conormal hAdd hd hs0 hsd
  obtain ⟨Ch, hCh0, hCh⟩ := hHC m
  obtain ⟨Cr, hCr0, hCr⟩ := row_data_unif (s := s) (νm := νm) (νp := νp)
    (c₀ := c₀) (Λ₀ := Λ₀) (N := N) hd hsd hHC m hN
  obtain ⟨Csig, hCsig0, hCsig⟩ := conormal_sigma (d := d) s (fun _ => 0) m
  refine ⟨(1 / 2) * (Ch + Csig * Cr),
    mul_nonneg (by norm_num) (add_nonneg hCh0 (mul_nonneg hCsig0 hCr0)), fun β V ρ U f hf => ?_⟩
  have hρ : SmoothPosDensity ρ := U.H.rho_smooth
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  obtain ⟨hrsm, hcb⟩ := hCr β V ρ U f hf
  set N' : ℝ := posSeminorm (m + 2) f with hN'
  have hN0 : 0 ≤ N' := posSeminorm_nonneg _ _
  set r : Torus d → ℝ := fun x => ∫ y, hTransport d s f x y ∂(withDensityReal ρ) with hr
  have hSig := hCsig (withDensityReal ρ) r hrsm
  have hsum := hAdd s (fun _ => 0) m (Ch * N') (Csig * Torus.cbNorm m r) _ _ (hCh f hf) hSig
  have hhalf := hSmul s (fun _ => 0) m _ _ hsum (1 / 2)
  refine ⟨?_, isSymmPair_hsource hsd hf, doublyCentered_hsource hd hs0.le hsd hρ hf hrsm⟩
  have hcb0 : 0 ≤ Torus.cbNorm m r := by
    unfold Torus.cbNorm
    exact Finset.sum_nonneg fun k _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hB0 : 0 ≤ |(1 / 2 : ℝ)| * (Ch * N' + Csig * Torus.cbNorm m r) := by positivity
  have hBle : |(1 / 2 : ℝ)| * (Ch * N' + Csig * Torus.cbNorm m r) ≤ (1 / 2) * (Ch + Csig * Cr) * N' := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have : Csig * Torus.cbNorm m r ≤ Csig * (Cr * N') := mul_le_mul_of_nonneg_left hcb hCsig0
    nlinarith
  refine conormalL_congr_offDiag (F := fun x y => (1 / 2) * (hTransport d s f x y +
    (-r x - r y + ∫ x', r x' ∂(withDensityReal ρ)))) (fun x y hxy => ?_)
    (conormalL_mono_B hhalf hB0 hBle)
  simp only [offZero, if_neg hxy]
  rw [hsource_eq hsd hf x y]

end HRS.ME.ParxU

end
