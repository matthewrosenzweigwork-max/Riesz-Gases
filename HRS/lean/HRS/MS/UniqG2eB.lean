import HRS.MS.UniqG2eA
import HRS.MS.UniqG2a
import HRS.MS.UniqG2bClose
import HRS.MS.UniqG1Meas

/-!
# G2e: Gronwall closing for the regimes `R1`, `R2a`, `R2c`

`g2e_decay`: from `g2a_master` (per-cell energy identity), the regime dispatch `g2e_nmain_bound`
(`-nMain ≤ Cd · cellEnergy`), and the abstract closing lemma `g2b_closing_gronwall`
(with `D = 0`, `S = ∅`), the mollified local energy satisfies `∫ ς_c^τ z_ε² ≤ C0 ε`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal Interval ContDiff

namespace HRS.MS.UniqG2e

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqT3
  HRS.MS.UniqE1 HRS.MS.UniqC3 HRS.MS.UniqE2 HRS.MS.UniqE3 HRS.MS.UniqE4 HRS.MS.UniqG2a
  HRS.MS.UniqNDefs

variable {d : ℕ}

theorem g2e_decay (hd : 1 ≤ d) {D : WholeDyn d} (hs0 : 0 ≤ D.s) (hsd : D.s < d) (m : ℕ)
    (hm : 1 ≤ m) (MB Λ ΛV G₀ : ℝ) {ρ : ℝ → Euc d → ℝ} {T : ℝ}
    (hMB : HRS.PDE.MatBound MB D.M) (hV : VHypRd (m + 3) ΛV G₀ D.V)
    (hcoef : CoeffHypRd D.s m Λ T ρ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    {Cb K : ℝ} {χ χh : Euc d → ℝ} {Ψ : ℝ → Euc d → Euc d}
    (hχ : IsUlocCutoff χ) (hν : 0 ≤ D.invβ)
    (hb : IsAdvectingDrift m Cb t (fun σ => meanFieldDriftW D (ρ (t - σ))))
    (hF : FlowBundle d m Cb t χ χh (fun σ => meanFieldDriftW D (ρ (t - σ))) Ψ K)
    {z : ℝ → Euc d → ℝ} (hz : IsForwardDistSolutionW D ρ t z) {B : ℝ} (hB : 0 ≤ B)
    (hzu : ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE 1 χ (z τ) ≤ ENNReal.ofReal B)
    (hχc : IsCutoffPair χ χh)
    (hΨ : HRS.Whole.IsNegDriftFlow t (fun σ => meanFieldDriftW D (ρ (t - σ))) Ψ)
    (Rg : PDE.Regime) (ν₀ : ℝ) (hR : RdRegimeHolds Rg d D.s D.M D.invβ ν₀)
    (hRne : Rg ≠ PDE.Regime.R3) :
    ∃ C0 : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ τ ∈ Set.Icc (0:ℝ) t, ∀ c : Euc d,
      ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ τ c x * moll d ε (z τ) x ^ 2) ≤
        ENNReal.ofReal (C0 * ε) := by
  have ht0 : 0 ≤ t := ht.1
  have hLM : ∀ τ ∈ Icc (0 : ℝ) t, LocMass B (z τ) := fun τ hτ =>
    locMass_of_ulocNormE hχ hB (hzu τ hτ)
  obtain ⟨C₁, C₂, hC₁, hC₂, hmaster⟩ := g2a_master hd hs0 hsd m hm MB Λ ΛV G₀ hMB hV hcoef ht hχ
    hν hb hF hz hB hzu
  obtain ⟨Cd, hCd0, hCd⟩ := g2e_nmain_bound hd D hs0 hsd ν₀ Rg hR hRne m Cb Λ T t ρ hcoef ht χ χh
    hχc _ Ψ hb hΨ K hF hB hLM
  obtain ⟨N0, hN0⟩ := e3_cellEnergy_le hF
  set Cc : ℝ := C₁ * (D.invβ + 1) + 2 * Cd with hCc
  have hCc0 : 0 ≤ Cc := by
    have : 0 ≤ C₁ * (D.invβ + 1) := mul_nonneg hC₁ (by linarith)
    linarith
  refine ⟨2 * C₂ * B ^ 2 * t * Real.exp (2 * Cc * t), fun ε hε hε1 τ hτ c0 => ?_⟩
  -- notation
  set X : ℝ → ℝ := fun σ => (cellEnergy χ Ψ σ (moll d ε (z σ))).toReal with hXdef
  set F : Euc d → ℝ → ℝ := fun c σ => ∫ x, varsigma χ Ψ σ c x * moll d ε (z σ) x ^ 2 with hFdef
  have hfin : ∀ σ ∈ Icc (0 : ℝ) t, cellEnergy χ Ψ σ (moll d ε (z σ)) ≠ ⊤ := fun σ hσ =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top)
      (hN0 ε hε hε1 B (z σ) (hLM σ hσ) σ hσ)
  have hcd : ∀ σ ∈ Icc (0 : ℝ) t, Continuous (moll d ε (z σ)) := fun σ hσ =>
    (moll_contDiff hε (hLM σ hσ).locallyIntegrable).continuous
  have hnn : ∀ σ ∈ Icc (0 : ℝ) t, ∀ c x, 0 ≤ varsigma χ Ψ σ c x * moll d ε (z σ) x ^ 2 :=
    fun σ hσ c x => mul_nonneg (hF.range σ hσ c x).1 (sq_nonneg _)
  have hmeas : ∀ σ ∈ Icc (0 : ℝ) t, ∀ c, AEStronglyMeasurable
      (fun x => varsigma χ Ψ σ c x * moll d ε (z σ) x ^ 2) volume := fun σ hσ c =>
    ((hF.contDiff σ hσ c).continuous.mul ((hcd σ hσ).pow 2)).aestronglyMeasurable
  have hFl : ∀ σ ∈ Icc (0 : ℝ) t, ∀ c, F c σ =
      (∫⁻ x, ENNReal.ofReal (varsigma χ Ψ σ c x * moll d ε (z σ) x ^ 2)).toReal := fun σ hσ c =>
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (hnn σ hσ c)) (hmeas σ hσ c)
  have hlfin : ∀ σ ∈ Icc (0 : ℝ) t, ∀ c,
      ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ σ c x * moll d ε (z σ) x ^ 2) ≠ ⊤ := fun σ hσ c =>
    ne_top_of_le_ne_top (hfin σ hσ) (e3_le_cellEnergy χ Ψ σ _ c)
  have hF0 : ∀ c, ∀ σ ∈ Icc (0 : ℝ) t, 0 ≤ F c σ := fun c σ hσ =>
    integral_nonneg (hnn σ hσ c)
  have hFX : ∀ c, ∀ σ ∈ Icc (0 : ℝ) t, F c σ ≤ X σ := fun c σ hσ => by
    rw [hFl σ hσ c]
    exact ENNReal.toReal_mono (hfin σ hσ) (e3_le_cellEnergy χ Ψ σ _ c)
  have hXB : ∀ σ ∈ Icc (0 : ℝ) t, X σ ≤ N0 * B ^ 2 := fun σ hσ => by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top N0)
      ENNReal.ofReal_ne_top) (hN0 ε hε hε1 B (z σ) (hLM σ hσ) σ hσ)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (sq_nonneg B)] at this
  have hX0 : ∀ σ ∈ Icc (0 : ℝ) t, 0 ≤ X σ := fun σ _ => ENNReal.toReal_nonneg
  have hFB : ∃ B0, ∀ c, ∀ σ ∈ Icc (0 : ℝ) t, F c σ ≤ B0 :=
    ⟨N0 * B ^ 2, fun c σ hσ => (hFX c σ hσ).trans (hXB σ hσ)⟩
  have hXeq : ∀ σ ∈ Icc (0 : ℝ) t, X σ = ⨆ c, F c σ := fun σ hσ => by
    simp only [hXdef]
    unfold cellEnergy
    rw [ENNReal.toReal_iSup (fun c => hlfin σ hσ c)]
    exact iSup_congr fun c => (hFl σ hσ c).symm
  -- per-cell master inequality
  choose I hIint hIeq hIle using fun c => hmaster ε hε hε1 c
  have hFc : ∀ c, ContinuousOn (F c) (Icc 0 t) := fun c => by
    have h1 : ContinuousOn (fun τ => ∫ σ in (0:ℝ)..τ, I c σ) (Icc 0 t) := by
      have := intervalIntegral.continuousOn_primitive_interval' (a := 0) (b₁ := 0) (b₂ := t)
        (hIint c) (Set.left_mem_uIcc)
      rwa [Set.uIcc_of_le ht0] at this
    exact h1.congr fun τ hτ => hIeq c τ hτ
  have hXm0 := HRS.MS.UniqG1.g1_iSup_measurable F t hFc hFB (inferInstance : Nonempty (Euc d))
  have hXm : AEStronglyMeasurable X (volume.restrict (Icc 0 t)) :=
    hXm0.congr (ae_restrict_of_forall_mem measurableSet_Icc fun τ hτ => (hXeq τ hτ).symm)
  have hXint : IntervalIntegrable X volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le ht0]
    refine Integrable.mono' (g := fun _ => (N0 * B ^ 2 : ℝ)) (integrable_const _) hXm ?_
    refine ae_restrict_of_forall_mem measurableSet_Icc fun σ hσ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hX0 σ hσ)]
    exact hXB σ hσ
  -- pointwise bound on the integrand
  set η : ℝ := C₂ * ε * B ^ 2 with hη
  have hη0 : 0 ≤ η := by positivity
  have hIX : ∀ c, ∀ σ ∈ Icc (0 : ℝ) t, I c σ ≤ Cc * X σ + η := fun c σ hσ => by
    have h1 := hIle c σ hσ
    have h2 := hCd ε hε hε1 σ hσ c
    have h3 : 0 ≤ D.invβ * ∫ x, varsigma χ Ψ σ c x * ‖fderiv ℝ (moll d ε (z σ)) x‖ ^ 2 :=
      mul_nonneg hν (integral_nonneg fun x => mul_nonneg (hF.range σ hσ c x).1 (by positivity))
    have h4 : Cc * X σ = C₁ * (D.invβ + 1) * X σ + 2 * (Cd * X σ) := by rw [hCc]; ring
    simp only [hXdef] at h4 h2 ⊢
    linarith
  have h1 : ∀ c, ∀ τ ∈ Icc (0 : ℝ) t, F c τ + 1 * ∫ σ in (0:ℝ)..τ, (fun (_ : Euc d) (_ : ℝ) => (0:ℝ)) c σ ≤
      Cc * (∫ σ in (0:ℝ)..τ, X σ) + η * τ + 0 * ∑ c' ∈ (fun _ => (∅ : Finset (Euc d))) c,
        ∫ σ in (0:ℝ)..τ, (fun (_ : Euc d) (_ : ℝ) => (0:ℝ)) c' σ := fun c τ hτ => by
    have hτI : Icc 0 τ ⊆ Icc 0 t := Icc_subset_Icc_right hτ.2
    have hIτ : IntervalIntegrable (I c) volume 0 τ :=
      (hIint c).mono_set (by rw [uIcc_of_le hτ.1, uIcc_of_le ht0]; exact hτI)
    have hXτ : IntervalIntegrable X volume 0 τ :=
      hXint.mono_set (by rw [uIcc_of_le hτ.1, uIcc_of_le ht0]; exact hτI)
    have hmono : ∫ σ in (0:ℝ)..τ, I c σ ≤ ∫ σ in (0:ℝ)..τ, (Cc * X σ + η) :=
      intervalIntegral.integral_mono_on hτ.1 hIτ ((hXτ.const_mul Cc).add
        intervalIntegrable_const) fun σ hσ => hIX c σ ⟨hσ.1, hσ.2.trans hτ.2⟩
    rw [intervalIntegral.integral_add (hXτ.const_mul Cc) intervalIntegrable_const,
      intervalIntegral.integral_const_mul] at hmono
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
    simp only [intervalIntegral.integral_zero, Finset.sum_empty, mul_zero, add_zero]
    have hFI : F c τ = ∫ σ in (0:ℝ)..τ, I c σ := hIeq c τ hτ
    rw [hFI]
    linarith [mul_comm η τ]
  have hclose := HRS.MS.UniqG2b.g2b_closing_gronwall t 1 Cc η 0 0 (fun _ => (∅ : Finset (Euc d)))
    F (fun _ _ => (0:ℝ)) X ht0 one_pos hCc0 hη0 le_rfl (fun c => by simp) (by simp) hF0 hFB hFc hXeq
    (fun c τ _ => le_rfl) (fun c => intervalIntegrable_const) ⟨0, fun c => by simp⟩ hXint h1
  have hXτ := hclose τ hτ
  have hexp : Real.exp (2 * Cc * τ) ≤ Real.exp (2 * Cc * t) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hτ.2 (by linarith))
  calc ∫⁻ x, ENNReal.ofReal (varsigma χ Ψ τ c0 x * moll d ε (z τ) x ^ 2)
      ≤ cellEnergy χ Ψ τ (moll d ε (z τ)) := e3_le_cellEnergy χ Ψ τ _ c0
    _ = ENNReal.ofReal (X τ) := (ENNReal.ofReal_toReal (hfin τ hτ)).symm
    _ ≤ ENNReal.ofReal (2 * C₂ * B ^ 2 * t * Real.exp (2 * Cc * t) * ε) := by
        refine ENNReal.ofReal_le_ofReal (hXτ.trans ?_)
        have h0 : 0 ≤ 2 * η * t := by positivity
        calc 2 * η * t * Real.exp (2 * Cc * τ) ≤ 2 * η * t * Real.exp (2 * Cc * t) :=
              mul_le_mul_of_nonneg_left hexp h0
          _ = _ := by rw [hη]; ring

end HRS.MS.UniqG2e
