import HRS.MS.SA12X3C15A
import HRS.MS.UniqG1Gronwall

/-!
# S.A.12 (SA12X4) W1: the weighted integral cell Gronwall bound

Per-cell integral inequality (from the cell energy derivative), summed with summable weights `w i`, absorption of the
neighbouring dissipation, and Gronwall for the weighted sum.  All sums are in `ℝ≥0∞`; the rate term `r i` of a cell is only an
`ℝ≥0∞`-valued bound (no measurability in time is asked of it): it enters through the superadditivity
`∑ w i ∫⁻ r i ≤ ∫⁻ ∑ w i r i` and the pointwise weighted domination `hr`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X4

/-- Superadditivity of the lower integral for a weighted countable sum (no measurability needed). -/
theorem sa12x4_tsum_lintegral_le {ι α : Type*} [MeasurableSpace α] {μ : Measure α} (w : ι → ℝ≥0∞)
    (hw : ∀ i, w i ≠ ⊤) (r : ι → α → ℝ≥0∞) :
    ∑' i, w i * ∫⁻ x, r i x ∂μ ≤ ∫⁻ x, ∑' i, w i * r i x ∂μ := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  have hfin : ∀ s : Finset ι, ∑ i ∈ s, w i * ∫⁻ x, r i x ∂μ ≤ ∫⁻ x, ∑ i ∈ s, w i * r i x ∂μ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      have hrw : ∫⁻ x, ∑ i ∈ insert a s, w i * r i x ∂μ =
          ∫⁻ x, (w a * r a x + ∑ i ∈ s, w i * r i x) ∂μ :=
        lintegral_congr fun x => Finset.sum_insert ha
      rw [Finset.sum_insert ha, hrw, ← lintegral_const_mul' _ _ (hw a)]
      calc ∫⁻ x, w a * r a x ∂μ + ∑ i ∈ s, w i * ∫⁻ x, r i x ∂μ
          ≤ ∫⁻ x, w a * r a x ∂μ + ∫⁻ x, ∑ i ∈ s, w i * r i x ∂μ := by gcongr
        _ ≤ ∫⁻ x, (w a * r a x + ∑ i ∈ s, w i * r i x) ∂μ := le_lintegral_add _ _
  refine (hfin s).trans (lintegral_mono fun x => ENNReal.sum_le_tsum s)

theorem sa12x4_weighted_gronwall {ι : Type*} [Countable ι] (t ν κ a : ℝ) (ht : 0 ≤ t) (hν : 0 ≤ ν)
    (hκ : 0 ≤ κ) (hκν : κ ≤ ν) (ha : 0 ≤ a) (w : ι → ℝ≥0∞) (hwfin : ∑' i, w i < ⊤)
    (f g D : ι → ℝ → ℝ) (r : ι → ℝ → ℝ≥0∞)
    (hnn : ∀ i, ∀ τ ∈ Icc (0 : ℝ) t, 0 ≤ f i τ) (hDnn : ∀ i, ∀ τ ∈ Icc (0 : ℝ) t, 0 ≤ D i τ)
    (hbdd : ∃ B : ℝ, ∀ i, ∀ τ ∈ Icc (0 : ℝ) t, f i τ ≤ B)
    (hDint : ∀ i, IntegrableOn (D i) (Icc (0 : ℝ) t))
    (hDbdd : ∃ B : ℝ, ∀ i, ∫ σ in Icc (0 : ℝ) t, D i σ ≤ B)
    (hcont : ∀ i, ContinuousOn (f i) (Icc (0 : ℝ) t))
    (hderiv : ∀ i, ∀ τ ∈ Icc (0 : ℝ) t, HasDerivWithinAt (f i) (g i τ) (Icc (0 : ℝ) t) τ)
    (hgint : ∀ i, IntegrableOn (g i) (Icc (0 : ℝ) t))
    (hineq : ∀ i, ∀ τ ∈ Icc (0 : ℝ) t, ENNReal.ofReal (g i τ + ν * D i τ) ≤ r i τ)
    (hr : ∀ τ ∈ Icc (0 : ℝ) t, ∑' i, w i * r i τ ≤
      ENNReal.ofReal κ * ∑' i, w i * ENNReal.ofReal (D i τ) +
        ENNReal.ofReal a * ∑' i, w i * ENNReal.ofReal (f i τ)) :
    ∀ τ ∈ Icc (0 : ℝ) t, ∑' i, w i * ENNReal.ofReal (f i τ) ≤
      ENNReal.ofReal (Real.exp (a * τ)) * ∑' i, w i * ENNReal.ofReal (f i 0) := by
  classical
  obtain ⟨Bf, hBf⟩ := hbdd
  obtain ⟨BD, hBD⟩ := hDbdd
  have hw : ∀ i, w i ≠ ⊤ := fun i => ne_top_of_le_ne_top hwfin.ne (ENNReal.le_tsum i)
  set W : ℝ → ℝ≥0∞ := fun τ => ∑' i, w i * ENNReal.ofReal (f i τ) with hW
  set S : ℝ≥0∞ := ∑' i, w i with hS
  have hSt : S ≠ ⊤ := hwfin.ne
  have hWle : ∀ τ ∈ Icc (0 : ℝ) t, W τ ≤ S * ENNReal.ofReal Bf := by
    intro τ hτ
    calc W τ ≤ ∑' i, w i * ENNReal.ofReal Bf := ENNReal.tsum_le_tsum fun i => by
          gcongr; exact hBf i τ hτ
      _ = S * ENNReal.ofReal Bf := by rw [ENNReal.tsum_mul_right]
  have hWfin : ∀ τ ∈ Icc (0 : ℝ) t, W τ ≠ ⊤ := fun τ hτ =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hSt ENNReal.ofReal_ne_top) (hWle τ hτ)
  have hWmeas : AEMeasurable W (volume.restrict (Icc (0 : ℝ) t)) :=
    AEMeasurable.ennreal_tsum fun i => (((hcont i).aemeasurable measurableSet_Icc).ennreal_ofReal).const_mul _
  -- the dissipation integrals
  set X : ℝ → ℝ≥0∞ := fun τ => ∑' i, w i * ∫⁻ σ in Icc (0 : ℝ) τ, ENNReal.ofReal (D i σ) with hX
  have hsubt : ∀ τ ∈ Icc (0 : ℝ) t, Icc (0 : ℝ) τ ⊆ Icc (0 : ℝ) t := fun τ hτ => Icc_subset_Icc_right hτ.2
  have hXle : ∀ τ ∈ Icc (0 : ℝ) t, X τ ≤ S * ENNReal.ofReal BD := by
    intro τ hτ
    calc X τ ≤ ∑' i, w i * ENNReal.ofReal BD := ENNReal.tsum_le_tsum fun i => by
          gcongr
          have h1 : ∫⁻ σ in Icc (0 : ℝ) τ, ENNReal.ofReal (D i σ) ≤
              ∫⁻ σ in Icc (0 : ℝ) t, ENNReal.ofReal (D i σ) :=
            lintegral_mono_set (hsubt τ hτ)
          refine h1.trans ?_
          rw [← ofReal_integral_eq_lintegral_ofReal (hDint i)
            ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => hDnn i σ hσ))]
          exact ENNReal.ofReal_le_ofReal (hBD i)
      _ = S * ENNReal.ofReal BD := by rw [ENNReal.tsum_mul_right]
  have hXfin : ∀ τ ∈ Icc (0 : ℝ) t, X τ ≠ ⊤ := fun τ hτ =>
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hSt ENNReal.ofReal_ne_top) (hXle τ hτ)
  -- the key inequality for the weighted sum
  have hkey : ∀ τ ∈ Icc (0 : ℝ) t, W τ ≤ W 0 + ENNReal.ofReal a * ∫⁻ σ in Icc (0 : ℝ) τ, W σ := by
    intro τ hτ
    have hsub := hsubt τ hτ
    have h0t : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_rfl, ht⟩
    -- per cell
    have hcell : ∀ i, ENNReal.ofReal (f i τ) + ENNReal.ofReal ν * ∫⁻ σ in Icc (0 : ℝ) τ, ENNReal.ofReal (D i σ) ≤
        ENNReal.ofReal (f i 0) + ∫⁻ σ in Icc (0 : ℝ) τ, r i σ := by
      intro i
      have hDi : IntegrableOn (D i) (Icc (0 : ℝ) τ) := (hDint i).mono_set hsub
      have hgi : IntegrableOn (g i) (Icc (0 : ℝ) τ) := (hgint i).mono_set hsub
      have hftc := HRS.MH.AdjointRd.Phase2SA12Construction.sa12x3_ftc_int t (f i) (g i) (hcont i) (hderiv i) (hgint i) τ hτ
      have hDnn' : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) τ)] D i :=
        (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => hDnn i σ (hsub hσ))
      have hDl : ENNReal.ofReal (∫ σ in Icc (0 : ℝ) τ, D i σ) = ∫⁻ σ in Icc (0 : ℝ) τ, ENNReal.ofReal (D i σ) :=
        ofReal_integral_eq_lintegral_ofReal hDi hDnn'
      set h : ℝ → ℝ := fun σ => g i σ + ν * D i σ with hh
      have hhi : IntegrableOn h (Icc (0 : ℝ) τ) := hgi.add (hDi.const_mul ν)
      have hint : ∫ σ in Icc (0 : ℝ) τ, h σ = (f i τ - f i 0) + ν * ∫ σ in Icc (0 : ℝ) τ, D i σ := by
        rw [hh, integral_add hgi (hDi.const_mul ν), integral_const_mul, hftc]
      have hmax : ∫ σ in Icc (0 : ℝ) τ, h σ ≤ ∫ σ in Icc (0 : ℝ) τ, max (h σ) 0 :=
        integral_mono hhi (hhi.pos_part) fun σ => le_max_left _ _
      have hmaxl : ENNReal.ofReal (∫ σ in Icc (0 : ℝ) τ, max (h σ) 0) =
          ∫⁻ σ in Icc (0 : ℝ) τ, ENNReal.ofReal (h σ) := by
        rw [ofReal_integral_eq_lintegral_ofReal hhi.pos_part
          (Filter.Eventually.of_forall fun σ => le_max_right _ _)]
        refine lintegral_congr fun σ => ?_
        simp [ENNReal.ofReal_max]
      have h1 : ENNReal.ofReal (f i τ + ν * ∫ σ in Icc (0 : ℝ) τ, D i σ) ≤
          ENNReal.ofReal (f i 0) + ENNReal.ofReal (∫ σ in Icc (0 : ℝ) τ, h σ) := by
        have : f i τ + ν * ∫ σ in Icc (0 : ℝ) τ, D i σ = f i 0 + ∫ σ in Icc (0 : ℝ) τ, h σ := by
          rw [hint]; ring
        rw [this]; exact ENNReal.ofReal_add_le
      have h2 : ENNReal.ofReal (∫ σ in Icc (0 : ℝ) τ, h σ) ≤ ∫⁻ σ in Icc (0 : ℝ) τ, r i σ := by
        refine (ENNReal.ofReal_le_ofReal hmax).trans ?_
        rw [hmaxl]
        refine setLIntegral_mono' measurableSet_Icc fun σ hσ => hineq i σ (hsub hσ)
      have hDI0 : 0 ≤ ∫ σ in Icc (0 : ℝ) τ, D i σ := setIntegral_nonneg measurableSet_Icc fun σ hσ => hDnn i σ (hsub hσ)
      have hf0 := hnn i τ hτ
      calc ENNReal.ofReal (f i τ) + ENNReal.ofReal ν * ∫⁻ σ in Icc (0 : ℝ) τ, ENNReal.ofReal (D i σ)
          = ENNReal.ofReal (f i τ + ν * ∫ σ in Icc (0 : ℝ) τ, D i σ) := by
            rw [← hDl, ← ENNReal.ofReal_mul hν, ENNReal.ofReal_add hf0 (mul_nonneg hν hDI0)]
        _ ≤ ENNReal.ofReal (f i 0) + ENNReal.ofReal (∫ σ in Icc (0 : ℝ) τ, h σ) := h1
        _ ≤ ENNReal.ofReal (f i 0) + ∫⁻ σ in Icc (0 : ℝ) τ, r i σ := by gcongr
    -- sum over cells
    have hsum : W τ + ENNReal.ofReal ν * X τ ≤ W 0 + ∑' i, w i * ∫⁻ σ in Icc (0 : ℝ) τ, r i σ := by
      have h1 : ∑' i, w i * (ENNReal.ofReal (f i τ) + ENNReal.ofReal ν * ∫⁻ σ in Icc (0 : ℝ) τ, ENNReal.ofReal (D i σ)) ≤
          ∑' i, w i * (ENNReal.ofReal (f i 0) + ∫⁻ σ in Icc (0 : ℝ) τ, r i σ) :=
        ENNReal.tsum_le_tsum fun i => by gcongr w i * ?_; exact hcell i
      have e1 : ∑' i, w i * (ENNReal.ofReal (f i τ) + ENNReal.ofReal ν * ∫⁻ σ in Icc (0 : ℝ) τ, ENNReal.ofReal (D i σ)) =
          W τ + ENNReal.ofReal ν * X τ := by
        simp only [mul_add, hW, hX]
        rw [ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
        congr 1
        refine tsum_congr fun i => ?_
        ring
      have e2 : ∑' i, w i * (ENNReal.ofReal (f i 0) + ∫⁻ σ in Icc (0 : ℝ) τ, r i σ) =
          W 0 + ∑' i, w i * ∫⁻ σ in Icc (0 : ℝ) τ, r i σ := by
        simp only [mul_add, hW]
        rw [ENNReal.tsum_add]
      rw [e1, e2] at h1; exact h1
    have hsup := sa12x4_tsum_lintegral_le (μ := volume.restrict (Icc (0 : ℝ) τ)) w hw r
    have hdom : ∫⁻ σ in Icc (0 : ℝ) τ, ∑' i, w i * r i σ ≤
        ENNReal.ofReal κ * X τ + ENNReal.ofReal a * ∫⁻ σ in Icc (0 : ℝ) τ, W σ := by
      calc ∫⁻ σ in Icc (0 : ℝ) τ, ∑' i, w i * r i σ
          ≤ ∫⁻ σ in Icc (0 : ℝ) τ, (ENNReal.ofReal κ * ∑' i, w i * ENNReal.ofReal (D i σ) +
              ENNReal.ofReal a * W σ) :=
            setLIntegral_mono' measurableSet_Icc fun σ hσ => hr σ (hsub hσ)
        _ = ENNReal.ofReal κ * X τ + ENNReal.ofReal a * ∫⁻ σ in Icc (0 : ℝ) τ, W σ := by
            have hm1 : AEMeasurable (fun σ => ∑' i, w i * ENNReal.ofReal (D i σ)) (volume.restrict (Icc (0 : ℝ) τ)) :=
              AEMeasurable.ennreal_tsum fun i =>
                ((hDint i).mono_set hsub).aestronglyMeasurable.aemeasurable.ennreal_ofReal.const_mul _
            have hm2 : AEMeasurable W (volume.restrict (Icc (0 : ℝ) τ)) := hWmeas.mono_measure
              (Measure.restrict_mono hsub le_rfl)
            rw [lintegral_add_left' (hm1.const_mul _), lintegral_const_mul'' _ hm1, lintegral_const_mul'' _ hm2]
            congr 2
            rw [lintegral_tsum fun i => (((hDint i).mono_set hsub).aestronglyMeasurable.aemeasurable.ennreal_ofReal.const_mul _)]
            refine tsum_congr fun i => ?_
            rw [lintegral_const_mul'' _ ((hDint i).mono_set hsub).aestronglyMeasurable.aemeasurable.ennreal_ofReal]
    have hfin1 : ENNReal.ofReal κ * X τ ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hXfin τ hτ)
    have hkX : ENNReal.ofReal κ * X τ ≤ ENNReal.ofReal ν * X τ := by
      gcongr
    have hcomb : W τ + ENNReal.ofReal κ * X τ ≤
        (W 0 + ENNReal.ofReal a * ∫⁻ σ in Icc (0 : ℝ) τ, W σ) + ENNReal.ofReal κ * X τ := by
      calc W τ + ENNReal.ofReal κ * X τ ≤ W τ + ENNReal.ofReal ν * X τ := by gcongr
        _ ≤ W 0 + ∑' i, w i * ∫⁻ σ in Icc (0 : ℝ) τ, r i σ := hsum
        _ ≤ W 0 + (ENNReal.ofReal κ * X τ + ENNReal.ofReal a * ∫⁻ σ in Icc (0 : ℝ) τ, W σ) := by
            gcongr; exact hsup.trans hdom
        _ = _ := by ring
    exact (ENNReal.add_le_add_iff_right hfin1).1 hcomb
  -- real Gronwall
  set φ : ℝ → ℝ := fun τ => (W τ).toReal with hφ
  have hφ0 : ∀ τ ∈ Icc (0 : ℝ) t, 0 ≤ φ τ := fun τ _ => ENNReal.toReal_nonneg
  have hφB : ∃ B : ℝ, ∀ τ ∈ Icc (0 : ℝ) t, φ τ ≤ B :=
    ⟨(S * ENNReal.ofReal Bf).toReal, fun τ hτ =>
      ENNReal.toReal_mono (ENNReal.mul_ne_top hSt ENNReal.ofReal_ne_top) (hWle τ hτ)⟩
  have hφm : AEStronglyMeasurable φ (volume.restrict (Icc (0 : ℝ) t)) :=
    hWmeas.ennreal_toReal.aestronglyMeasurable
  obtain ⟨Bφ, hBφ⟩ := hφB
  have hφint : ∀ τ ∈ Icc (0 : ℝ) t, IntegrableOn φ (Icc (0 : ℝ) τ) := by
    intro τ hτ
    have hsub := hsubt τ hτ
    refine Integrable.of_bound (hφm.mono_set hsub) (max Bφ 0) ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 σ (hsub hσ))]
    exact (hBφ σ (hsub hσ)).trans (le_max_left _ _)
  have hle : ∀ τ ∈ Icc (0 : ℝ) t, φ τ ≤ a * (∫ σ in (0 : ℝ)..τ, φ σ) + φ 0 := by
    intro τ hτ
    have hsub := hsubt τ hτ
    have h0t : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_rfl, ht⟩
    have hint : ∫ σ in (0 : ℝ)..τ, φ σ = ∫ σ in Icc (0 : ℝ) τ, φ σ := by
      rw [intervalIntegral.integral_of_le hτ.1, integral_Icc_eq_integral_Ioc]
    have hl : ∫⁻ σ in Icc (0 : ℝ) τ, W σ = ENNReal.ofReal (∫ σ in Icc (0 : ℝ) τ, φ σ) := by
      rw [ofReal_integral_eq_lintegral_ofReal (hφint τ hτ)
        ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => hφ0 σ (hsub hσ)))]
      refine setLIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
      simp only [hφ]
      rw [ENNReal.ofReal_toReal (hWfin σ (hsub hσ))]
    have hI0 : 0 ≤ ∫ σ in Icc (0 : ℝ) τ, φ σ :=
      setIntegral_nonneg measurableSet_Icc fun σ hσ => hφ0 σ (hsub hσ)
    have h1 := hkey τ hτ
    rw [hl] at h1
    have hfin : W 0 + ENNReal.ofReal a * ENNReal.ofReal (∫ σ in Icc (0 : ℝ) τ, φ σ) ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨hWfin 0 h0t, ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩
    have h2 := ENNReal.toReal_mono hfin h1
    rw [ENNReal.toReal_add (hWfin 0 h0t) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hI0] at h2
    rw [hint]
    linarith
  have hgr := HRS.MS.UniqG1.g1_gronwall_source_paren φ t a (φ 0) ha ENNReal.toReal_nonneg hφ0 ⟨Bφ, hBφ⟩ hφm hle
  intro τ hτ
  have h0t : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_rfl, ht⟩
  have h1 := hgr τ hτ
  calc W τ = ENNReal.ofReal (φ τ) := (ENNReal.ofReal_toReal (hWfin τ hτ)).symm
    _ ≤ ENNReal.ofReal (φ 0 * Real.exp (a * τ)) := ENNReal.ofReal_le_ofReal h1
    _ = ENNReal.ofReal (Real.exp (a * τ)) * W 0 := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, mul_comm]
        congr 1
        exact ENNReal.ofReal_toReal (hWfin 0 h0t)

end HRS.MH.AdjointRd.Phase2SA12X4
