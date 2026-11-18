import HRS.MS.SA12X4W1
import HRS.MS.SA12X5Defs

/-!
# S.A.12 X5 D2WA: the weighted integral cell Gronwall bound with a source term

`sa12x5_weighted_gronwall_src` is `sa12x4_weighted_gronwall` (SA12X4W1) with an extra source `Hs σ ≥ 0` in the
weighted domination `hr`; conclusion `W τ ≤ e^{aτ}(W 0 + ∫₀^τ Hs)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS.MH.AdjointRd.Phase2SA12X4 HRS.MH.AdjointRd.Phase2SA12Construction

theorem sa12x5_weighted_gronwall_src {ι : Type*} [Countable ι] (t ν κ a : ℝ) (ht : 0 ≤ t) (hν : 0 ≤ ν)
    (hκ : 0 ≤ κ) (hκν : κ ≤ ν) (ha : 0 ≤ a) (w : ι → ℝ≥0∞) (hwfin : ∑' i, w i < ⊤)
    (f g D : ι → ℝ → ℝ) (r : ι → ℝ → ℝ≥0∞)
    (hnn : ∀ i, ∀ τ ∈ Icc (0 : ℝ) t, 0 ≤ f i τ) (hDnn : ∀ i, ∀ τ ∈ Icc (0 : ℝ) t, 0 ≤ D i τ)
    (hbdd : ∃ B : ℝ, ∀ i, ∀ τ ∈ Icc (0 : ℝ) t, f i τ ≤ B)
    (hDint : ∀ i, IntegrableOn (D i) (Icc (0 : ℝ) t))
    (hDbdd : ∃ B : ℝ, ∀ i, ∫ σ in Icc (0 : ℝ) t, D i σ ≤ B)
    (hcont : ∀ i, ContinuousOn (f i) (Icc (0 : ℝ) t))
    (hderiv : ∀ i, ∀ τ ∈ Icc (0 : ℝ) t, HasDerivWithinAt (f i) (g i τ) (Icc (0 : ℝ) t) τ)
    (hgint : ∀ i, IntegrableOn (g i) (Icc (0 : ℝ) t))
    (Hs : ℝ → ℝ) (hHs0 : ∀ σ ∈ Icc (0 : ℝ) t, 0 ≤ Hs σ) (hHsint : IntegrableOn Hs (Icc (0 : ℝ) t))
    (hineq : ∀ i, ∀ τ ∈ Icc (0 : ℝ) t, ENNReal.ofReal (g i τ + ν * D i τ) ≤ r i τ)
    (hr : ∀ τ ∈ Icc (0 : ℝ) t, ∑' i, w i * r i τ ≤
      ENNReal.ofReal κ * ∑' i, w i * ENNReal.ofReal (D i τ) +
        ENNReal.ofReal a * ∑' i, w i * ENNReal.ofReal (f i τ) + ENNReal.ofReal (Hs τ)) :
    ∀ τ ∈ Icc (0 : ℝ) t, ∑' i, w i * ENNReal.ofReal (f i τ) ≤
      ENNReal.ofReal (Real.exp (a * τ)) * (∑' i, w i * ENNReal.ofReal (f i 0) +
        ENNReal.ofReal (∫ σ in Icc (0 : ℝ) τ, Hs σ)) := by
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
  have hkey : ∀ τ ∈ Icc (0 : ℝ) t, W τ ≤ W 0 + ENNReal.ofReal a * (∫⁻ σ in Icc (0 : ℝ) τ, W σ) +
      ENNReal.ofReal (∫ σ in Icc (0 : ℝ) τ, Hs σ) := by
    intro τ hτ
    have hsub := hsubt τ hτ
    have h0t : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_rfl, ht⟩
    -- per cell
    have hcell : ∀ i, ENNReal.ofReal (f i τ) + ENNReal.ofReal ν * ∫⁻ σ in Icc (0 : ℝ) τ, ENNReal.ofReal (D i σ) ≤
        ENNReal.ofReal (f i 0) + ∫⁻ σ in Icc (0 : ℝ) τ, r i σ := by
      intro i
      have hDi : IntegrableOn (D i) (Icc (0 : ℝ) τ) := (hDint i).mono_set hsub
      have hgi : IntegrableOn (g i) (Icc (0 : ℝ) τ) := (hgint i).mono_set hsub
      have hftc := sa12x3_ftc_int t (f i) (g i) (hcont i) (hderiv i) (hgint i) τ hτ
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
    have hJ : ENNReal.ofReal (∫ σ in Icc (0 : ℝ) τ, Hs σ) = ∫⁻ σ in Icc (0 : ℝ) τ, ENNReal.ofReal (Hs σ) :=
      ofReal_integral_eq_lintegral_ofReal (hHsint.mono_set hsub)
        ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => hHs0 σ (hsub hσ)))
    have hdom : ∫⁻ σ in Icc (0 : ℝ) τ, ∑' i, w i * r i σ ≤
        ENNReal.ofReal κ * X τ + ENNReal.ofReal a * (∫⁻ σ in Icc (0 : ℝ) τ, W σ) +
          ENNReal.ofReal (∫ σ in Icc (0 : ℝ) τ, Hs σ) := by
      calc ∫⁻ σ in Icc (0 : ℝ) τ, ∑' i, w i * r i σ
          ≤ ∫⁻ σ in Icc (0 : ℝ) τ, (ENNReal.ofReal κ * ∑' i, w i * ENNReal.ofReal (D i σ) +
              ENNReal.ofReal a * W σ + ENNReal.ofReal (Hs σ)) :=
            setLIntegral_mono' measurableSet_Icc fun σ hσ => hr σ (hsub hσ)
        _ = ENNReal.ofReal κ * X τ + ENNReal.ofReal a * (∫⁻ σ in Icc (0 : ℝ) τ, W σ) +
              ENNReal.ofReal (∫ σ in Icc (0 : ℝ) τ, Hs σ) := by
            have hm1 : AEMeasurable (fun σ => ∑' i, w i * ENNReal.ofReal (D i σ)) (volume.restrict (Icc (0 : ℝ) τ)) :=
              AEMeasurable.ennreal_tsum fun i =>
                ((hDint i).mono_set hsub).aestronglyMeasurable.aemeasurable.ennreal_ofReal.const_mul _
            have hm2 : AEMeasurable W (volume.restrict (Icc (0 : ℝ) τ)) := hWmeas.mono_measure
              (Measure.restrict_mono hsub le_rfl)
            have hXeq : ∫⁻ σ in Icc (0 : ℝ) τ, ∑' i, w i * ENNReal.ofReal (D i σ) = X τ := by
              rw [lintegral_tsum fun i => (((hDint i).mono_set hsub).aestronglyMeasurable.aemeasurable.ennreal_ofReal.const_mul _)]
              refine tsum_congr fun i => ?_
              rw [lintegral_const_mul'' _ ((hDint i).mono_set hsub).aestronglyMeasurable.aemeasurable.ennreal_ofReal]
            have hHm : AEMeasurable (fun σ => ENNReal.ofReal (Hs σ)) (volume.restrict (Icc (0 : ℝ) τ)) :=
              (hHsint.mono_set hsub).aestronglyMeasurable.aemeasurable.ennreal_ofReal
            rw [lintegral_add_right' _ hHm, lintegral_add_left' (hm1.const_mul _),
              lintegral_const_mul'' _ hm1, lintegral_const_mul'' _ hm2, hXeq, hJ]
    have hfin1 : ENNReal.ofReal κ * X τ ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hXfin τ hτ)
    have hkX : ENNReal.ofReal κ * X τ ≤ ENNReal.ofReal ν * X τ := by
      gcongr
    have hcomb : W τ + ENNReal.ofReal κ * X τ ≤
        (W 0 + ENNReal.ofReal a * (∫⁻ σ in Icc (0 : ℝ) τ, W σ) + ENNReal.ofReal (∫ σ in Icc (0 : ℝ) τ, Hs σ)) +
          ENNReal.ofReal κ * X τ := by
      calc W τ + ENNReal.ofReal κ * X τ ≤ W τ + ENNReal.ofReal ν * X τ := by gcongr
        _ ≤ W 0 + ∑' i, w i * ∫⁻ σ in Icc (0 : ℝ) τ, r i σ := hsum
        _ ≤ W 0 + (ENNReal.ofReal κ * X τ + ENNReal.ofReal a * (∫⁻ σ in Icc (0 : ℝ) τ, W σ) +
            ENNReal.ofReal (∫ σ in Icc (0 : ℝ) τ, Hs σ)) := by
            gcongr; exact hsup.trans hdom
        _ = _ := by ring
    exact (ENNReal.add_le_add_iff_right hfin1).1 hcomb
  -- real Gronwall on [0, τ₀]
  intro τ₀ hτ₀
  have hsub0 : Icc (0 : ℝ) τ₀ ⊆ Icc (0 : ℝ) t := Icc_subset_Icc_right hτ₀.2
  have h0t : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_rfl, ht⟩
  set Δ : ℝ≥0∞ := W 0 + ENNReal.ofReal (∫ σ in Icc (0 : ℝ) τ₀, Hs σ) with hΔ
  have hΔfin : Δ ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hWfin 0 h0t, ENNReal.ofReal_ne_top⟩
  have hkey' : ∀ τ ∈ Icc (0 : ℝ) τ₀, W τ ≤ Δ + ENNReal.ofReal a * ∫⁻ σ in Icc (0 : ℝ) τ, W σ := by
    intro τ hτ
    have hτt : τ ∈ Icc (0 : ℝ) t := ⟨hτ.1, hτ.2.trans (hτ₀.2)⟩
    have h1 := hkey τ hτt
    have h2 : ENNReal.ofReal (∫ σ in Icc (0 : ℝ) τ, Hs σ) ≤ ENNReal.ofReal (∫ σ in Icc (0 : ℝ) τ₀, Hs σ) := by
      refine ENNReal.ofReal_le_ofReal (setIntegral_mono_set (hHsint.mono_set hsub0) ?_
        (Filter.Eventually.of_forall fun x hx => Icc_subset_Icc_right hτ.2 hx))
      exact (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => hHs0 σ (hsub0 hσ))
    calc W τ ≤ W 0 + ENNReal.ofReal a * (∫⁻ σ in Icc (0 : ℝ) τ, W σ) +
          ENNReal.ofReal (∫ σ in Icc (0 : ℝ) τ, Hs σ) := h1
      _ = (W 0 + ENNReal.ofReal (∫ σ in Icc (0 : ℝ) τ, Hs σ)) + ENNReal.ofReal a * ∫⁻ σ in Icc (0 : ℝ) τ, W σ := by
          first | ring | abel | simp only [add_comm, add_left_comm, add_assoc]
      _ ≤ Δ + ENNReal.ofReal a * ∫⁻ σ in Icc (0 : ℝ) τ, W σ := by rw [hΔ]; gcongr
  set φ : ℝ → ℝ := fun τ => (W τ).toReal with hφ
  have hφ0 : ∀ τ ∈ Icc (0 : ℝ) t, 0 ≤ φ τ := fun τ _ => ENNReal.toReal_nonneg
  have hφB : ∃ B : ℝ, ∀ τ ∈ Icc (0 : ℝ) t, φ τ ≤ B :=
    ⟨(S * ENNReal.ofReal Bf).toReal, fun τ hτ =>
      ENNReal.toReal_mono (ENNReal.mul_ne_top hSt ENNReal.ofReal_ne_top) (hWle τ hτ)⟩
  have hφm : AEStronglyMeasurable φ (volume.restrict (Icc (0 : ℝ) t)) :=
    hWmeas.ennreal_toReal.aestronglyMeasurable
  obtain ⟨Bφ, hBφ⟩ := hφB
  have hφint : ∀ τ ∈ Icc (0 : ℝ) τ₀, IntegrableOn φ (Icc (0 : ℝ) τ) := by
    intro τ hτ
    have hsub : Icc (0 : ℝ) τ ⊆ Icc (0 : ℝ) t := Icc_subset_Icc_right (hτ.2.trans hτ₀.2)
    refine Integrable.of_bound (hφm.mono_set hsub) (max Bφ 0) ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun σ hσ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 σ (hsub hσ))]
    exact (hBφ σ (hsub hσ)).trans (le_max_left _ _)
  have hle : ∀ τ ∈ Icc (0 : ℝ) τ₀, φ τ ≤ a * (∫ σ in (0 : ℝ)..τ, φ σ) + Δ.toReal := by
    intro τ hτ
    have hsub : Icc (0 : ℝ) τ ⊆ Icc (0 : ℝ) t := Icc_subset_Icc_right (hτ.2.trans hτ₀.2)
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
    have h1 := hkey' τ hτ
    rw [hl] at h1
    have hfin : Δ + ENNReal.ofReal a * ENNReal.ofReal (∫ σ in Icc (0 : ℝ) τ, φ σ) ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨hΔfin, ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩
    have h2 := ENNReal.toReal_mono hfin h1
    rw [ENNReal.toReal_add hΔfin (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hI0] at h2
    rw [hint]
    linarith
  have hgr := HRS.MS.UniqG1.g1_gronwall_source_paren φ τ₀ a Δ.toReal ha ENNReal.toReal_nonneg
    (fun τ hτ => hφ0 τ (hsub0 hτ)) ⟨Bφ, fun τ hτ => hBφ τ (hsub0 hτ)⟩ (hφm.mono_set hsub0) hle
  have h1 := hgr τ₀ ⟨hτ₀.1, le_rfl⟩
  calc W τ₀ = ENNReal.ofReal (φ τ₀) := (ENNReal.ofReal_toReal (hWfin τ₀ hτ₀)).symm
    _ ≤ ENNReal.ofReal (Δ.toReal * Real.exp (a * τ₀)) := ENNReal.ofReal_le_ofReal h1
    _ = ENNReal.ofReal (Real.exp (a * τ₀)) * Δ := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, mul_comm]
        congr 1
        exact ENNReal.ofReal_toReal hΔfin

end HRS.MH.AdjointRd.Phase2SA12X5
