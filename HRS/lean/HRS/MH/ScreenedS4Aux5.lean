import HRS.MH.ScreenedS4Aux4

/-!
# Packet S4, part 5: assembly of `kg_rep_of_symbol`
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

lemma s4_main (hd : 1 ≤ d) {s : ℝ} (hsd : s < d) (hs1 : (d : ℝ) - 1 ≤ s) (c : ℝ) (hc : 0 < c)
    (hid : ∀ (i : Fin d) (φ : SchwartzMap (Euc d) ℝ) (y : Euc d),
      Integrable (fun ξ : Euc d => ((c * (2 * Real.pi * ξ i) * ‖ξ‖ ^ (s - d) : ℝ) : ℂ) * Complex.I *
        𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ) ∧
      ((HRS.Whole.convFun (rieszKernel d s) (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y : ℝ) : ℂ) =
        ∫ ξ : Euc d, ((c * (2 * Real.pi * ξ i) * ‖ξ‖ ^ (s - d) : ℝ) : ℂ) * Complex.I *
          𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ *
          Complex.exp (2 * Real.pi * Complex.I * (inner ℝ y ξ : ℝ))) :
    ∃ C : ℝ, ∀ (i : Fin d) (v : Euc d → ℝ), sobolevNormE (s + 1 - d) v < ⊤ →
      ∃ w : Euc d → ℝ, IsGradKernelRep d s i v w ∧ MemLp w 2 volume ∧
        eLpNorm w 2 volume ≤ ENNReal.ofReal C * sobolevNormE (s + 1 - d) v := by
  have hσ0 : 0 ≤ s + 1 - d := by linarith
  have hσ1 : s + 1 - d ≤ 1 := by linarith
  refine ⟨Real.sqrt ((2 * Real.pi * c) ^ 2 * (4 * Real.pi ^ 2) ^ (-(s + 1 - d))), fun i v hv => ?_⟩
  have hMS : HRS.PDE.ToolboxRd.MemSobolev (s + 1 - d) v := by
    by_contra h
    unfold sobolevNormE at hv
    rw [if_neg h] at hv
    exact lt_irrefl _ hv
  obtain ⟨hM2, hM2n⟩ := s4_M2 hc hσ0 i hMS
  have hv2 : MemLp v 2 volume := hMS.1
  set M2 : Euc d → ℂ := fun ξ => s4m c s i ξ * fourierL2 v ξ with hM2def
  set W : Lp (α := Euc d) ℂ 2 := (FT d).symm (hM2.toLp M2) with hW
  have hWmem : MemLp (⇑W) 2 volume := Lp.memLp W
  have hwmem : MemLp (fun x => (W x).re) 2 volume := by simpa using hWmem.re
  refine ⟨fun x => (W x).re, ?_, hwmem, ?_⟩
  · intro φ
    have hφ2 : MemLp (⇑φ) 2 volume := φ.memLp 2 volume
    have hM1 : Integrable (fun ξ : Euc d => s4m c s i ξ *
        𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ) := (hid i φ 0).1
    have hMmem := s4_Mphi_memLp hc hσ0 hσ1 i φ hM1
    set h : Euc d → ℝ := fun y => HRS.Whole.convFun (rieszKernel d s)
      (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) y with hh
    have hhh : ∀ y : Euc d, ((h y : ℝ) : ℂ) = ∫ ξ : Euc d, (s4m c s i ξ *
        𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ) *
          Complex.exp (2 * Real.pi * Complex.I * (inner ℝ y ξ : ℝ)) := fun y => (hid i φ y).2
    obtain ⟨hhmem, hpair⟩ := s4_pair_h hv2 hM1 hMmem hhh
    have hW2 := s4_pair_w hφ2 hM2
    have hFφ := fourierL2_schwartz φ
    have hrel : ∫ ξ, fourierL2 v ξ * conj (s4m c s i ξ *
        𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ) =
        -∫ ξ, M2 ξ * conj (fourierL2 φ ξ) := by
      rw [← integral_neg]
      refine integral_congr_ae ?_
      filter_upwards [hFφ] with ξ hξ
      rw [hξ, map_mul, conj_s4m]
      simp only [hM2def]
      ring
    have hA : ((∫ x, v x * h x : ℝ) : ℂ) = -∫ x, (W x) * ((φ x : ℝ) : ℂ) := by
      rw [← hpair, hrel, hW2]
    have hintWφ : Integrable (fun x => W x * ((φ x : ℝ) : ℂ)) :=
      hWmem.integrable_mul (hφ2.ofReal (K := ℂ))
    have hre : ∫ x, (W x).re * φ x = (∫ x, W x * ((φ x : ℝ) : ℂ)).re := by
      have := integral_re hintWφ
      simp only [RCLike.re_to_complex] at this
      rw [← this]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp
    refine ⟨hwmem.integrable_mul hφ2, hv2.integrable_mul hhmem, ?_⟩
    show ∫ x, (W x).re * φ x = -∫ y, v y * h y
    rw [hre]
    have : ∫ x, W x * ((φ x : ℝ) : ℂ) = -((∫ x, v x * h x : ℝ) : ℂ) := by rw [hA, neg_neg]
    rw [this]
    simp
  · calc eLpNorm (fun x => (W x).re) 2 volume ≤ eLpNorm (⇑W) 2 volume :=
          eLpNorm_mono hwmem.aestronglyMeasurable
            (fun x => by simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm (W x))
      _ = ‖W‖ₑ := (Lp.enorm_def W).symm
      _ = ‖hM2.toLp M2‖ₑ := (FT d).symm.enorm_map _
      _ = eLpNorm M2 2 volume := Lp.enorm_toLp hM2
      _ ≤ _ := hM2n
      _ = _ := by
          unfold sobolevNormE
          rw [if_pos hMS]

end HRS.MH.Screened
